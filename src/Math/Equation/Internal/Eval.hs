{-# LANGUAGE OverloadedStrings, PartialTypeSignatures, ScopedTypeVariables, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}

module Math.Equation.Internal.Eval where

-- We want to use QuickSpec's `prune` function to minimise a set of equations,
-- but this is tricky since its `Symbol` type contains a `TypeRep`. We can
-- serialise a `TypeRep` easily enough with `show`, but we can't de-serialise it
-- easily.

-- To work around this, we don't attempt to de-serialise any `TypeRep`, e.g. via
-- a function like `String -> TypeRep`; instead, since a serialised `TypeRep` is
-- just a `String` of Haskell source code corresponding to a type, we turn our
-- `prune`-invoking function into Haskell source code as well, and append the
-- `TypeRep`s as needed, as type annotations.

import Data.Dynamic
import Data.List
import Data.Maybe
import Data.String
import Data.Typeable
import Language.Eval.Internal
import qualified Language.Haskell.Exts.Syntax
import Math.Equation.Internal.Types
import MLSpec.Helper
import System.Environment
import System.IO
import System.IO.Unsafe
import Text.Read  -- Uses String as part of base, not Text

-- Used for their types
import qualified Test.QuickCheck.Gen
import qualified Test.QuickSpec
import qualified Test.QuickSpec.Main
import qualified Test.QuickSpec.Signature
import qualified Test.QuickSpec.Term
import qualified Test.QuickSpec.TestTree
import qualified Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning
import qualified Test.QuickSpec.Equation

-- We use nix-eval to perform the evaluation. Since the code is quite tricky, we
-- wrap nix-eval's `Expr` values as `TypedExpr`s which have a phantom type
-- representing the type of the expression they wrap. This way, we recover some
-- of the benefits of type-checking, as long as our annotations are correct

data TypedExpr a = TE Expr

-- Convenience: we can write "foo" to get a `TypedExpr a`
instance IsString (TypedExpr a) where
  fromString s = TE (fromString s)

instance Show (TypedExpr a) where
  show (TE x) = "TE (" ++ show x ++ ")"

-- Apply a function to an argument. Since this propagates types explicitly, it
-- should be used in preference to, e.g., wrapping/unwrapping `TE` constructors.
($$$) :: TypedExpr (a -> b) -> TypedExpr a -> TypedExpr b
(TE f) $$$ (TE x) = TE (f $$ x)

-- Function abstraction. Ensures we have the right arity, but you'll probably
-- want to make `a` concrete with an annotation. Only one argument at a time,
-- to keep the types simple.
tlam :: String -> TypedExpr b -> TypedExpr (a -> b)
tlam arg (TE f) = TE (f { eExpr = body })
  where body = "(\\(" ++ arg ++ ") -> (" ++ eExpr f ++ "))"

withType :: TypedExpr a -> String -> TypedExpr b
withType (TE x) t = TE (x { eExpr = "((" ++ eExpr x ++ ") :: (" ++ t ++ "))" })

-- Execute an expression, by evaluating it as the value of `main`. Returns the
-- resulting stdout (or `Nothing` on error)
exec :: TypedExpr (IO a) -> IO (Maybe String)
exec (TE x) = eval' ("main = " ++) (augment x)
  where augment = withPkgs ps . withMods ms
        ps            = map (Pkg . fst) extraImports
        ms            = map (Mod . snd) extraImports
        extraImports  = fromMaybe [] (given >>= readMaybe)
        given         = unsafePerformIO (lookupEnv "NIX_EVAL_EXTRA_IMPORTS")

-- Conversion from our representations to QuickSpec expressions

renderEqs :: [Equation] -> WithSig [Test.QuickSpec.Equation.Equation]
renderEqs []     = WS nil'
renderEqs (e:es) = case (renderEq e, renderEqs es) of
                        (WS x, WS xs) -> WS ((cons' $$$ x) $$$ xs)

renderEq :: Equation -> WithSig Test.QuickSpec.Equation.Equation
renderEq (Eq lhs rhs) = case (renderTerm lhs, renderTerm rhs) of
                             (WS l, WS r) -> WS (("(:=:)" $$$ l) $$$ r)

renderTerm :: Term -> WithSig Test.QuickSpec.Term.Term
renderTerm t = case (t, sigToSym t) of
    (App lhs rhs _, _ ) -> case (renderTerm lhs, renderTerm rhs) of
                                (WS l, WS r) -> WS ((app $$$ l) $$$ r)
    (C   c,       WS s) -> WS (const $$$ s)
    (V   v,       WS s) -> WS (var   $$$ s)
  where app :: TypedExpr (Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term)
        app   = qsQual "Test.QuickSpec.Term" "App"
        const, var :: TypedExpr (Test.QuickSpec.Term.Symbol -> Test.QuickSpec.Term.Term)
        const = qsQual "Test.QuickSpec.Term" "Const"
        var   = qsQual "Test.QuickSpec.Term" "Var"

renderTermN t sig = case (t, sigToSymN t) of
    (App l r _, _  ) -> case (renderTermN l sig, renderTermN r sig) of
                             (f_l, f_r) -> \sig -> app (f_l sig) (f_r sig)
    (C c,       f_s) -> \sig -> (const (f_s sig))
    (V v,       f_s) -> \sig -> (var   (f_s sig))
  where app   = Test.QuickSpec.Term.App
        const = Test.QuickSpec.Term.Const
        var   = Test.QuickSpec.Term.Var

newtype WithSig a = WS (TypedExpr a)



renderWithSig :: WithSig a -> Sig -> TypedExpr a
renderWithSig (WS (TE e)) sig = TE (e {
      eExpr = "let { givenSig = (" ++ eExpr s ++ "); } in (" ++ eExpr e ++ ")"
    })
  where TE s = render sig

renderWithSigN :: (Test.QuickSpec.Signature.Sig -> a) -> Sig -> a
renderWithSigN e sig = e sig'
  where sig' = sigToQS sig
        sigToQS (Sig cs vs) = mappend (renderQSConsts cs) (renderQSVars vs)

renderQSConsts = foldr (mappend . renderQSConst) mempty

renderQSVars   = undefined

renderQSConst :: Const -> Test.QuickSpec.Signature.Sig
renderQSConst = undefined

{-
data (Ord a, Ord b, Ord c, Ord d, Ord e, Ord f,
      Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f) =>
     QSFun a b c d e f = F0 a
                       | F1 (a -> b)
                       | F2 (a -> b -> c)
                       | F3 (a -> b -> c -> d)
                       | F4 (a -> b -> c -> d -> e)
                       | F5 (a -> b -> c -> d -> e -> f)
-}

data TSig a where
   TsZ :: TSig Z
   TsS :: TSig a -> TSig (S a)
   TsF :: TSig a -> TSig b -> TSig (a -> b)

tsToV :: TSig a -> a
tsToV  TsZ      = Z ()
tsToV (TsS x)   = S (tsToV x)
tsToV (TsF f x) = \a -> tsToV x


vToD :: Type -> (String -> QSSig, )
vToD (Language.Haskell.Exts.Syntax.TyFun x y) = TsF (vToD x) (vToD y)
vToD (Language.Haskell.Exts.Syntax.TyApp s x) = toDyn TsS (vToD x)
vToD _                                        = toDyn Z

{-
f0 = Test.QuickSpec.Signature.fun0
f1 = Test.QuickSpec.Signature.fun1
f2 = Test.QuickSpec.Signature.fun2
f3 = Test.QuickSpec.Signature.fun3
f4 = Test.QuickSpec.Signature.fun4
f5 = Test.QuickSpec.Signature.fun5
-}

class Specable a where
  specable :: String -> a -> QSSig

instance {-# OVERLAPPABLE #-} (Typeable a,
                               Ord      a) => Specable a where
  specable = Test.QuickSpec.Signature.fun0

instance {-# OVERLAPPABLE #-} (Typeable a,
                               Typeable b,
                               Ord      b) => Specable (a -> b) where
  specable = Test.QuickSpec.Signature.fun1

instance {-# OVERLAPPABLE #-} (Typeable a,
                               Typeable b,
                               Typeable c,
                               Ord      c) => Specable (a -> b -> c) where
  specable = Test.QuickSpec.Signature.fun2

instance {-# OVERLAPPABLE #-} (Typeable a,
                               Typeable b,
                               Typeable c,
                               Typeable d,
                               Ord      d) => Specable (a -> b -> c -> d) where
  specable = Test.QuickSpec.Signature.fun3

instance {-# OVERLAPPABLE #-} (Typeable a,
                               Typeable b,
                               Typeable c,
                               Typeable d,
                               Typeable e,
                               Ord      e) => Specable (a -> b -> c -> d -> e) where
  specable = Test.QuickSpec.Signature.fun4

instance {-# OVERLAPPABLE #-} (Typeable a,
                               Typeable b,
                               Typeable c,
                               Typeable d,
                               Typeable e,
                               Typeable f,
                               Ord      f) => Specable (a -> b -> c -> d -> e -> f) where
  specable = Test.QuickSpec.Signature.fun5

instance Specable Z where
  specable = Test.QuickSpec.Signature.fun0

instance (Specable a, Ord (S a), Typeable a) => Specable (S a) where
  specable = Test.QuickSpec.Signature.fun0

--instance (Specable a, Specable b, Specable c) => Specable (a -> b -> c) where
--  specable = Test.QuickSpec.Signature.fun2

class Base a where
  base :: a

instance Base Z where
  base = Z ()

instance (Base a) => Base (S a) where
  base = S base

instance (Base a, Base b) => Base (a -> b) where
  base = \x -> base

data E = forall a. Base a => E a

{-
vToS :: Type -> QSSig
vToS (Language.Haskell.Exts.Syntax.TyFun x y) = specable (fP (vToP x) (vToP y))
vToS (Language.Haskell.Exts.Syntax.TyApp s x) = specable (sP (vToP x))
vToS _                                        = specable  zP
-}

zP :: Z
zP = undefined

sP :: a -> (S a)
sP _ = undefined

fP :: a -> b -> (a -> b)
fP _ _ = undefined

{-
ts2U TsZ = undefined :: Z
ts2U (TsS x) = S (ts2U x)

ts2Q (TsF a (TsF b (TsF c (TsF d (TsF e f))))) = f5
-}

{-
data family Specable a

data instance Specable (a -> b) =
data instance Specable a
-}
{-
renderQSConst c = sigOf case fromDynamic (allSigs !! index) of
                    Just f' -> f'
  where a' = case a of
          0 -> a
          1 -> a
          2 -> a
          3 -> a
          4 -> a
          5 -> a
          _ -> error ("No fun* function for arity " ++ show a)

        Arity a    = constArity c
        Name  name = constName  c
        t          = constType  c

        index = 5 * sigDepth t + a'

        sigDepth (Language.Haskell.Exts.Syntax.TyApp _ x) = 1 + sigDepth x
        sigDepth _                                        = 0

        allSigs = sigsFrom (Z ())

        sigOf x = case cast x of
          Just x' -> Test.QuickSpec.Signature.fun0 name x'
          Nothing -> case cast x of
            Just x' -> Test.QuickSpec.Signature.fun1 name x'
            Nothing -> case cast x of
              Just x' -> Test.QuickSpec.Signature.fun2 name x'
              Nothing -> case cast x of
                Just x' -> Test.QuickSpec.Signature.fun3 name x'
                Nothing -> case cast x of
                  Just x' -> Test.QuickSpec.Signature.fun4 name x'
                  Nothing -> case cast x of
                    Just x' -> Test.QuickSpec.Signature.fun5 name x'
                    Nothing -> error ("No fun* function for arity " ++ show a)
-}

sigToSym :: Term -> WithSig Test.QuickSpec.Term.Symbol
sigToSym t = WS (head' $$$ filtered)
  where pred     = tlam "x" (("==" $$$ (name' $$$ "x")) $$$ gotName')
        Name n   = case t of
                        C c   -> constName c
                        V v   -> varName   v
                        App{} -> error ("Tried to get symbol for " ++ show t)
        gotName' = TE (asString n)
        filtered = (filter' $$$ pred) $$$ (symbols' $$$ "givenSig")

sigToSymN :: Term -> Test.QuickSpec.Signature.Sig -> Test.QuickSpec.Term.Symbol
sigToSymN t sig = head filtered
  where pred x   = name x == n
        Name n   = case t of
                        C c -> constName c
                        V v -> varName   v
                        App{} -> error ("Tried to get sym for " ++ show t)
        filtered = filter pred (symbols sig)

        symbols = Test.QuickSpec.Signature.symbols
        name    = Test.QuickSpec.Term.name




render :: Sig -> TypedExpr QSSig
render (Sig cs vs) = mappend' (renderConsts cs) (renderVars vs)

renderConsts :: [Const] -> TypedExpr QSSig
renderConsts = foldr (mappend' . renderConst) empty'

renderConst :: Const -> TypedExpr QSSig
renderConst c = (f $$$ name) $$$ v
  where f :: TypedExpr (String -> () -> QSSig)
        f = if a > 5
               then error ("No fun* function for arity " ++ show a)
               else TE . withQS . qualified "Test.QuickSpec.Signature" . raw $
                      "fun" ++ show a

        v :: TypedExpr ()
        v = TE . raw $ "Prelude.undefined :: (" ++ typeName t ++ ")"

        Arity a = constArity c
        Name  n = constName  c
        t       = constType  c

        name :: TypedExpr String
        name = TE (asString n)

-- | Render a list of `Var`s as a QuickSpec `Sig`. We must be careful to avoid
--   clobbering the same variable indices, so we add each type's variables in
--   one go
renderVars :: [Var] -> TypedExpr QSSig
renderVars vs = collapse (map renderGroup (sameTypes vs))
  where collapse           = foldr mappend' empty'
        renderGroup []     = empty'
        renderGroup (v:vs) = if varArity v > 2
                                then error ("Var arity too big: " ++ show (
                                               ("varArity v", varArity v),
                                               ("v", v)))
                                else renderTypedVars (varArity v) (varType v)
                                                     (map varName (v:vs))
        sameTypes []       = []
        sameTypes (v:vs)   = let (same, diff) = partition (sameType v) vs
                              in (v:same) : sameTypes diff
        sameType v1 v2     = varType v1 == varType v2

renderTypedVars :: Arity -> Type -> [Name] -> TypedExpr QSSig
renderTypedVars a t ns = (gvars $$$ names') $$$ genOf' t
  where gvars = if a > 2
                   then error ("Var arity too high: " ++ show (("a", a),
                                                               ("t", t),
                                                               ("ns", ns)))
                   else gvars' a

        names' :: TypedExpr [String]
        names' = collapse (map (\(Name n) -> TE (asString n)) ns)

        collapse :: [TypedExpr a] -> TypedExpr [a]
        collapse = foldr (\x -> ((cons' $$$ x) $$$)) nil'

-- Wrappers for Prelude functions

map' :: TypedExpr ((a -> b) -> [a] -> [b])
map' = "Prelude.map"

return' :: Monad m => TypedExpr (a -> m b)
return' = "Prelude.return"

head' :: TypedExpr ([a] -> a)
head' = "Prelude.head"

nil' :: TypedExpr [a]
nil' = "([])"

cons' :: TypedExpr (a -> [a] -> [a])
cons' = "(:)"

any' :: TypedExpr ((a -> Bool) -> [a] -> Bool)
any' = "Prelude.any"

show' :: Show a => TypedExpr (a -> String)
show' = "Prelude.show"

all' :: TypedExpr ((a -> Bool) -> [a] -> Bool)
all' = "Prelude.all"

join' :: Monad m => TypedExpr (m (m a) -> m a)
join' = TE . qualified "Control.Monad" $ "join"

mappend' :: TypedExpr a -> TypedExpr a -> TypedExpr a
mappend' x y = (TE "Prelude.mappend" $$$ x) $$$ y

id' :: TypedExpr (a -> a)
id' = "Prelude.id"

filter' :: TypedExpr ((a -> Bool) -> [a] -> [a])
filter' = "Prelude.filter"

not' :: TypedExpr (Bool -> Bool)
not' = "Prelude.not"

compose' :: TypedExpr (b -> c) -> TypedExpr (a -> b) -> TypedExpr (a -> c)
compose' f g = ("(.)" $$$ f) $$$ g

unlines' :: TypedExpr ([String] -> String)
unlines' = "Prelude.unlines"

-- Type synonyms for verbose QuickSpec types

type QSSig = Test.QuickSpec.Signature.Sig

type Ctx = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context

type Eqs = [Test.QuickSpec.Equation.Equation]

-- Ensures that QuickSpec is available during evaluation
withQS = withPkgs ["quickspec"] . withMods ["Test.QuickSpec",
                                            "Test.QuickSpec.Signature",
                                            "Test.QuickSpec.Term"]
qsQual :: Mod -> Expr -> TypedExpr a
qsQual m x = TE (withQS . qualified m $ x)

-- Various functions from QuickSpec, which we use to prune equations

empty' :: TypedExpr QSSig
empty' = qsQual "Test.QuickSpec.Signature" "emptySig"

gvars' :: Arity -> TypedExpr ([String] -> a -> QSSig)
gvars' (Arity a) = if a `elem` [0, 1, 2]
                      then qsQual "Test.QuickSpec.Signature" (raw ("gvars" ++ show a))
                      else error ("No gvars* function for arity " ++ show a)

name' :: TypedExpr (Test.QuickSpec.Term.Symbol -> String)
name' = qsQual "Test.QuickSpec.Term" "name"

term' :: TypedExpr (Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Term.Term)
term' = qsQual "Test.QuickSpec.Term" "term"

initial' :: TypedExpr (Int
                  -> [Test.QuickSpec.Term.Symbol]
                  -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
                  -> Ctx)
initial' = qsQual "Test.QuickSpec.Reasoning.NaiveEquationalReasoning"
                  "initial"

maxDepth' :: TypedExpr (QSSig -> Int)
maxDepth' = qsQual "Test.QuickSpec.Signature" "maxDepth"

symbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
symbols' = qsQual "Test.QuickSpec.Signature" "symbols"

isUndefined' = qsQual "Test.QuickSpec.Term" "isUndefined"

prune' = qsQual "Test.QuickSpec.Main" "prune"

showEquation' :: TypedExpr (Test.QuickSpec.Signature.Sig -> Test.QuickSpec.Equation.Equation -> String)
showEquation' = qsQual "Test.QuickSpec.Equation" "showEquation"

-- Prefix constructor names with `con`

conSome' :: TypedExpr (f a -> Test.QuickSpec.Utils.Typed.Some f)
conSome' = qsQual "Test.QuickSpec.Utils.Typed" "Some"

-- Pruning algorithm adapted from Test.QuickSpec.quickSpec

checkNames' :: [Name] -> TypedExpr ([Test.QuickSpec.Term.Symbol] -> Bool)
checkNames' ns = tlam "syms" body
  where body       = (all' $$$ (isIn' $$$ syms)) $$$ names

        names :: TypedExpr [String]
        names      = TE . raw $ "[" ++ commaNames ++ "]"

        commaNames = intercalate "," (map (show . (\(Name n) -> n)) ns)

        syms :: TypedExpr [Test.QuickSpec.Term.Symbol]
        syms = "syms"

isIn' :: TypedExpr ([Test.QuickSpec.Term.Symbol] -> String -> Bool)
isIn' = tlam "syms" (tlam "n" body)
  where body = (any' $$$ f) $$$ syms
        f    = compose' (eq $$$ n) name'

        syms :: TypedExpr [Test.QuickSpec.Term.Symbol]
        syms = "syms"

        eq :: Eq a => TypedExpr (a -> a -> Bool)
        eq = "(==)"

        n :: TypedExpr String
        n = "n"

genOf' :: Type -> TypedExpr (Test.QuickCheck.Gen.Gen a)
genOf' t = return' $$$ undef
  where undef = TE . raw $ "Prelude.undefined :: (" ++ typeName t ++ ")"

classesFromEqs :: [Equation] -> [[Term]]
classesFromEqs = combine [] . map nub . addAllToClasses []

addAllToClasses = foldl addToClasses

addToClasses cs (Eq l r) = case cs of
  []   -> [[l, r]]
  x:xs -> if l `elem` x || r `elem` x
             then (l:r:x):xs
             else x : addToClasses xs (Eq l r)

combine acc []     = acc
combine []  (c:cs) = combine [c] cs
combine acc (c:cs) = case nub (overlaps c) of
                          [] -> combine (c:acc) cs
                          xs -> combine [c ++ concat xs] (without xs)
  where classesWith t = filter (t `elem`) (acc ++ cs)
        overlaps      = foldr ((++) . classesWith) []
        without xs    = filter (`notElem` xs) (acc ++ cs)

unSomeClasses :: [Equation] -> [WithSig [Test.QuickSpec.Term.Expr a]]
unSomeClasses eqs = map mkUnSomeClass (classesFromEqs eqs)

unSomeClassesN :: [Equation] -> [Test.QuickSpec.Signature.Sig -> [Test.QuickSpec.Term.Expr a]]
unSomeClassesN eqs = map mkUnSomeClassN (classesFromEqs eqs)


mkUnSomeClass :: [Term] -> WithSig [Test.QuickSpec.Term.Expr a]
mkUnSomeClass []     = WS nil'
mkUnSomeClass (x:xs) = case (termToExpr x, mkUnSomeClass xs) of
                            (WS y, WS ys) -> WS ((cons' $$$ y) $$$ ys)

mkUnSomeClassN :: [Term] -> Test.QuickSpec.Signature.Sig -> [Test.QuickSpec.Term.Expr a]
mkUnSomeClassN []     sig = []
mkUnSomeClassN (x:xs) sig = case (termToExprN x, mkUnSomeClassN xs) of
                                 (y, ys) -> y sig : ys sig




unSomePrune :: [WithSig [Test.QuickSpec.Term.Expr a]] -> WithSig [Test.QuickSpec.Equation.Equation]
unSomePrune clss = WS ((((prune' $$$ arg1) $$$ arg2) $$$ id') $$$ arg3)
  where arg1  = ((initial' $$$ (maxDepth' $$$ "givenSig")) $$$ (symbols' $$$ "givenSig")) $$$ mkUniv2 clss'
        arg2  = (filter' $$$ compose' not' isUndefined') $$$ getTermHead clss'
        arg3  = sort' $$$ mkEqs2 clss'
        clss' = map (\(WS x) -> x) clss

unSomePruneN :: [Test.QuickSpec.Signature.Sig -> [Test.QuickSpec.Term.Expr Term]] -> Test.QuickSpec.Signature.Sig -> [Test.QuickSpec.Equation.Equation]
unSomePruneN clss sig = ((((prune $ arg1) $ arg2) $ id) $ arg3)
  where arg1  = ((initial $ (maxDepth $ sig)) $ (symbols $ sig)) $ mkUniv2N clss'
        arg2  = (filter $ not . isUndefined) $ getTermHeadN clss'
        arg3  = sort $ mkEqs2N clss'
        clss' = map ($ sig) clss

        symbols     = Test.QuickSpec.Signature.symbols
        prune       = Test.QuickSpec.Main.prune
        maxDepth    = Test.QuickSpec.Signature.maxDepth
        initial     = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
        isUndefined = Test.QuickSpec.Term.isUndefined


mkUniv2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2 = foldr (\x -> ((append' $$$ ((map' $$$ univ2) $$$ x)) $$$)) nil'

mkUniv2N :: Typeable a => [[Test.QuickSpec.Term.Expr a]] -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2N = foldr (\x -> (((++) $ ((map $ univ2N) $ x)) $)) []



univ2 :: TypedExpr (Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term)
univ2 = tlam "y" body `withType` t
  where body = (conTagged' $$$ (conSome' $$$ (conWitness' $$$ (strip' $$$ "y")))) $$$ (term' $$$ "y")
        t    = "Data.Typeable.Typeable a => Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term"

univ2N :: Data.Typeable.Typeable a => Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term
univ2N y = (conTagged $ (conSome $ (conWitness $ (stripN $ y)))) $ (term $ y)
  where conTagged  = Test.QuickSpec.Utils.Typed.Tagged
        conSome    = Test.QuickSpec.Utils.Typed.Some
        conWitness = Test.QuickSpec.Utils.Typed.Witness



conWitness' :: TypedExpr (a -> Test.QuickSpec.Utils.Typed.Witnessed a)
conWitness' = TE $ qualified "Test.QuickSpec.Utils.Typed" "Witness"

conTagged' :: TypedExpr (Test.QuickSpec.Utils.Typed.Witness -> a -> Test.QuickSpec.Utils.Typed.Tagged a)
conTagged' = TE $ qualified "Test.QuickSpec.Utils.Typed" "Tagged"

strip' :: TypedExpr (Test.QuickSpec.Term.Expr Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term)
strip' = tlam "x" body `withType` "Test.QuickSpec.Term.Expr a -> a"
  where body     = TE $ withMods ["Data.Typeable"] undef
        TE undef = undefined'

undefined' = TE "Prelude.undefined"

stripN :: Test.QuickSpec.Term.Expr a -> a
-- TypedExpr (Test.QuickSpec.Term.Expr Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term)
stripN x = undefined




getTermHead :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Term.Term]
getTermHead = foldr (\c -> ((cons' $$$ (term' $$$ (head' $$$ c))) $$$)) nil'

getTermHeadN = foldr (\c -> (((:) $ (term $ (head $ c))) $)) []



term = Test.QuickSpec.Term.term



mkEqs2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Equation.Equation]
mkEqs2 []     = nil'
mkEqs2 (c:cs) = (append' $$$ (f $$$ c)) $$$ mkEqs2 cs
  where f    = TE $ withMods ["Test.QuickSpec.Equation"] g
        TE g = tlam "(z:zs)" "[Test.QuickSpec.Term.term y :=: Test.QuickSpec.Term.term z | y <- zs]"

-- mkEqs2N :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Equation.Equation]
mkEqs2N []     = []
mkEqs2N (c:cs) = ((++) $ (f $ c)) $ mkEqs2N cs
  where f (z:zs) = [term y Test.QuickSpec.Equation.:=: term z | y <- zs]




sort' :: Ord a => TypedExpr ([a] -> [a])
sort' = TE $ qualified "Data.List" "sort"

termToExpr :: Term -> WithSig (Test.QuickSpec.Term.Expr a)
termToExpr t = WS (((expr' $$$ term) $$$ arity) $$$ eval)
  where WS term = renderTerm t

        arity :: TypedExpr Int
        arity = TE (raw (show (let Arity a = termArity t in a)))

        -- Used for variable instantiation (which we avoid) and specifying type
        eval  = undefined' `withType` ("Valuation -> (" ++ typeName (termType' t) ++ ")")

        expr' :: TypedExpr (_ -> Int -> _ -> Test.QuickSpec.Term.Expr _)
        expr' = TE (qualified "Test.QuickSpec.Term" "Expr")

termToExprN :: Term -> Test.QuickSpec.Signature.Sig -> (Test.QuickSpec.Term.Expr a)
termToExprN t sig = (((expr' $ term) $ arity) $ eval)
  where expr' = Test.QuickSpec.Term.Expr
        term  = renderTermN t sig sig
        arity = let Arity a = termArity t in a
        eval  = undefined



append' :: TypedExpr ([a] -> [a] -> [a])
append' = "(++)"

unType :: TypedExpr a -> TypedExpr b
unType (TE e) = TE e

withMods' :: [Mod] -> TypedExpr a -> TypedExpr a
withMods' ms (TE e) = TE (withMods ms (withQS e))



pruneEqs :: [Equation] -> IO (Maybe String)
pruneEqs = pruneEqs' showEqsOnLines

pruneEqsN :: [Equation] -> IO String
pruneEqsN eqs = pruneEqsN' showEqsOnLinesN eqs



newtype Z = Z () deriving (Eq, Show, Typeable)
newtype S a = S a deriving (Eq, Show, Typeable)
instance Ord Z where compare _ _ = EQ



showEqsOnLines (WS pruned) = WS (unlines' $$$ shown')
  where shown' = (map' $$$ showEq') $$$ pruned
        showEq = TE . withPkgs ["mlspec-helper"] $ qualified "MLSpec.Helper" "showEq'"
        showEq' = ("(.)" $$$ "Prelude.show") $$$ (showEq $$$ "givenSig")

showEqsOnLinesN mk_pruned sig = (unlines $ shown')
  where shown' = (map $ fullyShowEq) $ (mk_pruned sig)
        fullyShowEq = ((.) $ show) $ (showEq' $ sig)



pruneEqs' :: (WithSig [Test.QuickSpec.Equation.Equation] -> WithSig String) -> [Equation] -> IO (Maybe String)
pruneEqs' f eqs = exec main''
  where pruned   = unSomePrune clss
        sig      = sigFromEqs eqs
        clss     = unSomeClasses eqs
        main''   = TE . withMods ["Data.Typeable"]
                      . withPreamble decs
                      . withFlags ["--", "-fcontext-stack=1000"]
                      $ main'
        TE main' = "Prelude.putStrLn" $$$ renderWithSig (f pruned) sig
        decs     = concat ["newtype Z = Z () deriving (Eq, Show, Typeable);",
                           "newtype S a = S a deriving (Eq, Show, Typeable);",
                           "instance Ord Z where { compare _ _ = Prelude.EQ; };",
                           "instance (Ord a) => Ord (S a) where { compare (Main.S x) (Main.S y) = Prelude.compare x y; };"]

pruneEqsN' :: ((Test.QuickSpec.Signature.Sig -> [Test.QuickSpec.Equation.Equation]) -> Test.QuickSpec.Signature.Sig -> String) -> [Equation] -> IO _
pruneEqsN' f eqs = return (renderWithSigN (f pruned) sig)
  where pruned = unSomePruneN clss
        sig    = sigFromEqs eqs
        clss   = unSomeClassesN eqs



putErr = hPutStrLn stderr
