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
import qualified Data.Map
import qualified Data.Ord
import Data.String
import Data.Typeable
import Debug.Trace (traceShow)
import Language.Eval.Internal
import qualified Language.Haskell.Exts.Syntax
import qualified Language.Haskell.Exts.Parser as HSE.Parser
import Math.Equation.Internal.Types
import MLSpec.Helper
import System.Environment
import System.IO
import System.IO.Unsafe
import Text.Read  -- Uses String as part of base, not Text

-- Used for their types
import qualified Test.QuickCheck.Gen
import qualified Test.QuickCheck.Random
import qualified Test.QuickSpec
import qualified Test.QuickSpec.Main
import qualified Test.QuickSpec.Signature
import qualified Test.QuickSpec.Term
import qualified Test.QuickSpec.TestTree
import qualified Test.QuickSpec.Utils
import qualified Test.QuickSpec.Utils.Typeable
import qualified Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap
import qualified Test.QuickSpec.Utils.TypeRel (TypeRel, singleton)
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

renderTermN t sig = case (t, sigToSymN t sig) of
    (App l r _, _  ) -> case (renderTermN l sig, renderTermN r sig) of
                             (f_l, f_r) -> app f_l f_r
    (C c,       f_s) -> const f_s
    (V v,       f_s) -> var   f_s
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
renderWithSigN e sig = e (renderN sig)

renderN (Sig cs vs) = mappend (renderQSConsts cs) (renderQSVars vs)

renderQSConsts = foldr (mappend . renderQSConst) mempty

renderQSVars   = foldr (mappend . renderQSVarType) mempty . collectTypes
  where collectTypes = groupBy eqTypes . sortBy ordTypes
        eqTypes  (Var t1 _ _) (Var t2 _ _) = t1 == t2
        ordTypes (Var t1 _ _) (Var t2 _ _) = compare t1 t2


renderQSVarType [] = Test.QuickSpec.Signature.emptySig
renderQSVarType vs@(Var t _ (Arity a):_) = case getVal (getRep t) of
  MkHT x -> Test.QuickSpec.Signature.variableSig [
                Test.QuickSpec.Term.Variable
                  (Test.QuickSpec.Term.Atom
                    (Test.QuickSpec.Term.symbol (unName (varName v)) a x)
                    (Test.QuickSpec.Term.pgen (return x)))
              | v <- vs ]
              `mappend` mconcat [ Test.QuickSpec.Signature.totalSig
                                    (Test.QuickSpec.Term.totalGen
                                      (Test.QuickSpec.Term.pgen (return x)))
                                | v <- vs ]
              `mappend` mconcat [ Test.QuickSpec.Signature.partialSig
                                    (Test.QuickSpec.Term.partialGen
                                      (Test.QuickSpec.Term.pgen (return x)))
                                | v <- vs ]
              `mappend` Test.QuickSpec.Signature.typeSig x

renderQSVarType2 :: [Var] -> Test.QuickSpec.Signature.Sig
renderQSVarType2 vs = extend vs variablesSig
  where variablesSig = Test.QuickSpec.Signature.emptySig {
                           Test.QuickSpec.Signature.variables =
                             Data.Map.fromList (zipWith getVar vs [0..])
                         }

        getVar v@(Var t _ (Arity a)) idx =
          let rep = repToQSRep (getRep t)
           in case getVal (getRep t) of
                MkHT x -> (rep, Test.QuickSpec.Utils.Typed.Some
                                  (Test.QuickSpec.Utils.Typed.O
                                    [Test.QuickSpec.Term.Variable {
                                        Test.QuickSpec.Term.unVariable = Test.QuickSpec.Term.Atom {
                                            Test.QuickSpec.Term.sym = Test.QuickSpec.Term.Symbol {
                                                Test.QuickSpec.Term.index = idx,
                                                Test.QuickSpec.Term.name  = unName (varName v),
                                                Test.QuickSpec.Term.symbolArity = a,
                                                Test.QuickSpec.Term.silent = False,
                                                Test.QuickSpec.Term.undef = False,
                                                Test.QuickSpec.Term.symbolType = rep
                                              },
                                            Test.QuickSpec.Term.value = Test.QuickSpec.Term.pgen (return x)
                                          }
                                      }]))
        extend [] sig = sig
        extend (Var t _ (Arity a):xs) sig = extend xs (extendSig t a sig)

extendSig t a sig = case getVal (getRep t) of
  MkHT x -> extendOrd t a (addArrowTypes sig t a) `mappend` Test.QuickSpec.Signature.typeSig x


extendOrd t 0 sig = case getVal (getRep t) of
  MkHT x -> sig `mappend` Test.QuickSpec.Signature.ord x
extendOrd (Language.Haskell.Exts.Syntax.TyFun _ i o) a sig =
  extendSig o (a-1) sig
extendOrd t a sig = error ("Arity " ++ show a ++ " for non-function type " ++ show t)

addArrowTypes sig t 0 = case getVal (getRep t) of
  MkHT x -> sig `mappend` Test.QuickSpec.Signature.typeSig x
addArrowTypes sig (Language.Haskell.Exts.Syntax.TyFun _ i o) a =
  case getVal (getRep i) of
    MkHT x -> Test.QuickSpec.Signature.typeSig x `mappend` addArrowTypes sig o (a-1)

-- Conceptually the same as `fun0`, `fun1`, etc. but we have to bypass those
-- wrappers as we need to supply our own TypeRep
renderQSConst :: Const -> Test.QuickSpec.Signature.Sig
renderQSConst (Const (Arity a) (Name n) t) = extendSig t a constantSig
  where rawTyRep = getRep t

        tyrep = repToQSRep rawTyRep

        typerelsingleton :: Typeable a => Test.QuickSpec.Term.Constant a -> Test.QuickSpec.Utils.TypeRel.TypeRel Test.QuickSpec.Term.Constant
        typerelsingleton x  = typeMapfromList (Test.QuickSpec.Utils.Typed.O [x])

        typeMapfromList :: Typeable a => f a -> Test.QuickSpec.Utils.TypeMap.TypeMap f
        typeMapfromList x = Data.Map.fromList [ (tyrep, Test.QuickSpec.Utils.Typed.Some x) ]

        constantSig = case getVal rawTyRep of
          MkHT x -> Test.QuickSpec.Signature.emptySig {
            Test.QuickSpec.Signature.constants = typerelsingleton
              (Test.QuickSpec.Term.Constant
                (Test.QuickSpec.Term.Atom
                  (Test.QuickSpec.Term.Symbol 0 n a False False tyrep)
                  x))  -- Pruning equations shouldn't force any values
            }

type ListOfConstants = Test.QuickSpec.Utils.Typed.O
  Test.QuickSpec.Utils.Typed.List
  Test.QuickSpec.Term.Constant

repToQSRep tr = (Test.QuickSpec.Utils.Typeable.typeOf [()]) {
                    Test.QuickSpec.Utils.Typeable.unTypeRep = tr
                  }

-- Turn a normalised Type (e.g. `S (S Z) -> S Z`) into a TypeRep
getRep :: Type -> TypeRep
getRep t = case t of
    Language.Haskell.Exts.Syntax.TyFun _ l r -> mkFunTy (getRep l) (getRep r)

    Language.Haskell.Exts.Syntax.TyApp _
      (Language.Haskell.Exts.Syntax.TyCon _
        (Language.Haskell.Exts.Syntax.UnQual _
         (Language.Haskell.Exts.Syntax.Ident _ "S")))
      x -> mkTyConApp sCon [getRep x]

    Language.Haskell.Exts.Syntax.TyCon _
      (Language.Haskell.Exts.Syntax.UnQual _
        (Language.Haskell.Exts.Syntax.Ident _ "Z")) -> typeRep [Z ()]

    _ -> error ("Unknown type '" ++ show t ++ "'. Did you forget replaceTypes?")

  where sCon = typeRepTyCon (typeRep [S (Z ())])  -- The Z gets discarded

-- Construct a value of some normalised type. We use an existential so that
-- getVal can return a (wrapped up) value of the correct type. Since we should
-- only need these values in order to match up their TypeReps, this should be
-- sufficient.
getVal :: TypeRep -> HasType
getVal tr = case () of
    _ | thisCon == zCon   -> MkHT (Z ())
    _ | thisCon == sCon   -> case typeRepArgs tr of
                                  []   -> error ("No args in " ++ show tr)
                                  x:xs -> case getVal x of
                                               MkHT x -> MkHT (S x)
    _ | thisCon == funCon -> case map getVal (typeRepArgs tr) of
                                  [MkHT i, MkHT o] -> MkHT (\x -> case asTypeOf i x of
                                                                       _ -> o)
  where thisCon = typeRepTyCon tr
        funCon  = typeRepTyCon (typeRep [not])  -- Simple monomorphic function
        zCon    = typeRepTyCon (typeRep [Z ()])
        sCon    = typeRepTyCon (typeRep [S (Z ())])  -- The Z gets discarded

data HasType = forall a. (Ord a, Typeable a) => MkHT a

instance Show HasType where
  show (MkHT x) = "HasType(" ++ show (typeRep [x]) ++ ")"

data TSig a where
   TsZ :: TSig Z
   TsS :: TSig a -> TSig (S a)
   TsF :: TSig a -> TSig b -> TSig (a -> b)

tsToV :: TSig a -> a
tsToV  TsZ      = Z ()
tsToV (TsS x)   = S (tsToV x)
tsToV (TsF f x) = \a -> tsToV x

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

class Base a where
  base :: a

instance Base Z where
  base = Z ()

instance (Base a) => Base (S a) where
  base = S base

instance (Base a, Base b) => Base (a -> b) where
  base = \x -> base

data E = forall a. Base a => E a

zP :: Z
zP = undefined

sP :: a -> (S a)
sP _ = undefined

fP :: a -> b -> (a -> b)
fP _ _ = undefined

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
sigToSymN t sig = case filter pred symbols of
                       []  -> error . show $
                         (("Error",   "No symbol found"),
                          ("term t",  t),
                          ("Name n",  n),
                          ("symbols", symbols),
                          ("sig",     sig))
                       x:_ -> x
  where pred x   = name x == n
        Name n   = case t of
                        C c -> constName c
                        V v -> varName   v
                        App{} -> error ("Tried to get sym for " ++ show t)

        symbols = Test.QuickSpec.Signature.symbols sig
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

checkNames :: [Name] -> [Test.QuickSpec.Term.Symbol] -> Bool
checkNames ns syms = all (isIn syms) (map unName ns)

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

isIn :: [Test.QuickSpec.Term.Symbol] -> String -> Bool
isIn syms n = any f syms
  where f = (n ==) . Test.QuickSpec.Term.name

genOf' :: Type -> TypedExpr (Test.QuickCheck.Gen.Gen a)
genOf' t = return' $$$ undef
  where undef = TE . raw $ "Prelude.undefined :: (" ++ typeName t ++ ")"

classesFromEqs :: [Equation] -> [[Term]]
classesFromEqs eqs = trc ("classesFromEqs clss",  clss)  .
                     trc ("classesFromEqs clss'", clss') $
                     result
  where result = combine [] clss'
        clss   = foldl addToClasses [] eqs
        clss'  = map nub (foldl extend clss terms)
        terms  = concatMap (\(Eq l r) -> l : r : subTerms l ++ subTerms r) eqs

        subTerms (C _)       = []
        subTerms (V _)       = []
        subTerms (App l r _) = let l' = if termArity l == Arity 0
                                           then [l]
                                           else []
                                   r' = if termArity l == Arity 0
                                           then [l]
                                           else []
                                   ls = if termArity l > Arity 0
                                           then subTerms l
                                           else []
                                   rs = if termArity r > Arity 0
                                           then subTerms r
                                           else []
                                in l' ++ r' ++ ls ++ rs

        extend []     t = [[t]]
        extend (c:cs) t = if t `elem` c
                             then c:cs
                             else c : extend cs t

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

unSomeClassesN :: (Typeable a) => [Equation] -> Test.QuickSpec.Signature.Sig -> [[Test.QuickSpec.Term.Expr a]]
unSomeClassesN eqs sig = trc ("unSomeClassesN classes",  classes)  .
                         trc ("unSomeClassesN unsorted", unsorted) .
                         trc ("unSomeClassesN result",   result)   $
                         result
  where classes  = classesFromEqs eqs
        unsorted = map (sort . mkUnSomeClassN sig) classes
        result   = sort unsorted

unSomeClassesN2 :: [Equation]
                -> Test.QuickSpec.Signature.Sig
                -> [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
unSomeClassesN2 eqs sig = collectExprs result
  where classes  = classesFromEqs eqs
        result   = unSomeSortedClasses classes sig

unSomeSortedClasses classes sig =
  unSomeSortedQSClasses (map (mkUnSomeClassN2 sig) classes)

unSomeSortedQSClasses classes = sortBy multi classes
  where multi (x:_) (y:_) = compareTerms x y

compareTerms (Test.QuickSpec.Utils.Typed.Some x) (Test.QuickSpec.Utils.Typed.Some y) =
  compare (Test.QuickSpec.Term.term x) (Test.QuickSpec.Term.term y)

collectExprs :: [[Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]]
        -> [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
collectExprs arg@[]   = []
collectExprs (xs:xss) = collectOne xs : collectExprs xss
  where collectOne :: [Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]
                   -> Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr
        collectOne xs = case xs of
          []                                     -> Test.QuickSpec.Utils.Typed.Some
                                                      (Test.QuickSpec.Utils.Typed.O
                                                        ([] :: [Test.QuickSpec.Term.Expr ()]))
          [Test.QuickSpec.Utils.Typed.Some x]    -> Test.QuickSpec.Utils.Typed.Some
                                                      (Test.QuickSpec.Utils.Typed.O
                                                        [x])
          (Test.QuickSpec.Utils.Typed.Some x:xs) -> case collectOne xs of
            Test.QuickSpec.Utils.Typed.Some
              (Test.QuickSpec.Utils.Typed.O (y:xs')) -> case cast x `asTypeOf` Just y of
                Just x' -> Test.QuickSpec.Utils.Typed.Some
                             (Test.QuickSpec.Utils.Typed.O (x':y:xs'))

mkUnSomeClass :: [Term] -> WithSig [Test.QuickSpec.Term.Expr a]
mkUnSomeClass []     = WS nil'
mkUnSomeClass (x:xs) = case (termToExpr x, mkUnSomeClass xs) of
                            (WS y, WS ys) -> WS ((cons' $$$ y) $$$ ys)

mkUnSomeClassN :: Test.QuickSpec.Signature.Sig -> [Term] -> [Test.QuickSpec.Term.Expr a]
mkUnSomeClassN sig []     = []
mkUnSomeClassN sig (x:xs) = termToExprN x sig : mkUnSomeClassN sig xs

mkUnSomeClassN2 :: Test.QuickSpec.Signature.Sig
                -> [Term]
                -> [Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]
mkUnSomeClassN2 sig trms = sortBy compareTerms (mkUnSomeClassN2' sig trms)

mkUnSomeClassN2' sig []     = []
mkUnSomeClassN2' sig (x:xs) =
    case termType (setForTerm x) of
         Nothing -> error ("No type for " ++ show x)
         Just t  -> case getVal (getRep t) of
                         MkHT v -> (Test.QuickSpec.Utils.Typed.Some
                                     (Test.QuickSpec.Term.Expr term
                                                               arity
                                                               (const v))) : xs'
  where term        = renderTermN x sig
        Arity arity = termArity x
        xs' = mkUnSomeClassN2' sig xs

unSomePrune :: [WithSig [Test.QuickSpec.Term.Expr a]] -> WithSig [Test.QuickSpec.Equation.Equation]
unSomePrune clss = WS ((((prune' $$$ arg1) $$$ arg2) $$$ id') $$$ arg3)
  where arg1  = ((initial' $$$ (maxDepth' $$$ "givenSig")) $$$ (symbols' $$$ "givenSig")) $$$ mkUniv2 clss'
        arg2  = (filter' $$$ compose' not' isUndefined') $$$ getTermHead clss'
        arg3  = sort' $$$ mkEqs2 clss'
        clss' = map (\(WS x) -> x) clss

unSomePruneN :: [[Test.QuickSpec.Term.Expr Term]]
             -> Test.QuickSpec.Signature.Sig
             -> [Test.QuickSpec.Equation.Equation]
unSomePruneN clss sig =
    trc ("unSomePruneN reps", reps) .
    trc ("unSomePruneN sig",  sig)  .
    trc ("unSomePruneN eqs",  eqs)  $
    result
  where result = Test.QuickSpec.Main.prune ctx reps id eqs

        ctx   = mkCxt clss sig

        reps  = classesToReps clss

        eqs   = sort (mkEqs2N clss)

mkCxt :: (Typeable a) => [[Test.QuickSpec.Term.Expr a]]
                      -> Test.QuickSpec.Signature.Sig
                      -> Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context
mkCxt clss sig = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
                   (Test.QuickSpec.Signature.maxDepth sig)
                   (Test.QuickSpec.Signature.symbols  sig)
                   (mkUniv2N clss)

mkCxt2 :: [[Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]]
       -> Test.QuickSpec.Signature.Sig
       -> Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context
mkCxt2 clss sig = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
                   (Test.QuickSpec.Signature.maxDepth sig)
                   (Test.QuickSpec.Signature.symbols  sig)
                   (mkUniv3 clss)

mkCxt3 :: [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
       -> Test.QuickSpec.Signature.Sig
       -> Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context
mkCxt3 clss sig = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
                   (Test.QuickSpec.Signature.maxDepth sig)
                   (Test.QuickSpec.Signature.symbols  sig)
                   (mkUniv4 clss)
  where mkUniv4 :: [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
                -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
        mkUniv4 = concatMap (Test.QuickSpec.Utils.Typed.several
                              (map (Test.QuickSpec.Utils.Typed.tagged
                                     Test.QuickSpec.Term.term)))


classesToReps clss = filter (not . Test.QuickSpec.Term.isUndefined)
                            (map (term . head) clss)

classesToReps2 :: [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
               -> [Test.QuickSpec.Term.Term]
classesToReps2 clss = filter (not . Test.QuickSpec.Term.isUndefined) reps
  where reps = map (Test.QuickSpec.Utils.Typed.several getRep) clss
        getRep :: [Test.QuickSpec.Term.Expr a]
               -> Test.QuickSpec.Term.Term
        getRep (x:_) = term x

unSomePruneEqs :: [[Test.QuickSpec.Term.Expr Term]]
               -> Test.QuickSpec.Signature.Sig
               -> [Test.QuickSpec.Equation.Equation]
               -> [Test.QuickSpec.Equation.Equation]
unSomePruneEqs clss sig eqs = Test.QuickSpec.Main.prune ctx arg2 id eqs
  where ctx   = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
                  (Test.QuickSpec.Signature.maxDepth sig)
                  (Test.QuickSpec.Signature.symbols  sig)
                  (mkUniv2N clss)
        arg2  = filter (not . Test.QuickSpec.Term.isUndefined)
                       (getTermHeadN clss)



mkUniv2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2 = foldr (\x -> ((append' $$$ ((map' $$$ univ2) $$$ x)) $$$)) nil'

mkUniv2N :: Typeable a => [[Test.QuickSpec.Term.Expr a]]
                       -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2N = concatMap (map univ2N)

--univ = concatMap (some2 (map (tagged term))) clss

univ2 :: TypedExpr (Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term)
univ2 = tlam "y" body `withType` t
  where body = (conTagged' $$$ (conSome' $$$ (conWitness' $$$ (strip' $$$ "y")))) $$$ (term' $$$ "y")
        t    = "Data.Typeable.Typeable a => Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term"

univ2N :: Data.Typeable.Typeable a => Test.QuickSpec.Term.Expr a
                                   -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term
univ2N y = Test.QuickSpec.Utils.Typed.Tagged
             (Test.QuickSpec.Utils.Typed.Some
               (Test.QuickSpec.Utils.Typed.Witness (stripN y)))
             (term y)

mkUniv3 :: [[Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]]
        -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv3 = concatMap (map (Test.QuickSpec.Utils.Typed.some
                           (Test.QuickSpec.Utils.Typed.tagged
                             Test.QuickSpec.Term.term)))

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
stripN x = Test.QuickSpec.Term.eval x (Test.QuickSpec.Term.Valuation unvar)
  where unvar = runGen                       .
                Test.QuickSpec.Term.totalGen .
                Test.QuickSpec.Term.value    .
                Test.QuickSpec.Term.unVariable
        qcgen    = Test.QuickCheck.Random.mkQCGen 0
        runGen g = Test.QuickCheck.Gen.unGen g qcgen 0




getTermHead :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Term.Term]
getTermHead = foldr (\c -> ((cons' $$$ (term' $$$ (head' $$$ c))) $$$)) nil'

getTermHeadN = map (Test.QuickSpec.Term.term . head)



term = Test.QuickSpec.Term.term



mkEqs2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Equation.Equation]
mkEqs2 []     = nil'
mkEqs2 (c:cs) = (append' $$$ (f $$$ c)) $$$ mkEqs2 cs
  where f    = TE $ withMods ["Test.QuickSpec.Equation"] g
        TE g = tlam "(z:zs)" "[Test.QuickSpec.Term.term y :=: Test.QuickSpec.Term.term z | y <- zs]"

mkEqs2N cs = sort (concatMap f cs)
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

termToExprN :: Term
            -> Test.QuickSpec.Signature.Sig
            -> (Test.QuickSpec.Term.Expr a)
termToExprN t sig = Test.QuickSpec.Term.Expr term arity eval
  where term        = renderTermN t sig
        Arity arity = termArity t
        eval        = undefined



append' :: TypedExpr ([a] -> [a] -> [a])
append' = "(++)"

unType :: TypedExpr a -> TypedExpr b
unType (TE e) = TE e

withMods' :: [Mod] -> TypedExpr a -> TypedExpr a
withMods' ms (TE e) = TE (withMods ms (withQS e))



pruneEqs :: [Equation] -> IO (Maybe String)
pruneEqs = pruneEqs' showEqsOnLines

newtype Z = Z () deriving (Eq, Show, Typeable)
newtype S a = S a deriving (Eq, Show, Typeable, Ord)
instance Ord Z where compare _ _ = EQ
instance Ord (a -> b) where
  compare _ _ = EQ
instance Eq (a -> b) where
  _ == _ = True


showEqsOnLines (WS pruned) = WS (unlines' $$$ shown')
  where shown' = (map' $$$ showEq') $$$ pruned
        showEq = TE . withPkgs ["mlspec-helper"] $ qualified "MLSpec.Helper" "showEq'"
        showEq' = ("(.)" $$$ "Prelude.show") $$$ (showEq $$$ "givenSig")

showEqsOnLinesN :: [Test.QuickSpec.Equation.Equation]
                -> [Equation]
showEqsOnLinesN = map qsEqToEq

qsEqToEq (l Test.QuickSpec.Equation.:=: r) = Eq (qsTermToTerm l) (qsTermToTerm r)

qsTermToTerm t = case t of
  Test.QuickSpec.Term.Var   s -> V   (symToVar   s)
  Test.QuickSpec.Term.Const s -> C   (symToConst s)
  Test.QuickSpec.Term.App l r -> App (qsTermToTerm l) (qsTermToTerm r) Nothing

symToVar s =
  let n              = Test.QuickSpec.Term.name s
      [_, rawT, idx] = splitCommas n
   in Var (case HSE.Parser.parseType rawT of
             HSE.Parser.ParseOk t'        -> unwrapParens (const () <$> t')
             HSE.Parser.ParseFailed _ err -> error (concat [
                                    "Failed to parse var type: ",
                                    err,
                                    ". Type was: ",
                                    rawT]))
          (read (init idx) :: Int)
          (Arity (Test.QuickSpec.Term.symbolArity s))

symToConst s =
  let t = HSE.Parser.parseType (show (Test.QuickSpec.Term.symbolType s))
   in Const (Arity (Test.QuickSpec.Term.symbolArity s))
            (Name (Test.QuickSpec.Term.name s))
            (case t of
               HSE.Parser.ParseOk t'        -> unwrapParens (const () <$> t')
               HSE.Parser.ParseFailed _ err -> error (concat [
                                      "Failed to parse const type: ",
                                      err,
                                      ". Type was: ",
                                      show (Test.QuickSpec.Term.symbolType s)]))

splitCommas s = if ',' `elem` s
                   then takeWhile (/= ',') s :
                        splitCommas (tail (dropWhile (/= ',') s))
                   else [s]


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

pruneEqsN :: [Equation] -> [Equation]
pruneEqsN eqs = trc ("pruneEqsN pruned",  pruned)  .
                trc ("pruneEqsN classes", classes) .
                trc ("pruneEqsN sig",     sig)     $
                result
  where pruned  = unSomePruneN classes sig
        sig     = let sig'  = renderN (sigFromEqs eqs)
                      sig'' = Test.QuickSpec.Signature.signature sig'
                   in sig'' `mappend` Test.QuickSpec.Main.undefinedsSig sig''
        result  = showEqsOnLinesN pruned
        classes = unSomeClassesN eqs sig

dumpSym s = (("index"       :: String, Test.QuickSpec.Term.index       s),
             ("name"        :: String, Test.QuickSpec.Term.name        s),
             ("symbolArity" :: String, Test.QuickSpec.Term.symbolArity s),
             ("silent"      :: String, Test.QuickSpec.Term.silent      s),
             ("undef"       :: String, Test.QuickSpec.Term.undef       s),
             ("symbolType"  :: String, Test.QuickSpec.Term.symbolType  s))

putErr = hPutStrLn stderr

debug = case unsafePerformIO (lookupEnv "DEBUG") of
  Nothing -> False
  Just "" -> False
  _       -> True

trc :: Show a => a -> b -> b
trc = if debug
         then traceShow
         else \x y -> y

instance Show (Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term) where
  show t = show ("Tagged"      :: String,
                  ("tag"       :: String,
                    ("type"    :: String, Test.QuickSpec.Utils.Typed.witnessType
                                            (Test.QuickSpec.Utils.Typed.tag t))),
                  ("erase"     :: String, Test.QuickSpec.Utils.Typed.erase t))

-- From Test.QuickSpec.Main
provable reps (t Test.QuickSpec.Equation.:=: u) = do
  res <- t Test.QuickSpec.Reasoning.NaiveEquationalReasoning.=?= u
  if res
     then return True
     else do
       state <- Test.QuickSpec.Reasoning.NaiveEquationalReasoning.get
       -- Check that we won't unify two representatives---if we do
       -- the equation is false
       t Test.QuickSpec.Reasoning.NaiveEquationalReasoning.=:= u
       reps' <- mapM Test.QuickSpec.Reasoning.NaiveEquationalReasoning.rep reps
       if sort reps' == Test.QuickSpec.Utils.usort reps'
          then return False
          else do
            Test.QuickSpec.Reasoning.NaiveEquationalReasoning.put state
            return True
