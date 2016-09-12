{-# LANGUAGE OverloadedStrings, PartialTypeSignatures #-}

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

import Data.List
import Data.Maybe
import Data.String
import Language.Eval.Internal
import Math.Equation.Internal.Types
import System.Environment
import System.IO
import System.IO.Unsafe
import Text.Read  -- Uses String as part of base, not Text

-- Used for their types
import qualified Test.QuickCheck.Gen
import qualified Test.QuickSpec
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

newtype WithSig a = WS (TypedExpr a)

renderWithSig :: WithSig a -> Sig -> TypedExpr a
renderWithSig (WS (TE e)) sig = TE (e {
      eExpr = "let { givenSig = (" ++ eExpr s ++ "); } in (" ++ eExpr e ++ ")"
    })
  where TE s = render sig

sigToSym :: Term -> WithSig Test.QuickSpec.Term.Symbol
sigToSym t = WS (head' $$$ filtered)
  where pred     = tlam "x" (("==" $$$ ("name" $$$ "x")) $$$ name')
        Name n   = case t of
                        C c   -> constName c
                        V v   -> varName   v
                        App{} -> error ("Tried to get symbol for " ++ show t)
        name'    = TE (asString n)
        filtered = (filter' $$$ pred) $$$ (symbols' $$$ "givenSig")

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
        v = TE . raw $ "undefined :: (" ++ typeName t ++ ")"

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
map' = "map"

return' :: Monad m => TypedExpr (a -> m b)
return' = "return"

head' :: TypedExpr ([a] -> a)
head' = "head"

nil' :: TypedExpr [a]
nil' = "([])"

cons' :: TypedExpr (a -> [a] -> [a])
cons' = "(:)"

any' :: TypedExpr ((a -> Bool) -> [a] -> Bool)
any' = "any"

show' :: Show a => TypedExpr (a -> String)
show' = "show"

all' :: TypedExpr ((a -> Bool) -> [a] -> Bool)
all' = "all"

join' :: Monad m => TypedExpr (m (m a) -> m a)
join' = TE . withMods ["Control.Monad"] $ "join"

mappend' :: TypedExpr a -> TypedExpr a -> TypedExpr a
mappend' x y = (TE "mappend" $$$ x) $$$ y

id' :: TypedExpr (a -> a)
id' = "id"

filter' :: TypedExpr ((a -> Bool) -> [a] -> [a])
filter' = "filter"

not' :: TypedExpr (Bool -> Bool)
not' = "not"

compose' :: TypedExpr (b -> c) -> TypedExpr (a -> b) -> TypedExpr (a -> c)
compose' f g = ("(.)" $$$ f) $$$ g

unlines' :: TypedExpr ([String] -> String)
unlines' = "unlines"

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
  where undef = TE . raw $ "undefined :: (" ++ typeName t ++ ")"

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

mkUnSomeClass :: [Term] -> WithSig [Test.QuickSpec.Term.Expr a]
mkUnSomeClass []     = WS nil'
mkUnSomeClass (x:xs) = case (termToExpr x, mkUnSomeClass xs) of
                            (WS y, WS ys) -> WS ((cons' $$$ y) $$$ ys)

unSomePrune :: [WithSig [Test.QuickSpec.Term.Expr a]] -> WithSig [Test.QuickSpec.Equation.Equation]
unSomePrune clss = WS ((((prune' $$$ arg1) $$$ arg2) $$$ id') $$$ arg3)
  where arg1  = ((initial' $$$ (maxDepth' $$$ "givenSig")) $$$ (symbols' $$$ "givenSig")) $$$ mkUniv2 clss'
        arg2  = (filter' $$$ compose' not' isUndefined') $$$ getTermHead clss'
        arg3  = sort' $$$ mkEqs2 clss'
        clss' = map (\(WS x) -> x) clss

mkUniv2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2 = foldr (\x -> ((append' $$$ ((map' $$$ univ2) $$$ x)) $$$)) nil'

univ2 :: TypedExpr (Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term)
univ2 = tlam "y" body `withType` t
  where body = (conTagged' $$$ (conSome' $$$ (conWitness' $$$ (strip' $$$ "y")))) $$$ (term' $$$ "y")
        t    = "Data.Typeable.Typeable a => Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term"

conWitness' :: TypedExpr (a -> Test.QuickSpec.Utils.Typed.Witnessed a)
conWitness' = TE $ qualified "Test.QuickSpec.Utils.Typed" "Witness"

conTagged' :: TypedExpr (Test.QuickSpec.Utils.Typed.Witness -> a -> Test.QuickSpec.Utils.Typed.Tagged a)
conTagged' = TE $ qualified "Test.QuickSpec.Utils.Typed" "Tagged"

strip' :: TypedExpr (Test.QuickSpec.Term.Expr Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term)
strip' = tlam "x" body `withType` "Test.QuickSpec.Term.Expr a -> a"
  where body = TE $ withMods ["Data.Typeable"] "undefined"

getTermHead :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Term.Term]
getTermHead = foldr (\c -> ((cons' $$$ (term' $$$ (head' $$$ c))) $$$)) nil'

mkEqs2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Equation.Equation]
mkEqs2 []     = nil'
mkEqs2 (c:cs) = (append' $$$ (f $$$ c)) $$$ mkEqs2 cs
  where f    = TE $ withMods ["Test.QuickSpec.Equation"] g
        TE g = tlam "(z:zs)" "[term y :=: term z | y <- zs]"

sort' :: Ord a => TypedExpr ([a] -> [a])
sort' = TE $ qualified "Data.List" "sort"

termToExpr :: Term -> WithSig (Test.QuickSpec.Term.Expr a)
termToExpr t = WS (((expr' $$$ term) $$$ arity) $$$ eval)
  where WS term = renderTerm t

        arity :: TypedExpr Int
        arity = TE (raw (show (let Arity a = termArity t in a)))

        -- Used for variable instantiation (which we avoid) and specifying type
        eval  = "undefined" `withType` ("Valuation -> (" ++ typeName (termType' t) ++ ")")

        expr' :: TypedExpr (_ -> Int -> _ -> Test.QuickSpec.Term.Expr _)
        expr' = TE (qualified "Test.QuickSpec.Term" "Expr")

append' :: TypedExpr ([a] -> [a] -> [a])
append' = "(++)"

unType :: TypedExpr a -> TypedExpr b
unType (TE e) = TE e

withMods' :: [Mod] -> TypedExpr a -> TypedExpr a
withMods' ms (TE e) = TE (withMods ms (withQS e))

pruneEqs :: [Equation] -> IO (Maybe String)
pruneEqs = pruneEqs' showEqsOnLines

showEqsOnLines (WS pruned) = WS (unlines' $$$ shown')
  where shown' = (map' $$$ showEq') $$$ pruned
        showEq = TE . withPkgs ["mlspec-helper"] $ qualified "MLSpec.Helper" "showEq'"
        showEq' = ("(.)" $$$ "show") $$$ (showEq $$$ "givenSig")

pruneEqs' :: (WithSig [Test.QuickSpec.Equation.Equation] -> WithSig String) -> [Equation] -> IO (Maybe String)
pruneEqs' f eqs = exec main''
  where pruned   = unSomePrune clss
        sig      = sigFromEqs eqs
        clss     = unSomeClasses eqs
        main''   = TE $ withPreamble decs main'
        TE main' = "putStrLn" $$$ renderWithSig (f pruned) sig
        decs     = concat ["newtype Z = Z () deriving (Eq, Show, Typeable);",
                           "newtype S a = S a deriving (Eq, Show, Typeable);",
                           "instance Ord Z where compare _ _ = EQ;"]

putErr = hPutStrLn stderr
