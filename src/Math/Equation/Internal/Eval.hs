{-# LANGUAGE OverloadedStrings #-}

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
import Data.String
import Language.Eval.Internal
import Math.Equation.Internal.Types

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

-- Execute an expression, by evaluating it as the value of `main`. Returns the
-- resulting stdout (or `Nothing` on error)
exec :: TypedExpr (IO a) -> IO (Maybe String)
exec (TE x) = eval' ("main = " ++) x

-- Conversion from our representations to QuickSpec expressions

renderEqs :: [Equation] -> TypedExpr [Test.QuickSpec.Equation.Equation]
renderEqs []     = nil'
renderEqs (e:es) = (cons' $$$ renderEq e) $$$ renderEqs es

renderEq :: Equation -> TypedExpr Test.QuickSpec.Equation.Equation
renderEq (Eq lhs rhs) = ("(:=:)" $$$ renderTerm lhs) $$$ renderTerm rhs

renderTerm :: Term -> TypedExpr Test.QuickSpec.Term.Term
renderTerm t = case t of
    App lhs rhs -> (app  $$$ renderTerm lhs) $$$ renderTerm rhs
    C   c       -> const $$$ (sigToSym $$$ renderConst c)
    V   v       -> var   $$$ (sigToSym $$$ renderVar   v)
  where app :: TypedExpr (Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term -> Test.QuickSpec.Term.Term)
        app   = qsQual "Test.QuickSpec.Term" "App"
        const, var :: TypedExpr (Test.QuickSpec.Term.Symbol -> Test.QuickSpec.Term.Term)
        const = qsQual "Test.QuickSpec.Term" "Const"
        var   = qsQual "Test.QuickSpec.Term" "Var"
        sigToSym = compose' head' symbols'

render :: Sig -> TypedExpr QSSig
render (Sig cs vs) = mappend' (renderConsts cs) (renderVars vs)

renderConsts :: [Const] -> TypedExpr QSSig
renderConsts []     = empty'
renderConsts (c:cs) = mappend' (renderConst c) (renderConsts cs)

renderConst :: Const -> TypedExpr QSSig
renderConst c = (f $$$ name) $$$ v
  where f :: TypedExpr (String -> () -> QSSig)
        f = TE . withQS . qualified "Test.QuickSpec.Signature" . raw $
              "fun" ++ show a
        v :: TypedExpr ()
        v = TE . raw $ "undefined :: (" ++ t ++ ")"
        Arity a = constArity c
        Name  n = constName  c
        Type  t = constType  c
        name :: TypedExpr String
        name = TE (asString n)

-- | Render a list of `Var`s as a QuickSpec `Sig`. We must be careful to avoid
--   clobbering the same variable indices, so we add each type's variables in
--   one go
renderVars :: [Var] -> TypedExpr QSSig
renderVars vs = collapse (map renderGroup (groupBy sameType vs))
  where collapse []     = empty'
        collapse (s:ss) = mappend' s (collapse ss)
        renderGroup [] = empty'
        renderGroup (v:vs) = renderTypedVars (varArity v) (varType v) (map varName (v:vs))
        sameType v1 v2 = varType v1 == varType v2

renderTypedVars :: Arity -> Type -> [Name] -> TypedExpr QSSig
renderTypedVars a t ns = ((gvars' a) $$$ names') $$$ genOf' t
  where names' :: TypedExpr [String]
        names' = collapse (map (\(Name n) -> TE (asString n)) ns)
        collapse :: [TypedExpr a] -> TypedExpr [a]
        collapse []     = nil'
        collapse (x:xs) = (cons' $$$ x) $$$ collapse xs

renderVar :: Var -> TypedExpr QSSig
renderVar v = (gv $$$ nameL) $$$ genOf' (varType v)
  where gv = gvars' (varArity v)
        Name  n = varName  v
        nameL :: TypedExpr [String]
        nameL = return' $$$ name
        name :: TypedExpr String
        name = TE (asString n)

-- Wrappers for Prelude functions

fmap' :: Functor f => TypedExpr ((a -> b) -> f a -> f b)
fmap' = "fmap"

map' :: TypedExpr ((a -> b) -> [a] -> [b])
map' = "map"

concatMap' :: TypedExpr ((a -> [b]) -> [a] -> [b])
concatMap' = "concatMap"

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

(>>$) :: TypedExpr (IO a -> IO b -> IO b)
(>>$) = "(>>)"

(>>=$) :: Monad m => TypedExpr (m a -> (a -> m b) -> m b)
(>>=$) = "(>>=)"

app' :: Applicative f => TypedExpr (f (a -> b) -> f a -> f b)
app' = "(<*>)"

($<$>$) :: Functor f => TypedExpr (a -> b) -> TypedExpr (f a) -> TypedExpr (f b)
f $<$>$ x = (fmap' $$$ f) $$$ x

($<*>$) :: Applicative f => TypedExpr (f (a -> b)) -> TypedExpr (f a) -> TypedExpr (f b)
f $<*>$ x = (app' $$$ f) $$$ x

($>>=$) :: Monad m => TypedExpr (m a) -> TypedExpr (a -> m b) -> TypedExpr (m b)
x $>>=$ f = join' $$$ ((fmap' $$$ f) $$$ x)

unsafePerformIO' :: TypedExpr (IO a -> a)
unsafePerformIO' = TE . withMods ["System.IO.Unsafe"] $ "unsafePerformIO"

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

const' :: TypedExpr (a -> b -> a)
const' = "const"

compose' :: TypedExpr (b -> c) -> TypedExpr (a -> b) -> TypedExpr (a -> c)
compose' f g = ("(.)" $$$ f) $$$ g

unlines' :: TypedExpr ([String] -> String)
unlines' = "unlines"

-- Type synonyms for verbose QuickSpec types

type QSSig = Test.QuickSpec.Signature.Sig

type Ctx = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context

type Reps = [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]

type Cls = [Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O [] Maybe)]

type Univ = [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]

-- Used in place of Test.QuickSpec.Term.Strategy, to avoid impredicativity
data Strategy where

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
gvars' (Arity a) = qsQual "Test.QuickSpec.Signature" (raw ("gvars" ++ show a))

name' :: TypedExpr (Test.QuickSpec.Term.Symbol -> String)
name' = qsQual "Test.QuickSpec.Term" "name"

signature' :: TypedExpr (a -> QSSig)
signature' = qsQual "Test.QuickSpec.Signature" "signature"

tagged' :: TypedExpr ((f a -> b) -> f a -> Test.QuickSpec.Utils.Typed.Tagged b)
tagged' = qsQual "Test.QuickSpec.Utils.Typed" "tagged"

term' :: TypedExpr (Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Term.Term)
term' = qsQual "Test.QuickSpec.Term" "term"

undefinedsSig' :: TypedExpr (QSSig -> QSSig)
undefinedsSig' = qsQual "Test.QuickSpec.Signature" "undefinedsSig"

generate' :: TypedExpr (Bool
                     -> Strategy
                     -> QSSig
                     -> IO (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr)))
generate' = qsQual "Test.QuickSpec.Generate" "generate"

partialGen' :: TypedExpr (Test.QuickSpec.Term.PGen a -> Test.QuickCheck.Gen.Gen a)
partialGen' = qsQual "Test.QuickSpec.Term" "partialGen"

classes' :: TypedExpr (Test.QuickSpec.TestTree.TestResults a -> [[a]])
classes' = qsQual "Test.QuickSpec.TestTree" "classes"

tmToList' :: TypedExpr (Test.QuickSpec.Utils.TypeMap.TypeMap f -> [Test.QuickSpec.Utils.Typed.Some f])
tmToList' = qsQual "Test.QuickSpec.Utils.TypeMap" "toList"

some2' :: TypedExpr ((f (g a) -> b) -> Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O f g) -> b)
some2' = qsQual "Test.QuickSpec.Utils.Typed" "some2"

initial' :: TypedExpr (Int
                  -> [Test.QuickSpec.Term.Symbol]
                  -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
                  -> Ctx)
initial' = qsQual "Test.QuickSpec.Reasoning.NaiveEquationalReasoning" $
               "initial"

maxDepth' :: TypedExpr (QSSig -> Int)
maxDepth' = qsQual "Test.QuickSpec.Signature" "maxDepth"

symbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
symbols' = qsQual "Test.QuickSpec.Signature" "symbols"

isUndefined' = qsQual "Test.QuickSpec.Term" "isUndefined"

erase' :: TypedExpr (Test.QuickSpec.Utils.Typed.Tagged a -> a)
erase' = qsQual "Test.QuickSpec.Utils.Typed" "erase"

prune' = qsQual "Test.QuickSpec.Main" "prune"

showEquation' :: TypedExpr (Test.QuickSpec.Signature.Sig -> Test.QuickSpec.Equation.Equation -> String)
showEquation' = qsQual "Test.QuickSpec.Equation" "showEquation"

-- Prefix constructor names with `con`

conSome' = qsQual "Test.QuickSpec.Utils.Typed" "Some"

conO' = qsQual "Test.QuickSpec.Utils.Typed" "O"

-- Pruning algorithm adapted from Test.QuickSpec.quickSpec

{-
quickSpec :: Signature a => a -> IO ()
quickSpec sig = do
  r <- generate False (const partialGen) sig
  let clss   = concatMap (some2 (map (Some . O) . classes)) (TypeMap.toList r)
      univ   = concatMap (some2 (map (tagged term))) clss
      reps   = map (some2 (tagged term . head)) clss
      eqs    = equations clss
      ctx    = initial (maxDepth sig) (symbols sig) univ
      allEqs = map (some eraseEquation) eqs
      pruned = prune ctx (filter (not . isUndefined) (map erase reps)) id allEqs

  forM_ pruned (\eq ->
      printf "%s\n" (showEquation sig eq))
-}

genOf' :: Type -> TypedExpr (Test.QuickCheck.Gen.Gen a)
genOf' (Type t) = return' $$$ undef
  where undef = TE . raw $ "undefined :: (" ++ t ++ ")"

getClasses' :: TypedExpr (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr) -> Cls)
getClasses' = compose' cm tmToList'
  where cm  = concatMap' $$$ (some2' $$$ cls)
        cls = compose' mp classes'
        mp  = map' $$$ (compose' conSome' conO')

doCtx' s = (fmap' $$$ (getCtxSimple' $$$ render s)) $$$ doUniv' s

getCtxSimple' :: TypedExpr (QSSig -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term] -> Ctx)
getCtxSimple' = tlam "sig" body
  where body = (initial' $$$ depth) $$$ syms
        sig :: TypedExpr QSSig
        sig = "sig"
        depth = maxDepth' $$$ sig
        syms  = symbols' $$$ sig

addUndefineds :: TypedExpr (QSSig -> QSSig)
addUndefineds = tlam "sig" body
  where body = mappend' sig (undefinedsSig' $$$ sig)
        sig  = signature' $$$ "sig"

getPruned' :: TypedExpr ((Ctx, Reps) -> Eqs -> Eqs)
getPruned' = tlam "(ctx,reps)" body
  where reps' = "reps" :: TypedExpr Reps
        ctx'  = "ctx"  :: TypedExpr Ctx
        body  = (((prune' $$$ ctx') $$$ reps) $$$ id')
        reps  = (filter' $$$ pred) $$$ er
        pred :: TypedExpr (Test.QuickSpec.Term.Term -> Bool)
        pred = compose' not' isUndefined'
        er   = (map' $$$ erase') $$$ reps'

--prune :: [Equation] -> IO (Maybe [Equation])
prune eqs = tlam "sig" body $$$ render sig
  where body   = (getPruned' $<$>$ ctxRep) $<*>$ (return' $$$ eqs')
        sig    = sigFromEqs eqs
        eqs'   = renderEqs eqs
        ctxRep = getCtxRep sig

parseEqs = undefined

doReps' :: Sig -> TypedExpr (IO Reps)
doReps' s = (fmap' $$$ getReps') $$$ doClasses' s

getReps' :: TypedExpr ([Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O f g)]
                    -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term])
getReps' = (map' $$$ f)
  where f = some2' $$$ (compose' t "head")
        t = tagged' $$$ term'

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

doGenerate' :: Sig -> TypedExpr (IO (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr)))
doGenerate' s = getGenerate' $$$ render s

-- We do a type-breaking wrap/unwrap here to use our `Strategy` type in place of
-- QuickSpec's, which is problematic to wrap up in a `TypedExpr`
getGenerate' :: TypedExpr (QSSig -> IO (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr)))
getGenerate' = (generate' $$$ "False") $$$ (TE strat)
  where TE strat = (const' $$$ partialGen')

doClasses' :: Sig -> TypedExpr (IO Cls)
doClasses' s = (fmap' $$$ getClasses') $$$ doGenerate' s

doUniv' s = (fmap' $$$ getUniv') $$$ doClasses' s

getUniv' = "concatMap" $$$ f
  where f = some2' $$$ m
        m = map' $$$ t
        t = tagged' $$$ term'

getCtxRep :: Sig -> TypedExpr (IO (Ctx, Reps))
getCtxRep s = func $$$ render s
  where func :: TypedExpr (QSSig -> IO (Ctx, Reps))
        func = tlam "sig" funcbody
        funcbody :: TypedExpr (IO (Ctx, Reps))
        funcbody = (fmap' $$$ (compose' f getClasses')) $$$ (getGenerate' $$$ sig')
        f :: TypedExpr (Cls -> (Ctx, Reps))
        f       = tlam "cls" body
        body = ("(,)" $$$ ctx) $$$ rep
        ctx :: TypedExpr Ctx
        ctx     = (getCtxSimple' $$$ sig') $$$ u
        u :: TypedExpr Univ
        u       = getUniv' $$$ cls'
        rep :: TypedExpr Reps
        rep     = getReps' $$$ cls'
        cls' :: TypedExpr Cls
        cls' = "cls"
        sig' :: TypedExpr QSSig
        sig' = "sig"
