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

withType :: TypedExpr a -> String -> TypedExpr b
withType (TE x) t = TE (x { eExpr = "((" ++ eExpr x ++ ") :: (" ++ t ++ "))" })

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

(>>$) :: TypedExpr (IO a) -> TypedExpr (IO b) -> TypedExpr (IO b)
a >>$ b = ("(>>)" $$$ a) $$$ b

($>>$) :: TypedExpr a -> TypedExpr (IO b) -> TypedExpr (IO b)
a $>>$ b = (return' $$$ a) >>$ b

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

type Cls = [Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O [] Test.QuickSpec.Term.Expr)]

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

conSome' :: TypedExpr (f a -> Test.QuickSpec.Utils.Typed.Some f)
conSome' = qsQual "Test.QuickSpec.Utils.Typed" "Some"

conO' :: TypedExpr (f (g a) -> Test.QuickSpec.Utils.Typed.O f g a)
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

{-
getClasses' :: TypedExpr (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr) -> Cls)
getClasses' = compose' cm tmToList'
  where cm  = concatMap' $$$ (some2' $$$ cls)
        cls = compose' mp classes'
        mp  = map' $$$ (compose' conSome' conO')
-}

classesFromEqs :: [Equation] -> [[Term]]
classesFromEqs = combine [] . map nub . addAllToClasses []

addAllToClasses cs    []  = cs
addAllToClasses cs (e:es) = addAllToClasses (addToClasses cs e) es

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
  where classesWith t   = filter (t `elem`) (acc ++ cs)
        overlaps []     = []
        overlaps (t:ts) = classesWith t ++ overlaps ts
        without xs      = filter (`notElem` xs) (acc ++ cs)

getClasses' :: [Equation] -> TypedExpr Cls
getClasses' eqs = mkClasses classes
  where classes = classesFromEqs eqs

unSomeClasses :: [Equation] -> [TypedExpr [Test.QuickSpec.Term.Expr a]]
unSomeClasses eqs = map mkUnSomeClass (classesFromEqs eqs)

mkUnSomeClass :: [Term] -> TypedExpr [Test.QuickSpec.Term.Expr a]
mkUnSomeClass []     = nil'
mkUnSomeClass (x:xs) = (cons' $$$ termToExpr x) $$$ mkUnSomeClass xs

unSomePrune :: TypedExpr QSSig -> [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Equation.Equation]
unSomePrune sig clss = (((prune' $$$ arg1) $$$ arg2) $$$ id') $$$ arg3
  where arg1 = ((initial' $$$ (maxDepth' $$$ sig)) $$$ (symbols' $$$ sig)) $$$ (mkUniv2 clss)
        arg2 = (filter' $$$ (compose' not' isUndefined')) $$$ getTermHead clss
        arg3 = sort' $$$ (mkEqs2 clss)

mkUniv2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2 []     = nil'
mkUniv2 (x:cs) = (append' $$$ ((map' $$$ univ2) $$$ x)) $$$ (mkUniv2 cs)

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
getTermHead []     = nil'
getTermHead (c:cs) = (cons' $$$ (term' $$$ (head' $$$ c))) $$$ getTermHead cs

mkEqs2 :: [TypedExpr [Test.QuickSpec.Term.Expr a]] -> TypedExpr [Test.QuickSpec.Equation.Equation]
mkEqs2 []     = nil'
mkEqs2 (c:cs) = (append' $$$ (f $$$ c)) $$$ (mkEqs2 cs)
  where f = tlam "(z:zs)" "[term y :=: term z | y <- zs]"

sort' :: Ord a => TypedExpr ([a] -> [a])
sort' = TE $ qualified "Data.List" "sort"

mkClasses :: [[Term]] -> TypedExpr Cls
mkClasses [] = nil'
mkClasses (c:cs) = (cons' $$$ mkClass c) $$$ mkClasses cs
--mkClasses (c:cs) = (append' $$$ mkClass c) $$$ mkClasses cs

mkClass :: [Term] -> TypedExpr (Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O [] Test.QuickSpec.Term.Expr))
mkClass ts = conSome' $$$ (conO' $$$ l ts)
  where l    []  = nil'
        l (x:xs) = (cons' $$$ termToExpr x) $$$ l xs

termToExpr :: Term -> TypedExpr (Test.QuickSpec.Term.Expr a)
termToExpr t = ((expr' $$$ term) $$$ arity) $$$ eval
  where term  = renderTerm t

        arity :: TypedExpr Int
        arity = TE (raw (show (let Arity a = termArity t in a)))

        -- Used for variable instantiation (which we avoid) and specifying type
        eval  = "undefined" `withType` ("Valuation -> (" ++ typ ++ ")")

        typ   = case termType t of
                     Nothing -> error ("Couldn't get type of " ++ show t)
                     Just (Type x) -> x

        expr' :: TypedExpr (_ -> Int -> _ -> Test.QuickSpec.Term.Expr _)
        expr' = "Expr"


append' :: TypedExpr ([a] -> [a] -> [a])
append' = "(++)"

doCtx' :: [Equation] -> Sig -> TypedExpr Ctx
doCtx' eqs s = (getCtxSimple' $$$ render s) $$$ doUniv' eqs s

getCtxSimple' :: TypedExpr (QSSig -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term] -> Ctx)
getCtxSimple' = tlam "sig" body
  where body = (initial' $$$ depth) $$$ syms
        sig = "sig" :: TypedExpr QSSig
        depth = maxDepth' $$$ sig
        syms  = symbols' $$$ sig

addUndefineds :: TypedExpr (QSSig -> QSSig)
addUndefineds = tlam "sig" body
  where body = mappend' sig (undefinedsSig' $$$ sig)
        sig  = signature' $$$ sig'
        sig' = "sig" :: TypedExpr QSSig

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
  where body    = (getPruned' $$$ ctxRep) $$$ eqs'
        sig     = sigFromEqs eqs
        eqs'    = renderEqs eqs
        ctxRep  = getCtxRep eqs sig
        classes = classesFromEqs eqs

parseEqs = undefined

getReps' :: TypedExpr ([Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O [] Test.QuickSpec.Term.Expr)]
                    -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term])
getReps' = (map' $$$ f)
  where f = some2' $$$ (compose' t head')
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
getGenerate' = (generate' $$$ false') $$$ (TE strat)
  where TE strat = (const' $$$ partialGen')

        false' :: TypedExpr Bool
        false' = "False"

doUniv' :: [Equation] -> Sig -> TypedExpr [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
doUniv' eqs s = getUniv' $$$ getClasses' eqs

getUniv' = concatMap' $$$ f
  where f = some2' $$$ m
        m = map' $$$ t
        t = tagged' $$$ term'

getCtxRep :: [Equation] -> Sig -> TypedExpr (Ctx, Reps)
getCtxRep eqs s = func $$$ render s
  where func :: TypedExpr (QSSig -> (Ctx, Reps))
        func = tlam "sig" funcbody

        funcbody :: TypedExpr (Ctx, Reps)
        funcbody = f $$$ getClasses' eqs

        f :: TypedExpr (Cls -> (Ctx, Reps))
        f = tlam "cls" body

        body :: TypedExpr (Ctx, Reps)
        body = (pair' $$$ ctx) $$$ rep

        ctx :: TypedExpr Ctx
        ctx = (getCtxSimple' $$$ sig') $$$ u

        u :: TypedExpr Univ
        u = getUniv' $$$ cls'

        rep :: TypedExpr Reps
        rep = getReps' $$$ cls'

        cls' :: TypedExpr Cls
        cls' = "cls"

        sig' :: TypedExpr QSSig
        sig' = "sig"

pair' :: TypedExpr (a -> b -> (a, b))
pair' = "(,)"

unType :: TypedExpr a -> TypedExpr b
unType (TE e) = TE e

withMods' :: [Mod] -> TypedExpr a -> TypedExpr a
withMods' ms (TE e) = TE (withMods ms (withQS e))
