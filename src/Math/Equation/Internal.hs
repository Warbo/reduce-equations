{-# LANGUAGE OverloadedStrings, RankNTypes, ExistentialQuantification, PartialTypeSignatures #-}
module Math.Equation.Internal where

import Language.Eval.Internal
import Data.Aeson
import Data.List
import Data.String

-- Used for their types
import qualified Test.QuickCheck.Gen
import qualified Test.QuickSpec
import qualified Test.QuickSpec.Signature
import qualified Test.QuickSpec.Term
import qualified Test.QuickSpec.TestTree
import qualified Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning

-- We want to use QuickSpec's `prune` function to minimise a set of equations,
-- but this is tricky since it uses a `Context` which contains `TypeRep`s, which
-- can't be de-serialised easily

-- To work around this, we don't attempt to return a `TypeRep`, e.g. from a
-- function like `String -> TypeRep`; instead, we build a continuation which
-- will perform the minimisation, given the appropriate `TypeRep`s, and execute
-- that in a sub-process using `nix-eval`

data Sig = Sig [Const] [Var] deriving (Show)

instance Eq Sig where
  (Sig cs1 vs1) == (Sig cs2 vs2) = all (`elem` cs1) cs2 &&
                                   all (`elem` cs2) cs1 &&
                                   all (`elem` vs1) vs2 &&
                                   all (`elem` vs2) vs1

data Var = Var Type Int Arity deriving (Show, Eq)

data Const = Const Arity Name Type deriving (Show, Eq)

data Type = Type String deriving (Show, Eq)

data Name = Name String deriving (Show, Eq)

data Arity = Arity Int deriving (Show, Eq)

varName :: Var -> Name
varName (Var (Type t) i a) = Name ("(var, " ++ t ++ ", " ++ show i ++ ")")

varArity (Var t i a) = a

varType (Var t i a) = t

constName :: Const -> Name
constName (Const a n t) = n

constArity :: Const -> Arity
constArity (Const a n t) = a

constType :: Const -> Type
constType (Const a n t) = t

sigFrom :: [Object] -> Sig
sigFrom xs = withConsts (constsFrom xs) . withVars (varsFrom xs) $ emptySig

emptySig :: Sig
emptySig = Sig [] []

withConsts :: [Const] -> Sig -> Sig
withConsts cs (Sig cs' vs') = Sig (cs ++ cs') vs'

withVars :: [Var] -> Sig -> Sig
withVars vs (Sig cs' vs') = Sig cs' (vs ++ vs')

constsFrom :: [Object] -> [Const]
constsFrom _ = []

varsFrom :: [Object] -> [Var]
varsFrom _ = []

type QSSig = Test.QuickSpec.Signature.Sig

render :: Sig -> TypedExpr QSSig
render (Sig cs vs) = mappend' (renderConsts cs) (renderVars vs)

empty' :: TypedExpr QSSig
empty' = TE . withQS . qualified "Test.QuickSpec.Signature" $ "emptySig"

mappend' :: TypedExpr a -> TypedExpr a -> TypedExpr a
mappend' x y = (TE "mappend" $$$ x) $$$ y

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

renderVars :: [Var] -> TypedExpr QSSig
renderVars []     = empty'
renderVars (v:vs) = mappend' (renderVar v) (renderVars vs)

renderVar :: Var -> TypedExpr QSSig
renderVar v = (gv $$$ nameL) $$$ gen'
  where gv = gvars' (varArity v)
        Type  t = varType  v
        Name  n = varName  v
        gen' :: TypedExpr (Test.QuickCheck.Gen.Gen a)
        gen'    = return' $$$ undef
        undef   = TE . raw $ "undefined :: (" ++ t ++ ")"
        nameL :: TypedExpr [String]
        nameL = singleton' name
        name :: TypedExpr String
        name = TE (asString n)

withQS = withPkgs ["quickspec"] . withMods ["Test.QuickSpec",
                                            "Test.QuickSpec.Signature",
                                            "Test.QuickSpec.Term"]

gvars' :: Arity -> TypedExpr ([String] -> a -> QSSig)
gvars' (Arity a) = TE . withQS . raw $ "Test.QuickSpec.Signature.gvars" ++ show a

singleton' :: TypedExpr a -> TypedExpr [a]
singleton' x = return' $$$ x

addUndefineds :: TypedExpr (QSSig -> QSSig)
addUndefineds = tlam "sig" body
  where body = ("mappend" $$$ sig) $$$ (undefinedsSig' $$$ sig)
        sig  = signature' $$$ "sig"

signature' :: TypedExpr (a -> QSSig)
signature' = TE . withQS . qualified "Test.QuickSpec.Signature" $ "signature"

compose' f g = (dot $$$ f) $$$ g
  where dot :: TypedExpr ((b -> c) -> (a -> b) -> a -> c)
        dot = "(.)"

lambda :: [String] -> Expr -> Expr
lambda args body = body {
    eExpr = func
  }
  where func = "(\\" ++ argString ++ " -> (" ++ eExpr body ++ "))"
        argString = intercalate " " (map (\a -> "(" ++ a ++ ")") args)

-- TODO: Get all packages, mods, flags, etc.
do' ss = "do {" ++ intercalate ";" (map eExpr ss) ++ "}"

-- Adapted from Test.QuickSpec.quickSpec

undefinedsSig' :: TypedExpr (QSSig -> QSSig)
undefinedsSig' = TE . withQS . qualified "Test.QuickSpec.Signature" $ "undefinedsSig"

doGenerate' :: Sig -> TypedExpr (IO (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr)))
doGenerate' s = getGenerate' $$$ render s

getGenerate' :: TypedExpr (QSSig -> IO (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr)))
getGenerate' = (generate' $$$ "False") $$$ ("const" $$$ partialGen')

doClasses' :: Sig -> TypedExpr (IO Cls)
doClasses' s = (fmap' $$$ getClasses') $$$ doGenerate' s

doUniv' s = (fmap' $$$ getUniv') $$$ doClasses' s

getUniv' = "concatMap" $$$ f
  where f = some2' $$$ m
        m = "map" $$$ t
        t = tagged' $$$ term'

type Ctx = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context

type Reps = [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]

type Cls = [Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O [] Maybe)]

type Univ = [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]

fmap' :: Functor f => TypedExpr ((a -> b) -> f a -> f b)
fmap' = "fmap"

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

tagged' :: TypedExpr ((f a -> b) -> f a -> Test.QuickSpec.Utils.Typed.Tagged b)
tagged' = TE . withQS . qualified "Test.QuickSpec.Utils.Typed" $ "tagged"

term' :: TypedExpr (Test.QuickSpec.Term.Expr a -> Test.QuickSpec.Term.Term)
term' = TE . withQS . qualified "Test.QuickSpec.Term" $ "term"

-- Used in place of Test.QuickSpec.Term.Strategy, which seems to be impredicative
data Strategy where

generate' :: TypedExpr (Bool
                     -> Strategy
                     -> QSSig
                     -> IO (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr)))
generate' = TE . withQS . qualified "Test.QuickSpec.Generate" $ "generate"

partialGen' :: TypedExpr (Test.QuickSpec.Term.PGen a -> Test.QuickCheck.Gen.Gen a)
partialGen' = TE . withQS . qualified "Test.QuickSpec.Term" $ "partialGen"

getClasses' :: TypedExpr (Test.QuickSpec.Utils.TypeMap.TypeMap (Test.QuickSpec.Utils.Typed.O Test.QuickSpec.TestTree.TestResults Test.QuickSpec.Term.Expr) -> Cls)
getClasses' = compose' cm tmToList'
  where cm  = concatMap' $$$ (some2' $$$ cls)
        cls = compose' mp classes'
        mp  = map' $$$ (compose' conSome' conO')

classes' :: TypedExpr (Test.QuickSpec.TestTree.TestResults a -> [[a]])
classes' = TE . withQS . qualified "Test.QuickSpec.TestTree" $ "classes"

tmToList' :: TypedExpr (Test.QuickSpec.Utils.TypeMap.TypeMap f -> [Test.QuickSpec.Utils.Typed.Some f])
tmToList' = TE . withQS . qualified "Test.QuickSpec.Utils.TypeMap" $ "toList"

some2' :: TypedExpr ((f (g a) -> b) -> Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O f g) -> b)
some2' = TE . withQS . qualified "Test.QuickSpec.Utils.Typed" $ "some2"

conSome' = TE . withQS . qualified "Test.QuickSpec.Utils.Typed" $ "Some"

conO' = TE . withQS . qualified "Test.QuickSpec.Utils.Typed" $ "O"

doCtx' s = (fmap' $$$ (getCtxSimple' $$$ render s)) $$$ doUniv' s

getCtxSimple' :: TypedExpr (QSSig -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term] -> Ctx)
getCtxSimple' = tlam "sig" body
  where body = (getCtx' $$$ depth) $$$ syms
        sig :: TypedExpr QSSig
        sig = "sig"
        depth = maxDepth' $$$ sig
        syms  = symbols' $$$ sig

getCtx' :: TypedExpr (Int
                  -> [Test.QuickSpec.Term.Symbol]
                  -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
                  -> Ctx)
getCtx' = TE . withQS . qualified "Test.QuickSpec.Reasoning.NaiveEquationalReasoning" $
               "initial"

maxDepth' :: TypedExpr (QSSig -> Int)
maxDepth' = TE . withQS . qualified "Test.QuickSpec.Signature" $ "maxDepth"

symbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
symbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $ "symbols"

data Eqs where

getPruned' :: TypedExpr ((Ctx, Reps) -> Eqs -> Eqs)
getPruned' = tlam "(ctx,reps)" body
  where body = (((prune' $$$ ctx') $$$ reps) $$$ id')
        reps = (filter' $$$ pred) $$$ er
        pred :: TypedExpr (Test.QuickSpec.Term.Term -> Bool)
        pred = compose' not' isUndefined'
        er   = (map' $$$ erase') $$$ reps'
        reps' :: TypedExpr Reps
        reps' = "reps"
        ctx' :: TypedExpr Ctx
        ctx' = "ctx"

id' :: TypedExpr (a -> a)
id' = "id"

filter' :: TypedExpr ((a -> Bool) -> [a] -> [a])
filter' = "filter"

not' :: TypedExpr (Bool -> Bool)
not' = "not"

isUndefined' = TE . withQS . qualified "Test.QuickSpec.Term" $ "isUndefined"

erase' :: TypedExpr (Test.QuickSpec.Utils.Typed.Tagged a -> a)
erase' = TE . withQS . qualified "Test.QuickSpec.Utils.Typed" $ "erase"

prune' = TE . withQS . qualified "Test.QuickSpec.Main" $ "prune"

doReps' :: Sig -> TypedExpr (IO Reps)
doReps' s = (fmap' $$$ getReps') $$$ doClasses' s

getReps' :: TypedExpr ([Test.QuickSpec.Utils.Typed.Some (Test.QuickSpec.Utils.Typed.O f g)]
                    -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term])
getReps' = (map' $$$ f)
  where f = some2' $$$ (compose' t "head")
        t = tagged' $$$ term'

map' :: TypedExpr ((a -> b) -> [a] -> [b])
map' = "map"

concatMap' :: TypedExpr ((a -> [b]) -> [a] -> [b])
concatMap' = "concatMap"

return' :: Monad m => TypedExpr (a -> m b)
return' = "return"

head' :: TypedExpr ([a] -> a)
head' = "head"

{-
prune :: [Equation] -> IO (Maybe [Equation])
prune eqs = eval' evalAsMain expr
  where expr = lambda ["sig"] body $$ render sig
        body = (getPruned' $$ getCtxRep sig) $$ eqs'
        sig  = sigFrom eqs
        eqs' = renderEqs eqs
-}

evalAsMain :: TypedExpr (IO a) -> IO (Maybe String)
evalAsMain (TE x) = eval' ("main = " ++) x

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

{-
data Equation = Eq Term Term

instance FromJSON Equation where
  parseJSON (Object v) = Eq <$> v .: "lhs" <*> v .: "rhs"
  parseJSON _ = fail "Couldn't parse equation from JSON"

data Term = A Term Term | C Const | V Var

instance FromJSON Term where
  parseJSON (Object v) = do
    role <- v .: "role"
    case role of
      "application" -> A <$> v .: "lhs" <*> v .: "rhs"
      "constant"    -> do arity <- v .: "arity"
                          typ   <- v .: "type"
                          name  <- v .: "name"
                          return (C (Const arity name typ))
      "variable"    -> do typ   <- v .: "type"
                          index <- v .: "index"
                          arity <- v .: "arity"
                          return (V (Var typ index arity))
      _             -> fail ("Unknown term role: " ++ role)
  parseJSON x = fail ("Couldn't parse Term from JSON: " ++ show x)

renderEqs :: [Equation] -> Expr
renderEqs eqs = lambda ["sig"] body
  where body = raw $ "[" ++ intercalate "," (map renderEq eqs) ++ "]"
        renderEq :: Equation -> String
        renderEq (Eq lhs rhs) = let lhs' = "(" ++ renderTerm lhs ++ ")"
                                    rhs' = "(" ++ renderTerm rhs ++ ")"
                                 in "(" ++ lhs' ++ " :=: " ++ rhs' ++ ")"
        renderTerm :: Term -> String
        renderTerm t = case t of
          A lhs rhs -> "(App (" ++ renderTerm lhs ++ ") (" ++ renderTerm rhs ++ "))"
          V v       -> "(Var ("   ++ findSym (varName   v) ++ "))"
          C c       -> "(Const (" ++ findSym (constName c) ++ "))"
        -- Assumes a variable "sig" is in scope; extracts all symbols from "sig"
        -- and returns the one with a name matching "n". Assumes that such a
        -- symbol exists!
        findSym (Name n) = let pred = "(== " ++ show n ++ ") . Test.QuickSpec.Signature.name"
                               syms = "Test.QuickSpec.Signature.symbols sig"
                            in "(head (filter (" ++ pred ++ ") (" ++ syms ++ ")))"
-}

-- Aid the use of eval, by attaching a type to each Expr

data TypedExpr a = TE Expr

($$$) :: TypedExpr (a -> b) -> TypedExpr a -> TypedExpr b
(TE f) $$$ (TE x) = TE (f $$ x)

instance IsString (TypedExpr a) where
  fromString s = TE (fromString s)

instance Show (TypedExpr a) where
  show (TE x) = "TE (" ++ show x ++ ")"

tlam :: String -> TypedExpr b -> TypedExpr (a -> b)
tlam arg (TE f) = TE (lambda [arg] f)
