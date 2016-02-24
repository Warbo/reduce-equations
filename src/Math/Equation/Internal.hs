{-# LANGUAGE OverloadedStrings #-}
module Math.Equation.Internal where

import Language.Eval
import Data.Aeson
import Data.List

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

data Var = Var deriving (Show, Eq)

data Const = Const Arity Name Type deriving (Show, Eq)

data Type = Type String deriving (Show, Eq)

data Name = Name String deriving (Show, Eq)

data Arity = Arity Int deriving (Show, Eq)

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

render :: Sig -> Expr
render (Sig cs vs) = mappend' (renderConsts cs) (renderVars vs)

empty' = withPkgs ["quickspec"] . qualified "Test.QuickSpec.Signature" $ "emptySig"

mappend' x y = ("mappend" $$ x) $$ y

renderConsts :: [Const] -> Expr
renderConsts []     = empty'
renderConsts (c:cs) = mappend' (renderConst c) (renderConsts cs)

renderConst :: Const -> Expr
renderConst c = (f $$ asString n) $$ v
  where f = withPkgs ["quickspec"] . qualified "Test.QuickSpec.Signature"
                                   . raw $ "fun" ++ show a
        v = raw $ "undefined :: (" ++ t ++ ")"
        Arity a = constArity c
        Name  n = constName  c
        Type  t = constType c

renderVars :: [Var] -> Expr
renderVars vs = empty'
