module Math.Equation.Internal.Types where

import Data.Aeson
import Data.List

-- Types to represent equations, constants, variables, etc. and functions for
-- converting between representations

data Equation = Eq Term Term deriving (Eq, Show)

data Term = App Term Term | C Const | V Var deriving (Show, Eq)

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

-- Sig construction

emptySig :: Sig
emptySig = Sig [] []

instance Monoid Sig where
  mempty = emptySig
  mappend (Sig cs1 vs1) (Sig cs2 vs2) = Sig (nub (cs1 ++ cs2)) (nub (vs1 ++ vs2))

withConsts :: [Const] -> Sig -> Sig
withConsts cs (Sig cs' vs') = Sig (cs ++ cs') vs'

withVars :: [Var] -> Sig -> Sig
withVars vs (Sig cs' vs') = Sig cs' (vs ++ vs')

sigFromEqs :: [Equation] -> Sig
sigFromEqs = foldr (mappend . sigFromEq) emptySig

sigFromEq :: Equation -> Sig
sigFromEq e = withVars   (eqVars   e) .
              withConsts (eqConsts e) $ emptySig

-- Accessors

eqVars :: Equation -> [Var]
eqVars (Eq lhs rhs) = nub (termVars lhs ++ termVars rhs)

eqConsts :: Equation -> [Const]
eqConsts (Eq lhs rhs) = nub (termConsts lhs ++ termConsts rhs)

termConsts :: Term -> [Const]
termConsts t = nub $ case t of
  App lhs rhs -> termConsts lhs ++ termConsts rhs
  C c         -> [c]
  V v         -> []

termVars :: Term -> [Var]
termVars t = nub $ case t of
  App lhs rhs -> termVars lhs ++ termVars rhs
  C c         -> []
  V v         -> [v]

sigConsts :: Sig -> [Const]
sigConsts (Sig cs vs) = cs

sigVars :: Sig -> [Var]
sigVars (Sig cs vs) = vs

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

-- JSON conversion

sigFrom :: [Object] -> Sig
sigFrom xs = withConsts (constsFrom xs) . withVars (varsFrom xs) $ emptySig

constsFrom :: [Object] -> [Const]
constsFrom _ = []

varsFrom :: [Object] -> [Var]
varsFrom _ = []
