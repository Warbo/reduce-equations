{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Internal.Types where

import           Control.Monad
import           Data.Aeson
import           Data.List
import           Data.Stringable
import qualified Data.Text        as T
import           Language.Eval
import           System.IO.Unsafe

-- Types to represent equations, constants, variables, etc. and functions for
-- converting between representations

data Equation = Eq Term Term deriving (Eq)

instance ToJSON Equation where
  toJSON (Eq l r) = object [
                        "relation" .= toJSON ("~=" :: String),
                        "lhs"      .= toJSON l,
                        "rhs"      .= toJSON r
                      ]

instance FromJSON Equation where
  parseJSON (Object v) = Eq <$> v .: "lhs" <*> v .: "rhs"
  parseJSON _          = mzero

instance Show Equation where
  show = toString . encode . toJSON

data Term = App Term Term | C Const | V Var deriving (Show, Eq)

instance ToJSON Term where
  toJSON t = case t of
    C c     -> toJSON c
    V v     -> toJSON v
    App l r -> object ["role" .= ("application" :: String),
                       "lhs"  .= toJSON l,
                       "rhs"  .= toJSON r]

instance FromJSON Term where
  parseJSON (Object v) = do
    role <- v .: "role"
    case (role :: String) of
         "variable"    -> V <$> parseJSON (Object v)
         "constant"    -> C <$> parseJSON (Object v)
         "application" -> App <$> v .: "lhs" <*> v .: "rhs"
  parseJSON _          = mzero

data Sig = Sig [Const] [Var] deriving (Show)

instance Eq Sig where
  (Sig cs1 vs1) == (Sig cs2 vs2) = all (`elem` cs1) cs2 &&
                                   all (`elem` cs2) cs1 &&
                                   all (`elem` vs1) vs2 &&
                                   all (`elem` vs2) vs1

data Var = Var Type Int Arity deriving (Show, Eq)

instance ToJSON Var where
  toJSON (Var t i a) = object ["role"  .= ("variable" :: String),
                               "type"  .= toJSON t,
                               "id"    .= toJSON i,
                               "arity" .= toJSON a]

instance FromJSON Var where
  parseJSON (Object v) = do
    t <- v .: "type"
    i <- v .: "id"
    return (Var (Type t) i (Arity (countArity t)))
  parseJSON _          = mzero

countArity t = doCount t "->"

doCount haystack needle = T.count (T.pack needle) (T.pack haystack)

data Const = Const Arity Name Type deriving (Show, Eq)

instance ToJSON Const where
  toJSON (Const a n t) = object ["role"   .= ("constant" :: String),
                                 "symbol" .= toJSON n,
                                 "type"   .= toJSON t,
                                 "arity"  .= toJSON a]

instance FromJSON Const where
  parseJSON (Object v) = do
    t <- v .: "type"
    s <- v .: "symbol"
    return (Const (Arity (countArity t)) s (Type t))
  parseJSON _          = mzero

data Type = Type String deriving (Show, Eq)

instance ToJSON Type where
  toJSON (Type s) = toJSON s

data Name = Name String deriving (Show, Eq)

instance ToJSON Name where
  toJSON (Name n) = toJSON n

instance FromJSON Name where
  parseJSON (String s) = return (Name (toString s))
  parseJSON _          = mzero

data Arity = Arity Int deriving (Show, Eq)

instance ToJSON Arity where
  toJSON (Arity a) = toJSON a

instance FromJSON Arity where
  parseJSON (Number n) = Arity <$> parseJSON (Number n)
  parseJSON _          = mzero

instance Num Arity where
  fromInteger = Arity . fromInteger
  (Arity a) + (Arity b) = Arity (a + b)
  (Arity a) - (Arity b) = Arity (a - b)
  (Arity a) * (Arity b) = Arity (a * b)
  negate (Arity a) = Arity (negate a)
  abs (Arity a) = Arity (abs a)
  signum (Arity a) = Arity (signum a)

instance Ord Arity where
  Arity a <= Arity b = a <= b

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

termType :: Term -> Maybe Type
termType (C c)     = Just (constType c)
termType (V v)     = Just (varType   v)
termType (App l r) = do
  Type lType <- termType l
  Type rType <- termType r
  let left  = "typeRep ([] :: [" ++ lType ++ "])"
      right = "typeRep ([] :: [" ++ rType ++ "])"
      expr' = withMods ["Data.Typeable"] . raw $
                "funResultTy (" ++ left ++ ") (" ++ right ++ ")"
      expr  = expr' {
        eExpr = concat ["case (" ++ eExpr expr' ++ ") of {",

                        " Nothing -> error \"Incompatible types '",
                        lType, "' '", rType, "'\";",

                        " Just t -> show t;",

                        "}"]
      }
  result <- unsafePerformIO (eval expr)
  return (Type result)

termType' :: Term -> Type
termType' t = let Just x = termType t in x

-- JSON conversion

sigFrom :: [Object] -> Sig
sigFrom xs = withConsts (constsFrom xs) . withVars (varsFrom xs) $ emptySig

constsFrom :: [Object] -> [Const]
constsFrom _ = []

varsFrom :: [Object] -> [Var]
varsFrom _ = []

termArity :: Term -> Arity
termArity (C c)     = constArity c
termArity (V v)     = varArity v
termArity (App l r) = termArity l - 1
