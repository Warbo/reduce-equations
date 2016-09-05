{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Internal.Types where

import           Control.Monad
import           Data.Aeson
import           Data.List
import           Data.Maybe
import           Data.Stringable
import qualified Data.Text        as T
import           Language.Eval
import           System.IO.Unsafe
import           System.Environment
import           Text.Read  (readMaybe) -- Uses String as part of base, not Text

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

data Term = App Term Term (Maybe Type) | C Const | V Var

instance Eq Term where
  (C c1)        == (C c2)        = c1 == c2
  (V v1)        == (V v2)        = v1 == v2
  (App l1 r1 _) == (App l2 r2 _) = l1 == l2 && r1 == r2
  _             == _             = False

instance Show Term where
  show (C c)       = "C (" ++ show c ++ ")"
  show (V v)       = "V (" ++ show v ++ ")"
  show (App l r _) = "App (" ++ show l ++ ") (" ++ show r ++ ")"

instance ToJSON Term where
  toJSON t = case t of
    C c       -> toJSON c
    V v       -> toJSON v
    App l r _ -> object ["role" .= ("application" :: String),
                         "lhs"  .= toJSON l,
                         "rhs"  .= toJSON r]

instance FromJSON Term where
  parseJSON (Object v) = do
    role <- v .: "role"
    case (role :: String) of
         "variable"    -> V <$> parseJSON (Object v)
         "constant"    -> C <$> parseJSON (Object v)
         "application" -> app <$> v .: "lhs" <*> v .: "rhs"
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
    return (Var t i (Arity (countArity t)))
  parseJSON _          = mzero

countArity (FunType i o) = 1 + countArity o
countArity (RawType t)   = doCount t "->"

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
    return (Const (Arity (countArity t)) s t)
  parseJSON _          = mzero

data Type = RawType String | FunType Type Type deriving (Show, Eq)

instance ToJSON Type where
  toJSON (RawType s)   = object ["role" .= ("rawtype" :: String),
                                 "type" .= toJSON s]
  toJSON (FunType i o) = object ["role" .= ("functiontype" :: String),
                                 "lhs"  .= toJSON i,
                                 "rhs"  .= toJSON o]

instance FromJSON Type where
  parseJSON (String s) = RawType <$> parseJSON (String s)
  parseJSON (Object v) = do
    role <- v .: "role"
    if role == ("rawtype" :: String)
       then RawType <$> v .: "type"
       else FunType <$> v .: "lhs" <*> v .: "rhs"
  parseJSON _          = mzero

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
  App lhs rhs _ -> termConsts lhs ++ termConsts rhs
  C c           -> [c]
  V v           -> []

termVars :: Term -> [Var]
termVars t = nub $ case t of
  App lhs rhs _ -> termVars lhs ++ termVars rhs
  C c           -> []
  V v           -> [v]

sigConsts :: Sig -> [Const]
sigConsts (Sig cs vs) = cs

sigVars :: Sig -> [Var]
sigVars (Sig cs vs) = vs

varName :: Var -> Name
varName (Var t i a) = Name ("(var, " ++ typeName t ++ ", " ++ show i ++ ")")

typeName (RawType t) = t
typeName (FunType i o) = "(" ++ typeName i ++ ") -> (" ++ typeName o ++ ")"

varArity (Var t i a) = a

varType (Var t i a) = t

constName :: Const -> Name
constName (Const a n t) = n

constArity :: Const -> Arity
constArity (Const a n t) = a

constType :: Const -> Type
constType (Const a n t) = t

termType :: Term -> Maybe Type
termType (C c)       = Just (constType c)
termType (V v)       = Just (varType   v)
termType (App l r t) = t

app l r = App l r (getTermType l r)

getTermType :: Term -> Term -> Maybe Type
getTermType l r = do
  lType <- termType l
  case lType of
       FunType _ o                          -> return o
       RawType t | not ("->" `isInfixOf` t) -> Nothing
       RawType _                            -> do
         rType <- termType r
         let left  = "typeRep ([] :: [" ++ typeName lType ++ "])"
             right = "typeRep ([] :: [" ++ typeName rType ++ "])"
             expr' = withMods ["Data.Typeable"] . raw $
                       "funResultTy (" ++ left ++ ") (" ++ right ++ ")"
             expr  = expr' {
               eExpr = concat ["case (" ++ eExpr expr' ++ ") of {",

                               " Nothing -> error \"Incompatible types '",
                               typeName lType, "' '", typeName rType, "'\";",

                               " Just t -> show t;",

                               "}"]
             }
         result <- unsafePerformIO $ do
           extraImports <- lookupEnv "NIX_EVAL_EXTRA_IMPORTS"
           eval (augment extraImports expr)
         return (RawType result)
  where modsOf x = do
          ms <- x >>= readMaybe
          return (map (\(p,m) -> (Pkg p, Mod m)) ms)
        augment given expr = let pms = fromMaybe [] (modsOf given)
                                 ps  = map fst pms
                                 ms  = map snd pms
                              in withPkgs ps (withMods ms expr)

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
termArity (C c)       = constArity c
termArity (V v)       = varArity v
termArity (App l r _) = termArity l - 1
