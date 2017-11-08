{-# LANGUAGE OverloadedStrings, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Algebra.Equation.Internal.Types where

import           Control.Monad
import           Data.Aeson
import           Data.List
import           Data.Maybe
import           Data.Ord (comparing)
import           Data.Stringable hiding (length)
import qualified Data.Text.Lazy          as T
import qualified Data.Text.Lazy.Encoding as TE
import qualified Language.Haskell.Exts.Parser as HSE.Parser
import qualified Language.Haskell.Exts.Pretty as HSE.Pretty
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
import           System.Environment
import qualified Test.QuickSpec.Utils
import           Text.Read  (readMaybe) -- Uses String as part of base, not Text

-- Types to represent equations, constants, variables, etc. and functions for
-- converting between representations

data Equation = Eq Term Term

instance Eq Equation where
  (Eq l1 r1) == (Eq l2 r2) = (l1 == l2 && r1 == r2) ||
                             (l1 == r2 && r1 == l2)

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
  show = T.unpack . TE.decodeUtf8 . encode . toJSON

data Term = App Term Term (Maybe Type) | C Const | V Var

instance Eq Term where
  (C c1)        == (C c2)        = c1 == c2
  (V v1)        == (V v2)        = v1 == v2
  (App l1 r1 _) == (App l2 r2 _) = l1 == l2 && r1 == r2
  _             == _             = False

-- Duplicates the sorting of Test.QuickSpec.Term.Term, but without the type
-- juggling of "Some" and friends
instance Ord Term where
  compare = comparing stamp
    where stamp t = (depth t, size 0 t, -occur t, body t)

          occur t = length (Test.QuickSpec.Utils.usort (vars t []))

          body (V     x)   = Left (Left x)
          body (C     x)   = Left (Right x)
          body (App f x _) = Right (f, x)

          vars (V  x)      = (x:)
          vars (App f x _) = vars f . vars x
          vars (C _)       = id

          size v (App f x _) = size v f + size v x
          size v (V _)       = v
          size v (C _)       = 1

          depth (App f x _) = depth f `max` (1 + depth x)
          depth _           = 1

-- A more sane ordering
termLessThanEq (V v1)        (V v2)        = v1 <= v2
termLessThanEq (C c1)        (C c2)        = c1 <= c2
termLessThanEq (App f1 x1 _) (App f2 x2 _) = f1 < f2 || ((f1 == f2) && x1 <= x2)
termLessThanEq x             y             = num x <= num y
  where num (C   _)     = 0
        num (V   _)     = 1
        num (App _ _ _) = 2

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
  parseJSON (Object v) = v .: "role" >>= \x -> case (x :: String) of
    "variable"    -> V   <$> parseJSON (Object v)
    "constant"    -> C   <$> parseJSON (Object v)
    "application" -> App <$> v .: "lhs" <*> v .: "rhs" <*> return Nothing
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
    return (Var (unwrapParens t) i (Arity (countArity t)))
  parseJSON _          = mzero

instance Ord Var where
  compare = comparing varName

countArity (HSE.Syntax.TyFun _ i o) = 1 + countArity o
countArity _                        = 0

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
    return (Const (Arity (countArity t)) s (unwrapParens t))
  parseJSON _          = mzero

instance Ord Const where
  compare = comparing constName

type Type = HSE.Syntax.Type ()

instance ToJSON Type where
  toJSON = String . fromString . HSE.Pretty.prettyPrint

instance FromJSON Type where
  parseJSON (String s) = case HSE.Parser.parseType (toString s) of
    HSE.Parser.ParseOk t -> return (stripLoc t)
    _                    -> mzero
  parseJSON _          =    mzero

stripLoc :: HSE.Syntax.Type a -> Type
stripLoc = void

data Name = Name String deriving (Show, Eq, Ord)

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

typeName = fixUp . HSE.Pretty.prettyPrint
  where fixUp = collapseSpace . filter (/= '\n')
        collapseSpace (' ':' ':s) = collapseSpace (' ':s)
        collapseSpace       (c:s) = c : collapseSpace s
        collapseSpace          "" = ""

varArity (Var t i a) = a
varIndex (Var t i a) = i
varType  (Var t i a) = t

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

hasType (C c)             = True
hasType (V v)             = True
hasType (App l r Nothing) = False
hasType (App l r _)       = hasType l && hasType r

setAllTypes :: [Equation] -> [Equation]
setAllTypes = map setForEq

setForEq (Eq l r) = Eq (setForTerm l) (setForTerm r)

setForTerm (C c)              = C c
setForTerm (V v)              = V v
setForTerm (App l r (Just t)) = App (setForTerm l) (setForTerm r) (Just t)
setForTerm (App l r Nothing)  =
  let l' = setForTerm l
      r' = setForTerm r
   in case termType' l' of
           HSE.Syntax.TyFun _ _ o -> App l' r' (Just o)
           x                      -> error ("Expected function type, got " ++ show x)

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

unName (Name n) = n

-- Make sure we don't have one name with multiple types or arities
consistent :: [Equation] -> Bool
consistent [] = True
consistent eqs = all haveOnce names
  where db = nub (symTypes [] eqs)

        symTypes acc []          = acc
        symTypes acc (Eq l r:xs) = symTypes (constsOf l ++ constsOf r ++ acc) xs

        constsOf (C (Const a n t)) = [(n, (a, t))]
        constsOf (V _)             = []
        constsOf (App l r _)       = constsOf l ++ constsOf r

        names = map fst db

        haveOnce n = Data.List.length (filter ((== n) . fst) db) == 1

-- Required, since 'parse (prettyPrint t)' might have TyParens which 't' doesn't
unwrapParens (HSE.Syntax.TyFun _ i o) = HSE.Syntax.TyFun ()
                                                         (unwrapParens i)
                                                         (unwrapParens o)
unwrapParens (HSE.Syntax.TyApp _ i o) = HSE.Syntax.TyApp ()
                                                         (unwrapParens i)
                                                         (unwrapParens o)
unwrapParens (HSE.Syntax.TyParen _ t) = unwrapParens t
unwrapParens t                        = t

replaceInType db (HSE.Syntax.TyFun _ i o) = HSE.Syntax.TyFun
                                            ()
                                            (replaceInType db i)
                                            (replaceInType db o)
replaceInType db t                        = fromMaybe
  (error (show t ++ " not in " ++ show db))
  (lookup t db)
