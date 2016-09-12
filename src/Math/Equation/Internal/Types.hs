{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Internal.Types where

import           Control.Monad
import           Data.Aeson
import           Data.List
import           Data.Maybe
import           Data.Stringable
import qualified Data.Text        as T
import           Language.Eval
import qualified Language.Haskell.Exts.Parser as HSE.Parser
import qualified Language.Haskell.Exts.Pretty as HSE.Pretty
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
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

hasType (C c)             = True
hasType (V v)             = True
hasType (App l r Nothing) = False
hasType (App l r _)       = hasType l && hasType r

exprsFrom :: Term -> [(Term, Expr)]
exprsFrom t | hasType t = []
exprsFrom (App l r (Just t)) = exprsFrom l ++ exprsFrom r
exprsFrom (App l r Nothing)  = if hasType l && hasType r
                                  then case termType' l of
                                         FunType _ o -> []
                                         RawType _   -> [(App l r Nothing, exprFor (App l r Nothing))]
                                  else exprsFrom l ++ exprsFrom r
  where exprFor (App l r _) = exprForType (termType' l) (termType' r)

runExprs :: [(Term, Expr)] -> IO [(Term, Type)]
runExprs tes = process <$> eval expr
  where expr         = pack' $$ (encode' $$ asList' (map assoc tes))
        assoc (t, e) = ("(,)" $$ asString (encode t)) $$ ("show" $$ e)

        encode'      = withPkgs ["aeson"] . withMods ["Data.Aeson"] $ "encode"
        pack'        = withPkgs ["bytestring"] $ qualified "Data.ByteString.Lazy.Char8" "unpack"

        process ms = fromJust $ do
          s  <- ms
          ss <- decode (fromString s)
          mapM (\(trm, typ) -> do
                   trm' <- decode (fromString trm)
                   return (trm', RawType (read typ)))
               ss

setTypes :: [Equation] -> [(Term, Type)] -> [Equation]
setTypes []           _  = []
setTypes (Eq l r:eqs) db = Eq (setTermTypes l db) (setTermTypes r db) : setTypes eqs db

setTermTypes :: Term -> [(Term, Type)] -> Term
setTermTypes t           db | hasType t = t
setTermTypes (App l r t) db             = case t' of
                                            Nothing  -> App l' r' t
                                            Just t'' -> App l' r' (Just t'')
  where l' = setTermTypes l db
        r' = setTermTypes r db
        t' = lookup (App l r t) db

setAllTypes :: [Equation] -> [Equation]
setAllTypes = map setForEq
  where setForEq (Eq l r) = Eq (setForTerm l) (setForTerm r)
        setForTerm (C c)              = C c
        setForTerm (V v)              = V v
        setForTerm (App l r (Just t)) = App (setForTerm l) (setForTerm r) (Just t)
        setForTerm (App l r Nothing)  =
          let l' = setForTerm l
              r' = setForTerm r
           in case termType' l' of
                FunType _ o -> App l' r' (Just o)
                RawType t   -> case HSE.Parser.parseType t of
                  HSE.Parser.ParseOk (HSE.Syntax.TyFun _ o) -> App l' r' (Just (RawType (HSE.Pretty.prettyPrint o)))
                  HSE.Parser.ParseOk x           -> error ("Expected function type, got " ++ show x)
                  HSE.Parser.ParseFailed _ e     -> error ("Parsing type failed: " ++ e)

setEqTypes :: [Equation] -> IO [Equation]
setEqTypes eqs = if null exprs
                    then return eqs
                    else do
                      types <- runExprs exprs
                      setEqTypes (setTypes eqs types)
  where terms = concatMap (\(Eq l r) -> [l, r]) eqs
        exprs = concatMap exprsFrom terms

asList' :: [Expr] -> Expr
asList' []     = "[]"
asList' (e:es) = ("(:)" $$ e) $$ asList' es

augment = withPkgs ps . withMods ms
  where ps            = map (Pkg . fst) extraImports
        ms            = map (Mod . snd) extraImports
        extraImports  = fromMaybe [] (given >>= readMaybe)
        given         = unsafePerformIO (lookupEnv "NIX_EVAL_EXTRA_IMPORTS")

exprForType :: Type -> Type -> Expr
exprForType lType rType = augment expr
  where expr'    = withMods ["Data.Typeable"] $
                     ("funResultTy" $$ getRep left) $$ getRep right
        expr     = case' expr' [
                     ("Nothing", "error" $$ asString msg),
                     ("Just t",  "show t")]
        left     = typeName lType
        right    = typeName rType
        getRep t = raw $ "typeRep ([] :: [" ++ t ++ "])"
        msg      = "'" ++ left ++ "' '" ++ right ++ "'"

case' :: Expr -> [(Expr, Expr)] -> Expr
case' x ps = mod $ x {
               eExpr = "case (" ++ eExpr x ++ ") of {" ++
                         intercalate "; " clauses ++ "}"
             }
  where clauses = map mkClause ps
        mkClause (pat, val) = eExpr pat ++ " -> " ++ eExpr val
        mod  = withMods mods . withPkgs pkgs
        mods = concatMap (\(pat, val) -> eMods pat ++ eMods val) ps
        pkgs = concatMap (\(pat, val) -> ePkgs pat ++ ePkgs val) ps

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


addTypes :: [Equation] -> IO [Equation]
addTypes = undefined
