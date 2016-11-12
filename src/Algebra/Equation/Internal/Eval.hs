{-# LANGUAGE OverloadedStrings, PartialTypeSignatures, ScopedTypeVariables, FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}

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

import Data.Dynamic
import Data.List
import Data.Maybe
import qualified Data.Map
import qualified Data.Ord
import Data.String
import Data.Typeable
import qualified Language.Haskell.Exts.Syntax
import qualified Language.Haskell.Exts.Parser as HSE.Parser
import Math.Equation.Internal.Types
import MLSpec.Helper
import System.Environment
import System.IO
import System.IO.Unsafe
import Text.Read  -- Uses String as part of base, not Text

-- Used for their types
import qualified Test.QuickCheck.Gen
import qualified Test.QuickCheck.Random
import qualified Test.QuickSpec
import qualified Test.QuickSpec.Main
import qualified Test.QuickSpec.Signature
import qualified Test.QuickSpec.Term
import qualified Test.QuickSpec.TestTree
import qualified Test.QuickSpec.Utils
import qualified Test.QuickSpec.Utils.Typeable
import qualified Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap
import qualified Test.QuickSpec.Utils.TypeRel (TypeRel, singleton)
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning
import qualified Test.QuickSpec.Equation

-- Conversion from our representations to QuickSpec expressions

renderTermN t sig = case (t, sigToSymN t sig) of
    (App l r _, _  ) -> case (renderTermN l sig, renderTermN r sig) of
                             (f_l, f_r) -> app f_l f_r
    (C c,       f_s) -> const f_s
    (V v,       f_s) -> var   f_s
  where app   = Test.QuickSpec.Term.App
        const = Test.QuickSpec.Term.Const
        var   = Test.QuickSpec.Term.Var

renderN (Sig cs vs) = mappend (renderQSConsts cs) (renderQSVars vs)

renderQSConsts = foldr (mappend . renderQSConst) mempty

renderQSVars   = foldr (mappend . renderQSVarType) mempty . collectTypes
  where collectTypes = groupBy eqTypes . sortBy ordTypes
        eqTypes  (Var t1 _ _) (Var t2 _ _) = t1 == t2
        ordTypes (Var t1 _ _) (Var t2 _ _) = compare t1 t2

renderQSVarType [] = Test.QuickSpec.Signature.emptySig
renderQSVarType vs@(Var t _ (Arity a):_) = case getVal (getRep t) of
  MkHT x -> Test.QuickSpec.Signature.variableSig [
                Test.QuickSpec.Term.Variable
                  (Test.QuickSpec.Term.Atom
                    (Test.QuickSpec.Term.symbol (unName (varName v)) a x)
                    (Test.QuickSpec.Term.pgen (return x)))
              | v <- vs ]
              `mappend` mconcat [ Test.QuickSpec.Signature.totalSig
                                    (Test.QuickSpec.Term.totalGen
                                      (Test.QuickSpec.Term.pgen (return x)))
                                | v <- vs ]
              `mappend` mconcat [ Test.QuickSpec.Signature.partialSig
                                    (Test.QuickSpec.Term.partialGen
                                      (Test.QuickSpec.Term.pgen (return x)))
                                | v <- vs ]
              `mappend` Test.QuickSpec.Signature.typeSig x

extendSig t a sig = case getVal (getRep t) of
  MkHT x -> extendOrd t a (addArrowTypes sig t a) `mappend` Test.QuickSpec.Signature.typeSig x

extendOrd t 0 sig = case getVal (getRep t) of
  MkHT x -> sig `mappend` Test.QuickSpec.Signature.ord x
extendOrd (Language.Haskell.Exts.Syntax.TyFun _ i o) a sig =
  extendSig o (a-1) sig
extendOrd t a sig = error ("Arity " ++ show a ++ " for non-function type " ++ show t)

addArrowTypes sig t 0 = case getVal (getRep t) of
  MkHT x -> sig `mappend` Test.QuickSpec.Signature.typeSig x
addArrowTypes sig (Language.Haskell.Exts.Syntax.TyFun _ i o) a =
  case getVal (getRep i) of
    MkHT x -> Test.QuickSpec.Signature.typeSig x `mappend` addArrowTypes sig o (a-1)

-- Conceptually the same as `fun0`, `fun1`, etc. but we have to bypass those
-- wrappers as we need to supply our own TypeRep
renderQSConst :: Const -> Test.QuickSpec.Signature.Sig
renderQSConst (Const (Arity a) (Name n) t) = extendSig t a constantSig
  where rawTyRep = getRep t

        tyrep = repToQSRep rawTyRep

        typerelsingleton :: Typeable a => Test.QuickSpec.Term.Constant a -> Test.QuickSpec.Utils.TypeRel.TypeRel Test.QuickSpec.Term.Constant
        typerelsingleton x  = typeMapfromList (Test.QuickSpec.Utils.Typed.O [x])

        typeMapfromList :: Typeable a => f a -> Test.QuickSpec.Utils.TypeMap.TypeMap f
        typeMapfromList x = Data.Map.fromList [ (tyrep, Test.QuickSpec.Utils.Typed.Some x) ]

        constantSig = case getVal rawTyRep of
          MkHT x -> Test.QuickSpec.Signature.emptySig {
            Test.QuickSpec.Signature.constants = typerelsingleton
              (Test.QuickSpec.Term.Constant
                (Test.QuickSpec.Term.Atom
                  (Test.QuickSpec.Term.Symbol 0 n a False False tyrep)
                  x))  -- Pruning equations shouldn't force any values
            }

type ListOfConstants = Test.QuickSpec.Utils.Typed.O
  Test.QuickSpec.Utils.Typed.List
  Test.QuickSpec.Term.Constant

repToQSRep tr = (Test.QuickSpec.Utils.Typeable.typeOf [()]) {
                    Test.QuickSpec.Utils.Typeable.unTypeRep = tr
                  }

-- Turn a normalised Type (e.g. `S (S Z) -> S Z`) into a TypeRep
getRep :: Type -> TypeRep
getRep t = case t of
    Language.Haskell.Exts.Syntax.TyFun _ l r -> mkFunTy (getRep l) (getRep r)

    Language.Haskell.Exts.Syntax.TyApp _
      (Language.Haskell.Exts.Syntax.TyCon _
        (Language.Haskell.Exts.Syntax.UnQual _
         (Language.Haskell.Exts.Syntax.Ident _ "S")))
      x -> mkTyConApp sCon [getRep x]

    Language.Haskell.Exts.Syntax.TyCon _
      (Language.Haskell.Exts.Syntax.UnQual _
        (Language.Haskell.Exts.Syntax.Ident _ "Z")) -> typeRep [Z ()]

    _ -> error ("Unknown type '" ++ show t ++ "'. Did you forget replaceTypes?")

  where sCon = typeRepTyCon (typeRep [S (Z ())])  -- The Z gets discarded

-- Construct a value of some normalised type. We use an existential so that
-- getVal can return a (wrapped up) value of the correct type. Since we should
-- only need these values in order to match up their TypeReps, this should be
-- sufficient.
getVal :: TypeRep -> HasType
getVal tr = case () of
    _ | thisCon == zCon   -> MkHT (Z ())
    _ | thisCon == sCon   -> case typeRepArgs tr of
                                  []   -> error ("No args in " ++ show tr)
                                  x:xs -> case getVal x of
                                               MkHT x -> MkHT (S x)
    _ | thisCon == funCon -> case map getVal (typeRepArgs tr) of
                                  [MkHT i, MkHT o] -> MkHT (\x -> case asTypeOf i x of
                                                                       _ -> o)
  where thisCon = typeRepTyCon tr
        funCon  = typeRepTyCon (typeRep [not])  -- Simple monomorphic function
        zCon    = typeRepTyCon (typeRep [Z ()])
        sCon    = typeRepTyCon (typeRep [S (Z ())])  -- The Z gets discarded

data HasType = forall a. (Ord a, Typeable a) => MkHT a

instance Show HasType where
  show (MkHT x) = "HasType(" ++ show (typeRep [x]) ++ ")"

sigToSymN :: Term -> Test.QuickSpec.Signature.Sig -> Test.QuickSpec.Term.Symbol
sigToSymN t sig = case filter pred symbols of
                       []  -> error . show $
                         (("Error",   "No symbol found"),
                          ("term t",  t),
                          ("Name n",  n),
                          ("symbols", symbols),
                          ("sig",     sig))
                       x:_ -> x
  where pred x   = name x == n
        Name n   = case t of
                        C c -> constName c
                        V v -> varName   v
                        App{} -> error ("Tried to get sym for " ++ show t)

        symbols = Test.QuickSpec.Signature.symbols sig
        name    = Test.QuickSpec.Term.name

-- Type synonyms for verbose QuickSpec types

type QSSig = Test.QuickSpec.Signature.Sig

type Ctx = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context

type Eqs = [Test.QuickSpec.Equation.Equation]

-- Pruning algorithm adapted from Test.QuickSpec.quickSpec

checkNames :: [Name] -> [Test.QuickSpec.Term.Symbol] -> Bool
checkNames ns syms = all (isIn syms) (map unName ns)

isIn :: [Test.QuickSpec.Term.Symbol] -> String -> Bool
isIn syms n = any f syms
  where f = (n ==) . Test.QuickSpec.Term.name

classesFromEqs :: [Equation] -> [[Term]]
classesFromEqs eqs = combine [] clss'
  where clss   = foldl addToClasses [] eqs
        clss'  = map nub (foldl extend clss terms)
        terms  = concatMap (\(Eq l r) -> l : r : subTerms l ++ subTerms r) eqs

        subTerms (C _)       = []
        subTerms (V _)       = []
        subTerms (App l r _) = let l' = if termArity l == Arity 0
                                           then [l]
                                           else []
                                   r' = if termArity l == Arity 0
                                           then [l]
                                           else []
                                   ls = if termArity l > Arity 0
                                           then subTerms l
                                           else []
                                   rs = if termArity r > Arity 0
                                           then subTerms r
                                           else []
                                in l' ++ r' ++ ls ++ rs

        extend []     t = [[t]]
        extend (c:cs) t = if t `elem` c
                             then c:cs
                             else c : extend cs t

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

unSomeClassesN2 :: [Equation]
                -> Test.QuickSpec.Signature.Sig
                -> [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
unSomeClassesN2 eqs sig = collectExprs result
  where classes  = classesFromEqs eqs
        result   = unSomeSortedClasses classes sig

unSomeSortedClasses classes sig =
  unSomeSortedQSClasses (map (mkUnSomeClassN2 sig) classes)

unSomeSortedQSClasses classes = sortBy multi classes
  where multi (x:_) (y:_) = compareTerms x y

compareTerms (Test.QuickSpec.Utils.Typed.Some x) (Test.QuickSpec.Utils.Typed.Some y) =
  compare (Test.QuickSpec.Term.term x) (Test.QuickSpec.Term.term y)

collectExprs :: [[Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]]
        -> [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
collectExprs arg@[]   = []
collectExprs (xs:xss) = collectOne xs : collectExprs xss
  where collectOne :: [Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]
                   -> Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr
        collectOne xs = case xs of
          []                                     -> Test.QuickSpec.Utils.Typed.Some
                                                      (Test.QuickSpec.Utils.Typed.O
                                                        ([] :: [Test.QuickSpec.Term.Expr ()]))
          [Test.QuickSpec.Utils.Typed.Some x]    -> Test.QuickSpec.Utils.Typed.Some
                                                      (Test.QuickSpec.Utils.Typed.O
                                                        [x])
          (Test.QuickSpec.Utils.Typed.Some x:xs) -> case collectOne xs of
            Test.QuickSpec.Utils.Typed.Some
              (Test.QuickSpec.Utils.Typed.O (y:xs')) -> case cast x `asTypeOf` Just y of
                Just x' -> Test.QuickSpec.Utils.Typed.Some
                             (Test.QuickSpec.Utils.Typed.O (x':y:xs'))

mkUnSomeClassN :: Test.QuickSpec.Signature.Sig -> [Term] -> [Test.QuickSpec.Term.Expr a]
mkUnSomeClassN sig []     = []
mkUnSomeClassN sig (x:xs) = termToExprN x sig : mkUnSomeClassN sig xs

mkUnSomeClassN2 :: Test.QuickSpec.Signature.Sig
                -> [Term]
                -> [Test.QuickSpec.Utils.Typed.Some Test.QuickSpec.Term.Expr]
mkUnSomeClassN2 sig trms = sortBy compareTerms (mkUnSomeClassN2' sig trms)

mkUnSomeClassN2' sig []     = []
mkUnSomeClassN2' sig (x:xs) =
    case termType (setForTerm x) of
         Nothing -> error ("No type for " ++ show x)
         Just t  -> case getVal (getRep t) of
                         MkHT v -> (Test.QuickSpec.Utils.Typed.Some
                                     (Test.QuickSpec.Term.Expr term
                                                               arity
                                                               (const v))) : xs'
  where term        = renderTermN x sig
        Arity arity = termArity x
        xs' = mkUnSomeClassN2' sig xs

unSomePruneN :: [[Test.QuickSpec.Term.Expr Term]]
             -> Test.QuickSpec.Signature.Sig
             -> [Test.QuickSpec.Equation.Equation]
unSomePruneN clss sig = result
  where result = Test.QuickSpec.Main.prune ctx reps id eqs

        ctx   = mkCxt clss sig

        reps  = classesToReps clss

        eqs   = sort (mkEqs2N clss)

mkCxt :: (Typeable a) => [[Test.QuickSpec.Term.Expr a]]
                      -> Test.QuickSpec.Signature.Sig
                      -> Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context
mkCxt clss sig = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
                   (Test.QuickSpec.Signature.maxDepth sig)
                   (Test.QuickSpec.Signature.symbols  sig)
                   (mkUniv2N clss)

classesToReps clss = filter (not . Test.QuickSpec.Term.isUndefined)
                            (map (term . head) clss)

mkUniv2N :: Typeable a => [[Test.QuickSpec.Term.Expr a]]
                       -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]
mkUniv2N = concatMap (map univ2N)

univ2N :: Data.Typeable.Typeable a => Test.QuickSpec.Term.Expr a
                                   -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term
univ2N y = Test.QuickSpec.Utils.Typed.Tagged
             (Test.QuickSpec.Utils.Typed.Some
               (Test.QuickSpec.Utils.Typed.Witness (stripN y)))
             (term y)

stripN :: Test.QuickSpec.Term.Expr a -> a
stripN x = Test.QuickSpec.Term.eval x (Test.QuickSpec.Term.Valuation unvar)
  where unvar = runGen                       .
                Test.QuickSpec.Term.totalGen .
                Test.QuickSpec.Term.value    .
                Test.QuickSpec.Term.unVariable
        qcgen    = Test.QuickCheck.Random.mkQCGen 0
        runGen g = Test.QuickCheck.Gen.unGen g qcgen 0

term = Test.QuickSpec.Term.term

mkEqs2N cs = sort (concatMap f cs)
  where f (z:zs) = [term y Test.QuickSpec.Equation.:=: term z | y <- zs]

termToExprN :: Term
            -> Test.QuickSpec.Signature.Sig
            -> (Test.QuickSpec.Term.Expr a)
termToExprN t sig = Test.QuickSpec.Term.Expr term arity eval
  where term        = renderTermN t sig
        Arity arity = termArity t
        eval        = undefined

newtype Z = Z () deriving (Eq, Show, Typeable)
newtype S a = S a deriving (Eq, Show, Typeable, Ord)
instance Ord Z where compare _ _ = EQ
instance Ord (a -> b) where
  compare _ _ = EQ
instance Eq (a -> b) where
  _ == _ = True

showEqsOnLinesN :: [Test.QuickSpec.Equation.Equation]
                -> [Equation]
showEqsOnLinesN = map qsEqToEq

qsEqToEq (l Test.QuickSpec.Equation.:=: r) = Eq (qsTermToTerm l) (qsTermToTerm r)

qsTermToTerm t = case t of
  Test.QuickSpec.Term.Var   s -> V   (symToVar   s)
  Test.QuickSpec.Term.Const s -> C   (symToConst s)
  Test.QuickSpec.Term.App l r -> App (qsTermToTerm l) (qsTermToTerm r) Nothing

symToVar s =
  let n              = Test.QuickSpec.Term.name s
      [_, rawT, idx] = splitCommas n
   in Var (case HSE.Parser.parseType rawT of
             HSE.Parser.ParseOk t'        -> unwrapParens (const () <$> t')
             HSE.Parser.ParseFailed _ err -> error (concat [
                                    "Failed to parse var type: ",
                                    err,
                                    ". Type was: ",
                                    rawT]))
          (read (init idx) :: Int)
          (Arity (Test.QuickSpec.Term.symbolArity s))

symToConst s =
  let t = HSE.Parser.parseType (show (Test.QuickSpec.Term.symbolType s))
   in Const (Arity (Test.QuickSpec.Term.symbolArity s))
            (Name (Test.QuickSpec.Term.name s))
            (case t of
               HSE.Parser.ParseOk t'        -> unwrapParens (const () <$> t')
               HSE.Parser.ParseFailed _ err -> error (concat [
                                      "Failed to parse const type: ",
                                      err,
                                      ". Type was: ",
                                      show (Test.QuickSpec.Term.symbolType s)]))

splitCommas s = if ',' `elem` s
                   then takeWhile (/= ',') s :
                        splitCommas (tail (dropWhile (/= ',') s))
                   else [s]

pruneEqsN :: [Equation] -> [Equation]
pruneEqsN eqs = result
  where pruned  = doPrune classes sig
        sig     = let sig'  = renderN (sigFromEqs eqs)
                      sig'' = Test.QuickSpec.Signature.signature sig'
                   in sig'' `mappend` Test.QuickSpec.Main.undefinedsSig sig''
        result  = showEqsOnLinesN pruned
        classes = unSomeClassesN2 eqs sig

instance Show (Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term) where
  show t = show ("Tagged"      :: String,
                  ("tag"       :: String,
                    ("type"    :: String, Test.QuickSpec.Utils.Typed.witnessType
                                            (Test.QuickSpec.Utils.Typed.tag t))),
                  ("erase"     :: String, Test.QuickSpec.Utils.Typed.erase t))

doPrune clss sig = pruned
  where univ = concatMap (Test.QuickSpec.Utils.Typed.some2
                           (map (Test.QuickSpec.Utils.Typed.tagged term)))
                         clss
        reps = map (Test.QuickSpec.Utils.Typed.some2
                     (Test.QuickSpec.Utils.Typed.tagged term . head))
                   clss
        eqs  = Test.QuickSpec.Equation.equations clss

        ctx  = Test.QuickSpec.Reasoning.NaiveEquationalReasoning.initial
                 (Test.QuickSpec.Signature.maxDepth sig)
                 (Test.QuickSpec.Signature.symbols sig)
                 univ

        allEqs = map (Test.QuickSpec.Utils.Typed.some
                       Test.QuickSpec.Equation.eraseEquation)
                     eqs

        pruned = Test.QuickSpec.Main.prune
                   ctx
                   (filter (not . Test.QuickSpec.Term.isUndefined)
                           (map Test.QuickSpec.Utils.Typed.erase reps))
                   id
                   allEqs
