{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module Main where

import Data.Aeson
import qualified Data.ByteString as B
import Data.ByteString.Lazy.Char8 (pack, unpack)
import Data.List
import Language.Eval.Internal
import System.Directory
import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty            (defaultMain, testGroup, localOption)
import Test.Tasty.QuickCheck

import qualified Test.QuickSpec.Term

import Math.Equation.Reduce
import Math.Equation.Internal

main = defaultMain $ testGroup "All tests" [
    testProperty "Can parse example equations" canParseExamples
  , testProperty "Can evaluate equations"      canEvalExamples
  , testProperty "Can make signature"          canMakeSignature
  , testProperty "Constants added"             constantsAdded
  , testProperty "Variables added"             variablesAdded
  , testProperty "Sigs render"                 sigsRender
  , testProperty "Sigs have constants"         sigsHaveConsts
  , testProperty "Sigs have variables"         sigsHaveVars
  , testProperty "Constants are distinct"      sigConstsUniqueIndices
  , testProperty "Variables are distinct"      sigVarsUniqueIndices
  , testProperty "Can generate terms from sig" canGenerateFromSig
  , testProperty "Can get classes from sig"    canGetClassesFromSig
  , testProperty "Can get universe from sig"   canGetUnivFromSig
  , testProperty "Can get context from sig"    canGetCxtFromSig
  , testProperty "Can get reps from sig"       canGetRepsFromSig
  , testProperty "Can get sig from equations"  canGetSigFromEqs
  , testProperty "Sig has equation variables"  eqSigHasVars
  , testProperty "Sig has equation constants"  eqSigHasConsts
  --, testProperty "Can get prune equations"     canPruneEquations
  ]

-- Tests

canParseExamples = not (null exampleEqs)

canEvalExamples = withExamples strict
  where strict (!x) = True

canMakeSignature = withExamples makeSig
  where makeSig xs = case sigFrom xs of
                          Sig !cs !vs -> True

constantsAdded cs s = case withConsts cs s of
  Sig cs' _ -> all (`elem` cs') cs

variablesAdded vs s = case withVars vs s of
  Sig _ vs' -> all (`elem` vs') vs

sigsRender = testEval mkExpr (== Just "True")
  where mkExpr s = let e = show' $$$ (f $$$ render s)
                       f :: TypedExpr (QSSig -> Bool)
                       f = TE $ withQS "(const True :: Test.QuickSpec.Sig -> Bool)"
                    in (e, ("f", f))

sigsHaveConsts = testEval mkExpr (== Just "True")
  where mkExpr (s, cs) = let e            = show' $$$ (hasConsts $$$ render s')
                             s'           = withConsts cs s
                             hasConsts :: TypedExpr (QSSig -> Bool)
                             hasConsts    = compose' checkConsts' constantSymbols'
                             checkConsts' :: TypedExpr ([Test.QuickSpec.Term.Symbol] -> Bool)
                             checkConsts' = checkNames' names
                             names        = map constName cs
                             dbg          = ("names",  names)
                          in (e, dbg)

sigsHaveVars = testEval mkExpr (== Just "True")
  where mkExpr (s, vs) = let e          = show' $$$ (hasVars $$$ render s')
                             s'         = withVars vs s
                             hasVars :: TypedExpr (QSSig -> Bool)
                             hasVars    = compose' checkVars' variableSymbols'
                             checkVars' = checkNames' names
                             names      = map varName vs
                             dbg        = ("names", names)
                          in (e, dbg)

sigConstsUniqueIndices = once sigConstsUniqueIndices'

-- Use `c` to generate a bunch of similar constants `consts`, add them to `s` to
-- get `sig`. Render `sig` to a QuickSpec signature, then print out its constant
-- symbols and compare with those of `sig`.
sigConstsUniqueIndices' s (Const a (Name n) t) = testEval mkExpr hasConsts
  where mkExpr () = let syms  = constantSymbols' $$$ render sig
                        names = (map' $$$ name') $$$ syms
                        e     = unlines' $$$ names
                     in (e, ("consts", consts))
        hasConsts Nothing    = error "Failed to evaluate"
        hasConsts (Just out) = setEq (map Name (lines out))
                                     (map constName (sigConsts sig))
        consts = [Const a (Name (n ++ show i)) t | i <- [0..10]]
        sig    = withConsts consts s

sigVarsUniqueIndices = once sigVarsUniqueIndices'

-- Use `v` to generate a bunch of `Var`s of the same type, `vars`, add them to
-- `s` to get `sig`. Render `sig` to a QuickSpec signature, then print out its
-- variable symbols and compare with those of `sig`.
sigVarsUniqueIndices' s (Var t _ a) = testEval mkExpr hasVars
  where mkExpr () = let syms  = variableSymbols' $$$ render sig
                        names = (map' $$$ name') $$$ syms
                        e     = unlines' $$$ names
                     in (e, ("vars", vars))
        hasVars Nothing    = error "Failed to evaluate"
        hasVars (Just out) = setEq (map Name (lines out))
                                   (map varName (sigVars sig))
        vars = [Var t i a | i <- [0..10]]
        sig  = withVars vars s

canGenerateFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doGenerate' s) $$$ putTrue
                    in (e, ())

canGetClassesFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doClasses' s) $$$ putTrue
                    in (e, ())

canGetUnivFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doUniv' s) $$$ putTrue
                    in (e, ())

canGetCxtFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doCtx' s) $$$ putTrue
                    in (e, ())

canGetRepsFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doReps' s) $$$ putTrue
                    in (e, ())

canGetSigFromEqs eqs = case sigFromEqs eqs of
  !(Sig _ _) -> True

eqSigHasVars eqs = counterexample debug test
  where sig     = sigFromEqs eqs
        sigvars = sigVars sig
        eqvars  = concatMap eqVars eqs
        test    = setEq sigvars eqvars
        debug   = show (("eqs", eqs),
                        ("sigvars", sigvars),
                        ("eqvars",  eqvars),
                        ("sig",     sig))

eqSigHasConsts eqs = counterexample debug test
  where sig       = sigFromEqs eqs
        test      = setEq sigconsts eqconsts
        sigconsts = sigConsts sig
        eqconsts  = concatMap eqConsts eqs
        debug     = show (("eqs",       eqs),
                          ("sig",       sig),
                          ("sigconsts", sigconsts),
                          ("eqconsts",  eqconsts))

--canReduceExamples = length (reduce exampleEqs) < length exampleEqs

-- Helpers

setEq xs ys = all (`elem` xs) ys && all (`elem` ys) xs

endsInTrue x = case x of
  Nothing -> False
  Just y  -> last (lines y) == "True"

putTrue :: TypedExpr (IO ())
putTrue  = TE $ "putStr" $$ asString "True"

-- | Check that the generated `String` expressions satisfy the given predicate.
--   The type `b` is for any extra debug output to include in case of failure.
testEval :: (Arbitrary a, Show a, Show b) => (a -> (TypedExpr String, b))
                                          -> (Maybe String -> Bool)
                                          -> Property
testEval = testEval' (\(TE e) -> eval e)

-- | Check that the output of the generated `IO` actions satifies the given
--   predicate. `b` is for extra debug output to include in case of failure.
testExec :: (Arbitrary a, Show a, Show b) => (a -> (TypedExpr (IO e), b))
                                           -> (Maybe String -> Bool)
                                           -> Property
testExec = testEval' exec

-- | Takes an expression-evaluating function, an expression-generating function
--   (`b` is any debug output we should include in case of failure), an
--   output-checking function and tests whether the output of evaluating the
--   generated expressions passes the checker.
testEval' :: (Arbitrary a, Show a, Show b) => (TypedExpr e -> IO (Maybe String))
                                            -> (a -> (TypedExpr e, b))
                                            -> (Maybe String -> Bool)
                                            -> Property
testEval' evl mkExpr expect = forAll (resize 10 arbitrary) go
  where go arg = once $ monadicIO $ do
                   let (e, dbg) = mkExpr arg
                   result <- run (evl e)
                   monitor . counterexample . show $ (("expr",   e),
                                                      ("result", result),
                                                      ("debug",  dbg))
                   assert (expect result)

constantSymbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
constantSymbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $
                                           "constantSymbols"

variableSymbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
variableSymbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $
                                           "variableSymbols"

-- Data generators

-- Example input from files

exampleEqs :: [[Object]]
exampleEqs = map parse exampleJson
  where parse x = case decode (pack x) of
          Nothing -> error ("Failed to parse JSON: " ++ x)
          Just  e -> e

exampleJson :: [String]
{-# NOINLINE exampleJson #-}
exampleJson = unsafePerformIO $ exampleFiles >>= mapM readFile

exampleDir = "test/data"

exampleFiles = do
    fs <- getDirectoryContents exampleDir
    return (prefix (json fs))
  where prefix   = map ((exampleDir ++ "/") ++)
        json     = filter isJson
        isJson :: String -> Bool
        isJson x = reverse ".json" == take 5 (reverse x)

withExamples f = forAll (elements exampleEqs) f

-- Random input generators

instance Arbitrary Equation where
  arbitrary = Eq <$> arbitrary <*> arbitrary

instance Arbitrary Term where
  arbitrary = oneof [App <$> arbitrary <*> arbitrary,
                     C <$> arbitrary,
                     V <$> arbitrary]

instance Arbitrary Var where
  arbitrary = sized $ \n -> do
    arity <- elements [0, 1, 2]
    typ   <- naryType arity n
    index <- elements [0, 1, 2]
    return $ Var (Type typ) index (Arity arity)

instance Arbitrary Const where
  arbitrary = sized $ \n -> do
    arity <- elements [0..5]
    name  <- listOf1 arbitrary
    typ   <- naryType arity n
    return $ Const (Arity arity) (Name name) (Type typ)

instance Arbitrary Sig where
  arbitrary = Sig <$> listOf arbitrary <*> listOf arbitrary

instance Arbitrary Type where
  arbitrary = Type <$> sized sizedType

sizedType :: Int -> Gen String
sizedType 0 = elements ["Int", "Bool", "Float"]
sizedType n = oneof [
    sizedType 0,
    do x <- sizedType (n - 1)
       return $ "[" ++ x ++ "]",
    do n' <- choose (0, n - 1)
       l  <- sizedType n'
       r  <- sizedType (n - n')
       return $ "(" ++ l ++ ", " ++ r ++ ")"
  ]

naryType 0 n = sizedType n
naryType a n = do
  arg <- sizedType n
  ret <- naryType (a-1) n
  return $ "(" ++ arg ++ ") -> (" ++ ret ++ ")"
