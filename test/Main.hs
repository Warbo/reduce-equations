{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module Main where

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
  , testProperty "Can generate terms from sig" canGenerateFromSig
  --, testProperty "Reduce examples"             canReduceExamples
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
  where mkExpr s = let e = "show" $$ (f $$ render s)
                       f = withQS "(const True :: Test.QuickSpec.Sig -> Bool)"
                    in (e, ("f", f))

sigsHaveConsts = testEval mkExpr (== Just "True")
  where mkExpr (s, cs) = let e            = "show" $$ (hasConsts $$ render s')
                             s'           = withConsts cs s
                             hasConsts    = withQS $ compose' checkConsts' constantSymbols'
                             checkConsts' = checkNames' names
                             names        = map constName cs
                             dbg          = ("names",  names)
                          in (e, dbg)

sigsHaveVars = testEval mkExpr (== Just "True")
  where mkExpr (s, vs) = let e          = "show" $$ (hasVars $$ render s')
                             s'         = withVars vs s
                             hasVars    = withQS $ compose' checkVars' variableSymbols'
                             checkVars' = checkNames' names
                             names      = map varName vs
                             dbg        = ("names", names)
                          in (e, dbg)

canGenerateFromSig = testEval' evl mkExpr expect
  where mkExpr s = let e     = ("(>>)" $$ doGen) $$ true
                       doGen = doGenerate' $$ render s
                       true  = "putStr" $$ asString "True"
                    in (e, ())
        evl      = eval' (\e -> "main = " ++ e)
        expect x = case x of
          Nothing -> False
          Just y  -> last (lines y) == "True"

--canReduceExamples = length (reduce exampleEqs) < length exampleEqs

-- Helpers

testEval :: (Arbitrary a, Show a, Show b) => (a -> (Expr, b))
                                          -> (Maybe String -> Bool)
                                          -> Property
testEval = testEval' eval

testEval' :: (Arbitrary a, Show a, Show b) => (Expr -> IO (Maybe String))
                                           -> (a -> (Expr, b))
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

constantSymbols' = withQS $ qualified "Test.QuickSpec.Signature"
                                      "constantSymbols"

variableSymbols' = withQS $ qualified "Test.QuickSpec.Signature"
                                      "variableSymbols"

isIn' = withQS $ lambda ["syms", "n"] body
  where body = ("any" $$ f) $$ "syms"
        f    = compose' "(== n)" name'

name' = withQS $ qualified "Test.QuickSpec.Term" "name"

checkNames' :: [Name] -> Expr
checkNames' ns = lambda ["syms"] body
  where body       = ("all" $$ (isIn' $$ "syms")) $$ names
        names      = raw $ "[" ++ commaNames ++ "]"
        commaNames = intercalate "," (map (show . (\(Name n) -> n)) ns)

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
