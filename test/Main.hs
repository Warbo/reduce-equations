{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module Main where

import qualified Data.ByteString as B
import Data.ByteString.Lazy.Char8 (pack, unpack)
import Data.List
import Language.Eval
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

sigsRender = forAll (resize 2 arbitrary) sigsRender'

sigsRender' s = once $ monadicIO $ do
    result <- run $ eval ("show" $$ (f $$ render s))
    assert (result == Just "True")
  where f = withPkgs ["quickspec"] $ withMods ["Test.QuickSpec"] $
            "(const True :: Test.QuickSpec.Sig -> Bool)"

sigsHaveConsts = forAll (resize 2 arbitrary)
                        (\(s, cs) -> sigsHaveConsts' s cs)

sigsHaveConsts' s cs = once $ monadicIO $ do
    result <- run $ eval ("show" $$ (hasConsts $$ render s'))
    assert (result == Just "True")
  where s' = withConsts cs s
        hasConsts   = withMods ["Test.QuickSpec.Term", "Test.QuickSpec.Signature"] $
                      withDefs $ "(checkConsts . Test.QuickSpec.Signature.constantSymbols)"
        withDefs    = withPreamble checkConsts . withPreamble isIn
        checkConsts = "checkConsts syms = all (isIn syms) [" ++
                        intercalate "," (map (show . (\(Name n) -> n) . constName) cs) ++ "]"
        isIn        = "isIn syms n = any ((== n) . Test.QuickSpec.Term.name) syms"

--canReduceExamples = length (reduce exampleEqs) < length exampleEqs

-- Helpers

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
  arbitrary = return Var

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
    do n' <- choose (0, n - 1)
       l  <- sizedType n'
       r  <- sizedType (n - n')
       return $ "(" ++ l ++ ") -> (" ++ r ++ ")",
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
