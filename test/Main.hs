module Main where

import qualified Data.ByteString as B
import Data.ByteString.Lazy.Char8 (pack, unpack)
import System.Directory
import System.IO.Unsafe
import Test.Tasty            (defaultMain, testGroup, localOption)
import Test.Tasty.QuickCheck

import Math.Equation.Reduce

main = defaultMain $ testGroup "All tests" [
    testProperty "Can parse example equations" canParseExamples
  , testProperty "Reduce examples"             canReduceExamples
  ]

-- Tests

canParseExamples = forAll (elements exampleJson) canParse
  where canParse s = case decode (pack s) :: Maybe [Equation] of
         Nothing -> error ("Failed to parse: " ++ s)
         Just _  -> True

canReduceExamples = forAll (elements exampleJson) canReduce
  where canReduce s = length (reduce s) < length s

-- Helpers

exampleJson :: [String]
{-# NOINLINE exampleJson #-}
exampleJson = unsafePerformIO $ exampleFiles >>= mapM readFile

exampleDir = "test/data"

exampleFiles = do
    fs <- getDirectoryContents exampleDir
    return (prefix (json fs))
  where prefix   = map ((exampleDir ++ "/") ++)
        json     = filter isJson
        isJson x = reverse ".json" == take 5 (reverse x)
