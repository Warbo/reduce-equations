{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Reduce where

import           Data.Aeson
import           Data.List
import           Data.Maybe
import qualified Data.Stringable as S
import           Math.Equation.Internal.Eval
import           Math.Equation.Internal.Types

parseAndReduce :: String -> IO String
parseAndReduce s = do
    result <- pruneEqs (parseLines s)
    case result of
         Nothing -> error "Failed to reduce given input"
         Just o  -> return o

parseLines :: String -> [Equation]
parseLines s = map parse eqLines
  where eqLines :: [String]
        eqLines = filter ("{" `isPrefixOf`) (lines s)

parse :: String -> Equation
parse l = fromMaybe (error ("Couldn't parse line: " ++ l))
                    (decode (S.fromString l))
