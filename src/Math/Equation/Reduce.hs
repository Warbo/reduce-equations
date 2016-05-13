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
    result <- pruneEqs eqs
    case result of
         Nothing -> error "Failed to reduce given input"
         Just o  -> return o
  where eqLines :: [String]
        eqLines = filter ("{" `isPrefixOf`) (lines s)

        eqs :: [Equation]
        eqs = map (fromJust . decode. S.fromString) eqLines
