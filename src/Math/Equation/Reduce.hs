{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Reduce where

import           Data.Aeson
import qualified Data.ByteString.Lazy  as BS
import           Data.List
import           Data.Maybe
import qualified Data.Stringable as S
import           Math.Equation.Internal.Eval
import           Math.Equation.Internal.Types

doReduce = BS.getContents >>= parseAndReduce >>= putStrLn

parseAndReduce :: BS.ByteString -> IO String
parseAndReduce s = do
    result <- pruneEqs (parseLines s)
    case result of
         Nothing -> error "Failed to reduce given input"
         Just o  -> return o

parseLines :: BS.ByteString -> [Equation]
parseLines s = map (setForEq . parse) eqLines
  where eqLines :: [BS.ByteString]
        eqLines = filter (BS.isPrefixOf "{") (BS.split newline s)
        newline = head (BS.unpack "\n")

parse :: BS.ByteString -> Equation
parse l = fromMaybe (error ("Couldn't parse line: " ++ S.toString l))
                    (decode l)

{-
pruneEqs2 :: [Equation] -> IO (Maybe String)
pruneEqs2 = pruneEqs . alterTypes

alterTypes =
-}
