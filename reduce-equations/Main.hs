module Main where

import qualified Algebra.Equation.Reduce    as Reduce
import qualified Data.ByteString.Lazy.Char8 as BS

main = BS.interact Reduce.doReduce
