module Main where

import Math.Equation.Reduce
import System.Environment

main = getContents >>= parseAndReduce >>= putStrLn
