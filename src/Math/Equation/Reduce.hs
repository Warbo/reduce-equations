{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Reduce (
    module Test.QuickSpec.Equation
  , module Data.Aeson
  , reduce
  ) where

import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Aeson
import Test.QuickSpec.Equation
import Test.QuickSpec.Main hiding (universe)
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning
import Test.QuickSpec.Term

instance FromJSON Equation where
  parseJSON (Object v) = (:=:) <$> v .: "lhs" <*> v .: "rhs"
  parseJSON _ = fail "Couldn't parse equation from JSON"

instance FromJSON Term where
  parseJSON (Object v) = do
    role <- v .: "role"
    case role of
      "application" -> App <$> v .: "lhs" <*> v .: "rhs"
      "constant"    -> parseConst v
      "variable"    -> parseVar   v
      _             -> fail ("Unknown term role: " ++ role)
  parseJSON _ = fail "Couldn't parse Term from JSON"

parseConst v = return (Const undefined)

parseVar v = return (Var undefined)

dpth = 3

reduce = let ts   = []
             tts  = []
             syms = []
             cxt  = initial dpth syms tts
             toEq = undefined
          in prune cxt ts toEq
