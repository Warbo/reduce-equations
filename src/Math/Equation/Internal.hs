{-# LANGUAGE OverloadedStrings, RankNTypes, ExistentialQuantification, PartialTypeSignatures #-}
module Math.Equation.Internal (
    module Math.Equation.Internal.Eval
  , module Math.Equation.Internal.Types
  ) where

import Math.Equation.Internal.Eval  -- Used for interacting with QuickSpec
import Math.Equation.Internal.Types -- Our own representations
