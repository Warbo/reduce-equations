{-# LANGUAGE RankNTypes, ExistentialQuantification, PartialTypeSignatures #-}
module Algebra.Equation.Internal (
    module Algebra.Equation.Internal.Eval
  , module Algebra.Equation.Internal.Types
  ) where

import Algebra.Equation.Internal.Eval  -- Used for interacting with QuickSpec
import Algebra.Equation.Internal.Types -- Our own representations
