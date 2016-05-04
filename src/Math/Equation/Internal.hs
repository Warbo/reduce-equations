{-# LANGUAGE OverloadedStrings, RankNTypes, ExistentialQuantification, PartialTypeSignatures #-}
module Math.Equation.Internal (
    module Math.Equation.Internal.Eval
  , module Math.Equation.Internal.Types
  , classesFromEqs
  ) where

import Data.List
import Language.Eval.Internal
import Math.Equation.Internal.Eval  -- Used for interacting with QuickSpec
import Math.Equation.Internal.Types -- Our own representations

classesFromEqs :: [Equation] -> [[Term]]
classesFromEqs = map nub . addAllToClasses []

addAllToClasses cs    []  = cs
addAllToClasses cs (e:es) = addAllToClasses (addToClasses cs e) es

addToClasses cs (Eq l r) = case cs of
  []   -> [[l, r]]
  x:xs -> if l `elem` x
             then (r:x):xs
             else if r `elem` x
                     then (l:x):xs
                     else x : addToClasses xs (Eq l r)

{-
data Equation = Eq Term Term

instance FromJSON Equation where
  parseJSON (Object v) = Eq <$> v .: "lhs" <*> v .: "rhs"
  parseJSON _ = fail "Couldn't parse equation from JSON"

data Term = A Term Term | C Const | V Var

instance FromJSON Term where
  parseJSON (Object v) = do
    role <- v .: "role"
    case role of
      "application" -> A <$> v .: "lhs" <*> v .: "rhs"
      "constant"    -> do arity <- v .: "arity"
                          typ   <- v .: "type"
                          name  <- v .: "name"
                          return (C (Const arity name typ))
      "variable"    -> do typ   <- v .: "type"
                          index <- v .: "index"
                          arity <- v .: "arity"
                          return (V (Var typ index arity))
      _             -> fail ("Unknown term role: " ++ role)
  parseJSON x = fail ("Couldn't parse Term from JSON: " ++ show x)

renderEqs :: [Equation] -> Expr
renderEqs eqs = lambda ["sig"] body
  where body = raw $ "[" ++ intercalate "," (map renderEq eqs) ++ "]"
        renderEq :: Equation -> String
        renderEq (Eq lhs rhs) = let lhs' = "(" ++ renderTerm lhs ++ ")"
                                    rhs' = "(" ++ renderTerm rhs ++ ")"
                                 in "(" ++ lhs' ++ " :=: " ++ rhs' ++ ")"
        renderTerm :: Term -> String
        renderTerm t = case t of
          A lhs rhs -> "(App (" ++ renderTerm lhs ++ ") (" ++ renderTerm rhs ++ "))"
          V v       -> "(Var ("   ++ findSym (varName   v) ++ "))"
          C c       -> "(Const (" ++ findSym (constName c) ++ "))"
        -- Assumes a variable "sig" is in scope; extracts all symbols from "sig"
        -- and returns the one with a name matching "n". Assumes that such a
        -- symbol exists!
        findSym (Name n) = let pred = "(== " ++ show n ++ ") . Test.QuickSpec.Signature.name"
                               syms = "Test.QuickSpec.Signature.symbols sig"
                            in "(head (filter (" ++ pred ++ ") (" ++ syms ++ ")))"
-}
