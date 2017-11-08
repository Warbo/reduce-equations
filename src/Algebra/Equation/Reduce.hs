{-# LANGUAGE OverloadedStrings #-}

module Algebra.Equation.Reduce where

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8   as BS
import qualified Data.ByteString.Internal     as BI
import           Data.List
import qualified Data.Map                     as Map
import           Data.Maybe
import qualified Data.Stringable              as S
import qualified Data.Text.Lazy               as T
import qualified Data.Text.Lazy.Encoding      as TE
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
import           Algebra.Equation.Internal.Eval
import           Algebra.Equation.Internal.Types

doReduce = encode . parseAndReduce

parseAndReduce s = case eitherDecode s of
  Left  err -> error ("Failed to parse eqs: " ++ err)
  Right eqs -> reduction eqs

reduction :: [Equation] -> [Equation]
reduction eqs = if consistent eqs'
                    then map normalise result
                    else error "Inconsistent types in parsed equations"
  where eqs'        = setAllTypes eqs
        (db, eqs'') = replaceTypes eqs'
        o           = pruneEqsN eqs''
        result      = restoreTypes db o

replaceTypes :: [Equation] -> ([(Type, Type)], [Equation])
replaceTypes eqs = let db = zip typs new
                    in (db, map (replaceEqTypes db) eqs)
  where typs = allTypes eqs
        new  = iterate s z
        z = tyCon "Z"
        s = HSE.Syntax.TyApp () (tyCon "S")

replaceEqTypes db (Eq l r) = Eq (replaceTermTypes db l) (replaceTermTypes db r)

replaceTermTypes db trm = case trm of
    C (Const a n t) -> C (Const a n (replace t))
    V (Var t i a)   -> V (Var (replace t) i a)
    App l r t       -> App (replaceTermTypes db l)
                           (replaceTermTypes db r)
                           (replace <$> t)
  where replace = replaceInType db . unwrapParens

tyCon = HSE.Syntax.TyCon () . HSE.Syntax.UnQual () . HSE.Syntax.Ident ()

allTypes :: [Equation] -> [Type]
allTypes = nub . filter notFunc
               . concatMap components
               . catMaybes
               . nub
               . concatMap eqTypes
  where eqTypes (Eq l r) = termTypes l ++ termTypes r
        termTypes (App l r t) = [unwrapParens <$> t] ++ termTypes l ++ termTypes r
        termTypes t           = [unwrapParens <$> termType t]

        notFunc HSE.Syntax.TyFun{} = False
        notFunc _                  = True

        components (HSE.Syntax.TyFun _ i o) = components i ++ components o
        components t                        = [t]

restoreTypes :: [(Type, Type)] -> [Equation] -> [Equation]
restoreTypes db = map (replaceEqTypes db')
  where db'         = map swap db
        swap (x, y) = (y, x)

normalise (Eq lhs rhs) = if orderedEq eq1
                            then eq1
                            else if orderedEq eq2
                                    then eq2
                                    else error ("No order for " ++ show eq1)
  where eq1 = renumber (Eq lhs rhs)
        eq2 = renumber (Eq rhs lhs)

orderedEq (Eq lhs rhs) = termLessThanEq lhs rhs

renumber (Eq lhs rhs) = Eq lhs' rhs'
  where lhs' = setAll final (setAll bump lhs types) types
        rhs' = setAll final (setAll bump rhs types) types

        -- Recurse to find all vars of all types, replace their indices using
        -- lookup table m, which maps a type and index to a new index
        setAll :: (Map.Map Type (Map.Map Int Int)) -> Term -> [Type] -> Term
        setAll m x []     = x
        setAll m x (t:ts) = setAll m (setFor m t x) ts
        setFor m t (V (Var t' i a)) = if t == t'
                                         then V (Var t' (m Map.! t Map.! i) a)
                                         else V (Var t' i                   a)
        setFor m t (C c)            = C c
        setFor m t (App f x y)      = App (setFor m t f) (setFor m t x) y

        vars     = eqVars (Eq lhs rhs)
        types    = nub (map varType vars)
        maxVar   = maximum (map varIndex vars)
        varsOf t = filter ((t ==) . varType) vars

        -- Increase each var index to be outside the range of the final indices.
        -- We do this to prevent clashes, e.g. replacing x with y and y with z.
        doBump n = n + maxVar + 1
        bump = Map.fromList
                 (map (\t -> (t, Map.fromList
                                   (map ((\i -> (i, doBump i)) . varIndex)
                                        (varsOf t))))
                      types)

        -- Make each type's variables sequential
        final = Map.fromList
                  (map (\t -> (t, Map.fromList (zip (map (doBump . varIndex)
                                                         (varsOf t))
                                                    [0..])))
                       types)
