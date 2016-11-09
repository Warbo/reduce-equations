{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Reduce where

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Internal   as BI
import           Data.List
import           Data.Maybe
import qualified Data.Stringable         as S
import qualified Data.Text.Lazy          as T
import qualified Data.Text.Lazy.Encoding as TE
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
import           Math.Equation.Internal.Eval
import           Math.Equation.Internal.Types

doReduce = parseAndReduce <$> BS.getContents >>= showEqs

showEqs = mapM_ (BS.putStrLn . encode)

parseAndReduce s = case eitherDecode s of
  Left  err -> error ("Failed to parse eqs: " ++ err)
  Right eqs -> reduction eqs

reduction :: [Equation] -> [Equation]
reduction eqs = if consistent eqs'
                    then result
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

        notFunc (HSE.Syntax.TyFun _ _ _) = False
        notFunc _                        = True

        components (HSE.Syntax.TyFun _ i o) = components i ++ components o
        components t                        = [t]

restoreTypes :: [(Type, Type)] -> [Equation] -> [Equation]
restoreTypes db = map (replaceEqTypes db')
  where db'         = map swap db
        swap (x, y) = (y, x)
