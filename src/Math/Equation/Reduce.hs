{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Reduce where

import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as BS
import           Data.List
import           Data.Maybe
import qualified Data.Stringable         as S
import qualified Data.Text.Lazy          as T
import qualified Data.Text.Lazy.Encoding as TE
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
import           Math.Equation.Internal.Eval
import           Math.Equation.Internal.Types

doReduce = BS.getContents >>= parseAndReduce >>= showEqs

showEqs = mapM_ (BS.putStrLn . encode)

parseAndReduce :: BS.ByteString -> IO [Equation]
parseAndReduce s = do
    let (db, eqs) = replaceTypes (parseLines s)
    result <- pruneEqs eqs
    case result of
         Nothing -> error "Failed to reduce given input"
         Just o  -> return (replaceVars db (S.fromString o))

parseLines :: BS.ByteString -> [Equation]
parseLines s = map (setForEq . parse) eqLines
  where eqLines :: [BS.ByteString]
        eqLines = filter (BS.isPrefixOf "{") (bsLines s)
        bsLines = BS.split newline
        newline = head (BS.unpack "\n")


parse :: BS.ByteString -> Equation
parse l = fromMaybe (error ("Couldn't parse line: " ++ S.toString l))
                    (decode l)

replaceTypes :: [Equation] -> ([(Type, Type)], [Equation])
replaceTypes eqs = let db = zip typs new
                    in (db, map (replaceEqTypes db) eqs)
  where typs = allTypes eqs
        new  = iterate s z
        z = tyCon "Z"
        s = HSE.Syntax.TyApp (tyCon "S")

replaceEqTypes db (Eq l r) = Eq (replaceTermTypes l) (replaceTermTypes r)
  where replaceTermTypes (C (Const a n t))  = C (Const a n (replaceInType t))
        replaceTermTypes (V (Var t i a))    = V (Var (replaceInType t) i a)
        replaceTermTypes (App l r (Just t)) = App (replaceTermTypes l)
                                                  (replaceTermTypes r)
                                                  (Just (replaceInType t))

        replaceInType (HSE.Syntax.TyFun i o) = HSE.Syntax.TyFun (replaceInType i)
                                                                (replaceInType o)
        replaceInType t                      = fromJust (lookup t db)

tyCon = HSE.Syntax.TyCon . HSE.Syntax.UnQual . HSE.Syntax.Ident

allTypes :: [Equation] -> [Type]
allTypes = filter notFunc . concatMap components . catMaybes . nub . concatMap eqTypes
  where eqTypes (Eq l r) = termTypes l ++ termTypes r
        termTypes (App l r t) = [t] ++ termTypes l ++ termTypes r
        termTypes t           = [termType t]

        notFunc (HSE.Syntax.TyFun _ _) = False
        notFunc _                      = True

        components (HSE.Syntax.TyFun i o) = components i ++ components o
        components t                      = [t]

replaceVars db = restoreTypes db . parseLines

restoreTypes :: [(Type, Type)] -> [Equation] -> [Equation]
restoreTypes db = map (replaceEqTypes db')
  where db'         = map swap db
        swap (x, y) = (y, x)
