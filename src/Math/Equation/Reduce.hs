{-# LANGUAGE OverloadedStrings #-}

module Math.Equation.Reduce (
    module Test.QuickSpec.Equation
  , module Data.Aeson
  --, reduce
  ) where

import Control.Monad
import Control.Monad.Trans.State.Strict as S
import Data.Functor.Identity
import Control.Monad.Reader
import Data.Aeson
import Data.List
import Test.QuickSpec.Equation
import Test.QuickSpec.Main hiding (universe)
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning hiding (rep, get, put)
import Test.QuickSpec.Term

{-
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
-}
{-
-- Adapted from Test.QuickSpec.Main.prune
prune :: Context -> [Term] -> (a -> Equation) -> [a] -> [a]
prune ctx reps erase eqs = fst (runIdentity (runStateT (doFilterM eqs) (rel ctx)))
  where
    doFilterM []     = []
    doFilterM (x:xs) = let flg = runReaderT (provable (erase x)) (maxDepth ctx, universe ctx)
                           ys  = doFilterM xs
                        in if flg then ys else x:ys

    provable (t :=: u) = do
      x <- flatten t
      y <- flatten u
      a <- rep x
      b <- rep y
      if a == b
         then return True
         else do state <- get
                 unify (t :=: u)
                 reps' <- mapM rep reps
                 let eq = distinct reps'
                 unless eq (put state)
                 return (not eq)

    unify (t :=: u) = do x <- flatten t
                         y <- flatten u
                         p <- rep x
                         q <- rep y
                         let b = p == q
                         unless b $ mapM_ (\s -> do t' <- subst s t
                                                    u' <- subst s u
                                                    (unified, pending) <- propagate1 (t', u')
                                                    mapM_ propagate pending
                                                    return unified)
                                          (foo t ++ foo u)
                         return b
    foo x = substs x (universe ctx) (maxDepth ctx)

flatten (Var   x) = return (index x)
flatten (Const x) = return (index x)
flatten (App f x) = do
  f' <- flatten f
  x' <- flatten x
  f' CC.$$ x'


subst :: (Symbol -> Int) -> Term -> CC Int
subst s (Var   x) = return (s x)
subst s (Const x) = return (index x)
subst s (App f x) = do
  f' <- subst s f
  x' <- subst s x
  f' CC.$$ x'

substs :: Term -> IntMap Universe -> Int -> [Subst]
substs t univ d = map lookup (sequence (map choose vars))
  where vars = map (maximumBy (comparing snd)) .
               partitionBy fst .
               holes $ t

        choose (x, n) =
          let m = IntMap.findWithDefault (ERROR "empty universe")
                  (index x) univ in
          [ (x, t)
          | d' <- [0..d-n],
            t <- IntMap.findWithDefault [] d' m ]

        lookup ss =
          let m = IntMap.fromList [ (index x, y) | (x, y) <- ss ]
          in \x -> IntMap.findWithDefault (index x) (index x) m

distinct reps = sort reps == map head (group (sort reps))

get = ReaderT (const S.get)

put x = ReaderT (const (S.put x))

rep x = ReaderT (const (flatten x >>= CC.rep))

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

propagate (a, b) = do
  (unified, pending) <- propagate1 (a, b)
  mapM_ propagate pending
  return unified

propagate1 (a, b) = do
  invariant (printf "before propagate (%s, %s)" (show a) (show b))
  res <- liftUF (a UF.=:= b)
  case res of
    Nothing -> return (False, [])
    Just (r :> r') -> do
      funUses <- gets (IntMap.lookup r . funUse)
      argUses <- gets (IntMap.lookup r . argUse)
      case (funUses, argUses) of
        (Nothing, Nothing) -> return (True, [])
        _ -> fmap (\x -> (True, x)) (updateUses r r' (fromMaybe [] funUses) (fromMaybe [] argUses))

liftCC x = ReaderT (const x)




















runTool :: Signature a => (Sig -> IO ()) -> a -> IO ()
runTool tool sig_ = tool (signature sig_ `mappend` undefinedsSig (signature sig_))





quickSpec :: Signature a => a -> IO ()
quickSpec = runTool qsReal

qsReal sig = fmap (doPrune sig) (generateTermsSatisfying False (const True) (const partialGen) sig)

doPrune sig r = pruned
  where clss   = concatMap (some2 (map (Some . O) . classes)) (TypeMap.toList r)
        univ   = concatMap (some2 (map (tagged term))) clss
        reps   = map (some2 (tagged term . head)) clss
        eqs    = equations clss
        ctx    = initial (maxDepth sig) (symbols sig) univ
        allEqs = map (some eraseEquation) eqs
        terms  = filter (not . isUndefined) (map erase reps)
        pruned = prune ctx terms id allEqs

generateTermsSatisfying :: Bool -> (Term -> Bool) -> Strategy -> Sig -> IO (TypeMap (TestResults `O` Expr))
generateTermsSatisfying shutUp p strat sig = unbuffered $ do
  rs <- fmap (TypeMap.mapValues2 reps) (generate False (const partialGen) (updateDepth (maxDepth sig - 1) sig))
  let ts = TypeMap.fromList [
               Some (O (terms' p sig rs w))
             | Some (Witness w) <- usort (saturatedTypes sig ++ variableTypes sig) ]
  seeds <- genSeeds (maxQuickCheckSize sig)
  let cs = fmap (mapSome2 (test' (map (toValuation strat sig) seeds) sig)) ts
  return cs

















prune :: Context -> [Term] -> (a -> Equation) -> [a] -> [a]
prune ctx reps erase = evalEQ ctx . doFilterM

doFilterM [] = return []
doFilterM (x:xs) = do p  <- provable reps (erase x)
                      ys <- doFilterM xs
                      return $ if p then ys else x:ys

provable reps (t :=: u) = do
  res <- (liftCC same) t u
  if res
     then return True
     else do
        state <- get
        unify (t :=: u)
        reps' <- mapM (liftCC nerRep) reps
        if distinct reps'
           then return False
           else do put state
                   return True

usort = map head . group . sort

distinct reps = sort reps == map head (group (sort reps))

same t u = do
  x <- flatten t
  y <- flatten u
  same2 x y

same2 t u = liftM2 (==) (ccRep t) (ccRep u)

nerRep x = flatten x >>= ccRep

ccRep = liftUF . ufRep

ufRep t = do
  m <- fmap links get
  case IntMap.lookup t m of
       Nothing -> return t
       Just t' -> do r <- rep t'
                     when (t' /= r) $ modifyLinks (IntMap.insert t r)
                     return r

links :: UF.S -> IntMap Int
-}
