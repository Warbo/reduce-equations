{-# LANGUAGE BangPatterns, OverloadedStrings, PartialTypeSignatures #-}

module Main where

import           Data.Aeson
import qualified Data.ByteString as B
import           Data.ByteString.Lazy.Char8 (pack, unpack)
import           Data.Char
import           Data.List
import           Data.Maybe
import qualified Data.Sequence   as Seq
import qualified Data.Stringable as S
import Language.Eval.Internal
import System.Directory
import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty            (defaultMain, testGroup, localOption)
import Test.Tasty.QuickCheck

import qualified Test.QuickSpec.Term

import Math.Equation.Reduce
import Math.Equation.Internal

main = defaultMain $ testGroup "All tests" [
    testProperty "Can parse example equations"  canParseExamples
  , testProperty "Can evaluate equations"       canEvalExamples
  , testProperty "Can make signature"           canMakeSignature
  , testProperty "Constants added"              constantsAdded
  , testProperty "Variables added"              variablesAdded
  , testProperty "Sigs render"                  sigsRender
  , testProperty "Sigs have constants"          sigsHaveConsts
  , testProperty "Sigs have variables"          sigsHaveVars
  , testProperty "Constants are distinct"       sigConstsUniqueIndices
  , testProperty "Variables are distinct"       sigVarsUniqueIndices
  , testProperty "Can find closure of term"     canFindClosure
  , testProperty "Can generate terms from sig"  canGenerateFromSig
  , testProperty "No classes without equations" noClassesFromEmptyEqs
  , testProperty "Equation induces a class"     oneClassFromEq
  , testProperty "Classes contain given terms"  classesHaveTerms
  , testProperty "Equal terms in same class"    eqPartsAppearInSameClass
  , testProperty "Terms appear in one class"    classesHaveNoDupes
  , testProperty "Class elements are equal"     classElementsAreEqual
  , testProperty "Non-equal elements separate"  nonEqualElementsSeparate
  , testProperty "Can get classes from sig"     canGetClassesFromEqs
  , testProperty "Can get universe from sig"    canGetUnivFromSig
  , testProperty "Can get context from sig"     canGetCxtFromSig
  , testProperty "Can get sig from equations"   canGetSigFromEqs
  , testProperty "Sig has equation variables"   eqSigHasVars
  , testProperty "Sig has equation constants"   eqSigHasConsts
  , testProperty "Can render equations"         canRenderEqs
  --, testProperty "Can get prune equations"     canPruneEquations
  ]

-- Tests

canParseExamples = not (null exampleEqs)

canEvalExamples = withExamples strict
  where strict (!x) = True

canMakeSignature = withExamples makeSig
  where makeSig xs = case sigFrom xs of
                          Sig !cs !vs -> True

constantsAdded cs s = case withConsts cs s of
  Sig cs' _ -> all (`elem` cs') cs

variablesAdded vs s = case withVars vs s of
  Sig _ vs' -> all (`elem` vs') vs

sigsRender = testEval mkExpr (== Just "True")
  where mkExpr s = let e = show' $$$ (f $$$ render s)
                       f :: TypedExpr (QSSig -> Bool)
                       f = TE $ withQS "(const True :: Test.QuickSpec.Sig -> Bool)"
                    in (e, ("f", f))

sigsHaveConsts = testEval mkExpr (== Just "True")
  where mkExpr (s, cs) = let e            = show' $$$ (hasConsts $$$ render s')
                             s'           = withConsts cs s
                             hasConsts :: TypedExpr (QSSig -> Bool)
                             hasConsts    = compose' checkConsts' constantSymbols'
                             checkConsts' :: TypedExpr ([Test.QuickSpec.Term.Symbol] -> Bool)
                             checkConsts' = checkNames' names
                             names        = map constName cs
                             dbg          = ("names",  names)
                          in (e, dbg)

sigsHaveVars = testEval mkExpr (== Just "True")
  where mkExpr (s, vs) = let e          = show' $$$ (hasVars $$$ render s')
                             s'         = withVars vs s
                             hasVars :: TypedExpr (QSSig -> Bool)
                             hasVars    = compose' checkVars' variableSymbols'
                             checkVars' = checkNames' names
                             names      = map varName vs
                             dbg        = ("names", names)
                          in (e, dbg)

sigConstsUniqueIndices = once sigConstsUniqueIndices'

-- Use `c` to generate a bunch of similar constants `consts`, add them to `s` to
-- get `sig`. Render `sig` to a QuickSpec signature, then print out its constant
-- symbols and compare with those of `sig`.
sigConstsUniqueIndices' s (Const a (Name n') t) = testEval mkExpr hasConsts
  where n = 'x' : n'  -- Avoid issues with linefeed being cut off
        mkExpr () = let syms  = constantSymbols' $$$ render sig
                        names = (map' $$$ name') $$$ syms
                        e     = unlines' $$$ names
                     in (e, ("consts", consts))
        hasConsts Nothing    = error "Failed to evaluate"
        hasConsts (Just out) = setEq (map Name (lines out))
                                     (map constName (sigConsts sig))
        consts = [Const a (Name (n ++ show i)) t | i <- [0..10]]
        sig    = withConsts consts s

sigVarsUniqueIndices = once sigVarsUniqueIndices'

-- Use `v` to generate a bunch of `Var`s of the same type, `vars`, add them to
-- `s` to get `sig`. Render `sig` to a QuickSpec signature, then print out its
-- variable symbols and compare with those of `sig`.
sigVarsUniqueIndices' s (Var t _ a) = testEval mkExpr hasVars
  where mkExpr () = let syms  = variableSymbols' $$$ render sig
                        names = (map' $$$ name') $$$ syms
                        e     = unlines' $$$ names
                     in (e, ("vars", vars))
        hasVars Nothing    = error "Failed to evaluate"
        hasVars (Just out) = setEq (map Name (lines out))
                                   (map varName (sigVars sig))
        vars = [Var t i a | i <- [0..10]]
        sig  = withVars vars s

canGenerateFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doGenerate' s) $$$ putTrue
                    in (e, ())

noClassesFromEmptyEqs = null (classesFromEqs [])

oneClassFromEq eq = length (classesFromEqs [eq]) == 1

classesHaveTerms eqs = found `all` terms
  where terms            = concatMap termsOf eqs
        termsOf (Eq l r) = [l, r]
        found t          = (t `elem`) `any` classes
        classes          = classesFromEqs eqs

eqPartsAppearInSameClass eqs = all eqPartsInSameClass eqs
  where classes                     = classesFromEqs eqs
        matchingClass t             = head $ filter (t `elem`) classes
        eqPartsInSameClass (Eq l r) = r `elem` (matchingClass l) &&
                                      l `elem` (matchingClass r)

classesHaveNoDupes eqs = all appearOnce terms
  where classes      = classesFromEqs eqs
        terms        = concat classes
        appearOnce t = length (filter (t `elem`) classes) == 1

nonEqualElementsSeparate t v = match classes expected && match expected classes
  where (a:b:c:d:e:f:_) = map extend [0..]

        extend 0 = t
        extend n = App v (extend (n-1))

        eqs = [Eq a b, Eq b c, Eq d e, Eq e f]

        classes = classesFromEqs eqs

        expected = [[a, b, c], [d, e, f]]

        match    []  ys = True
        match (x:xs) ys = any (setEq x) ys && match xs ys

classElementsAreEqual :: [Equation] -> _
classElementsAreEqual eqs = all elementsAreEqual classes
  where classes :: [[Term]]
        classes              = classesFromEqs eqs

        terms                = nub $ concatMap termsOf eqs
        termsOf (Eq x y)     = [x, y]

        elementsAreEqual :: [Term] -> Bool
        elementsAreEqual cls = all (equalToAll cls) cls

        equalToAll :: [Term] -> Term -> Bool
        equalToAll xs y = all (equal y) xs

        equal :: Term -> Term -> Bool
        equal x y = y `isElem` eqClosure eqs x

canFindClosure t v = all match expected
  where -- Generate unique terms by wrapping in "App c"
        (a:b:c:d:e:f:g:h:_) = map extend [0..]
        extend 0 = t
        extend n = App v (extend (n-1))

        match (x, xs) = setEq (eqClosure eqs x) xs

        eqs = [Eq a b, Eq a c, Eq b d, Eq b b, Eq f g, Eq f h]

        abcd     = [a, b, c, d]
        fgh      = [f, g, h]
        expected = [(a, abcd), (b, abcd), (c, abcd), (d, abcd),
                    (e, [e]),
                    (f, fgh), (g, fgh), (h, fgh)]

-- | The list of all terms equal to `x`, according to `eqs`
eqClosure :: [Equation] -> Term -> Seq.Seq Term
eqClosure eqs x = indirect eqs Seq.empty (directEq eqs x)

indirect :: [Equation] -> Seq.Seq Term -> Seq.Seq Term -> Seq.Seq Term
indirect eqs seen xs | null xs   = seen
indirect eqs seen xs | otherwise = indirect eqs (nub' $ seen Seq.>< unseen) unseen
  where new       = xs >>= directEq eqs
        unseen    = nub' $ Seq.filter notSeen new
        notSeen a = not (a `isElem` seen)

nub' = foldl f Seq.empty
  where f acc x = if x `isElem` acc
                     then acc
                     else x Seq.<| acc

isElem x xs = isJust (Seq.elemIndexL x xs)

-- | The list of terms equal to `x` by definition, according to `eqs`
directEq :: [Equation] -> Term -> Seq.Seq Term
directEq eqs x = x Seq.<| Seq.filter direct terms
  where terms            = Seq.fromList . nub . concatMap termsOf $ eqs
        termsOf (Eq a b) = [a, b]
        direct a         = Eq x a `elem` eqs || Eq a x `elem` eqs

canGetClassesFromEqs :: [Equation] -> _
canGetClassesFromEqs eqs = True
  where typeCheck = classesFromEqs eqs

canGetUnivFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doUniv' s) $$$ putTrue
                    in (e, ())

canGetCxtFromSig = testExec mkExpr endsInTrue
  where mkExpr s = let e = ((>>$) $$$ doCtx' s) $$$ putTrue
                    in (e, ())

canGetSigFromEqs eqs = case sigFromEqs eqs of
  Sig _ _ -> True

eqSigHasVars eqs = counterexample debug test
  where sig     = sigFromEqs eqs
        sigvars = sigVars sig
        eqvars  = concatMap eqVars eqs
        test    = setEq sigvars eqvars
        debug   = show (("eqs", eqs),
                        ("sigvars", sigvars),
                        ("eqvars",  eqvars),
                        ("sig",     sig))

eqSigHasConsts eqs = counterexample debug test
  where sig       = sigFromEqs eqs
        test      = setEq sigconsts eqconsts
        sigconsts = sigConsts sig
        eqconsts  = concatMap eqConsts eqs
        debug     = show (("eqs",       eqs),
                          ("sig",       sig),
                          ("sigconsts", sigconsts),
                          ("eqconsts",  eqconsts))

canRenderEqs = once . forAll (return <$> resize 3 arbitrary) $ canRenderEqs'

canRenderEqs' :: [Equation] -> _
canRenderEqs' eqs = testEval mkExpr haveEqs
  where mkExpr () = (expr, debug)
        expr      = unlines' $$$ shownEqs'
        sig'      = render (sigFromEqs eqs)
        shownEqs' = (map' $$$ (showEquation' $$$ sig')) $$$ eqs'
        eqs'      = unsafePerformIO' $$$ (prune eqs)
        debug     = (("eqs",  eqs),
                     ("sig'", sig'),
                     ("eqs'", eqs'))
        lToEq l   = unsafePerformIO $ do
                      print ("GOT LINE: " ++ l)
                      return (lToEq' l)
        lToEq' l  = case eitherDecode' (S.fromString l) of
                         Left  e  -> error e
                         Right eq -> eq
        keep ('D':'e':'p':'t':'h':_) = False
        keep _ = True
        haveEqs Nothing  = error "Failed to eval"
        haveEqs (Just s) = setEq (map lToEq (filter keep (lines s)))
                                 eqs

-- Helpers

setEq xs ys = all (`elem` xs) ys && all (`elem` ys) xs

endsInTrue x = case x of
  Nothing -> False
  Just y  -> last (lines y) == "True"

putTrue :: TypedExpr (IO ())
putTrue  = TE $ "putStr" $$ asString "True"

-- | Check that the generated `String` expressions satisfy the given predicate.
--   The type `b` is for any extra debug output to include in case of failure.
testEval :: (Arbitrary a, Show a, Show b) => (a -> (TypedExpr String, b))
                                          -> (Maybe String -> Bool)
                                          -> Property
testEval = testEval' (\(TE e) -> eval e)

-- | Check that the output of the generated `IO` actions satifies the given
--   predicate. `b` is for extra debug output to include in case of failure.
testExec :: (Arbitrary a, Show a, Show b) => (a -> (TypedExpr (IO e), b))
                                           -> (Maybe String -> Bool)
                                           -> Property
testExec = testEval' exec

-- | Takes an expression-evaluating function, an expression-generating function
--   (`b` is any debug output we should include in case of failure), an
--   output-checking function and tests whether the output of evaluating the
--   generated expressions passes the checker.
testEval' :: (Arbitrary a, Show a, Show b) => (TypedExpr e -> IO (Maybe String))
                                            -> (a -> (TypedExpr e, b))
                                            -> (Maybe String -> Bool)
                                            -> Property
testEval' evl mkExpr expect = forAll (resize 10 arbitrary) go
  where go arg = once $ monadicIO $ do
                   let (e, dbg) = mkExpr arg
                   result <- run (evl e)
                   monitor . counterexample . show $ (("expr",   e),
                                                      ("result", result),
                                                      ("debug",  dbg))
                   assert (expect result)

constantSymbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
constantSymbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $
                                           "constantSymbols"

variableSymbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
variableSymbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $
                                           "variableSymbols"

-- Data generators

-- Example input from files

exampleEqs :: [[Object]]
exampleEqs = map parse exampleJson
  where parse x = fromMaybe (error ("Failed to parse JSON: " ++ x)) (decode (pack x))

exampleJson :: [String]
{-# NOINLINE exampleJson #-}
exampleJson = unsafePerformIO $ exampleFiles >>= mapM readFile

exampleDir = "test/data"

exampleFiles = do
    fs <- getDirectoryContents exampleDir
    return (prefix (json fs))
  where prefix   = map ((exampleDir ++ "/") ++)
        json     = filter isJson
        isJson :: String -> Bool
        isJson x = reverse ".json" == take 5 (reverse x)

withExamples = forAll (elements exampleEqs)

-- Random input generators

instance Arbitrary Equation where
  arbitrary = Eq <$> arbitrary <*> arbitrary
  shrink (Eq l r) = [Eq l' r' | (l', r') <- shrink (l, r)]

instance Arbitrary Term where
  arbitrary = oneof [App <$> arbitrary <*> arbitrary,
                     C   <$> arbitrary,
                     V   <$> arbitrary]
  shrink (C c)     = C <$> shrink c
  shrink (V v)     = V <$> shrink v
  shrink (App l r) = [l, r] ++ [App l' r' | (l', r') <- shrink (l, r)]

instance Arbitrary Var where
  arbitrary = sized $ \n -> do
    arity <- elements [0, 1, 2]
    typ   <- naryType arity n
    index <- elements [0, 1, 2]
    return $ Var (Type typ) index (Arity arity)

instance Arbitrary Const where
  arbitrary = sized $ \n -> do
    arity <- elements [0..5]
    name  <- listOf1 (arbitrary `suchThat` (`notElem` ("\n\r" :: String)))
    typ   <- naryType arity n
    return $ Const (Arity arity) (Name name) (Type typ)

instance Arbitrary Sig where
  arbitrary = Sig <$> listOf arbitrary <*> listOf arbitrary
  shrink (Sig [] []) = []
  shrink (Sig cs vs) = Sig [] [] : [Sig cs' vs' | (cs', vs') <- shrink (cs, vs)]

instance Arbitrary Type where
  arbitrary = Type <$> sized sizedType

sizedType :: Int -> Gen String
sizedType 0 = elements ["Int", "Bool", "Float"]
sizedType n = oneof [
    sizedType 0,
    do x <- sizedType (n - 1)
       return $ "[" ++ x ++ "]",
    do n' <- choose (0, n - 1)
       l  <- sizedType n'
       r  <- sizedType (n - n')
       return $ "(" ++ l ++ ", " ++ r ++ ")"
  ]

naryType 0 n = sizedType n
naryType a n = do
  arg <- sizedType n
  ret <- naryType (a-1) n
  return $ "(" ++ arg ++ ") -> (" ++ ret ++ ")"
