{-# LANGUAGE BangPatterns, OverloadedStrings, PartialTypeSignatures, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Main where

import           Data.Aeson
import qualified Data.ByteString              as B
import qualified Data.ByteString.Lazy         as LB
import           Data.Char
import           Data.List
import           Data.Maybe
import qualified Data.Sequence                as Seq
import qualified Data.Stringable              as S
import qualified Data.String                  as DS
import           Data.Text.Encoding
import           Language.Eval.Internal
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
import           Math.Equation.Internal
import           Math.Equation.Reduce
import           System.Directory
import           System.IO.Unsafe
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import qualified Test.QuickSpec.Signature
import qualified Test.QuickSpec.Term
import           Test.Tasty            (defaultMain, testGroup, localOption)
import           Test.Tasty.QuickCheck

main = defaultMain $ testGroup "All tests" [
    testProperty "Can parse equations"          canParseEquations
  , testProperty "Can parse terms"              canParseTerms
  , testProperty "Can parse variables"          canParseVars
  , testProperty "Can parse constants"          canParseConsts
  , testProperty "Can parse examples"           canParseExamples
  , testProperty "Can evaluate examples"        canEvalExamples
  , testProperty "Can make example signature"   canMakeSignature
  , testProperty "Constants added"              constantsAdded
  , testProperty "Variables added"              variablesAdded
  , testProperty "Sigs render"                  sigsRender
  , testProperty "Sigs have constants"          sigsHaveConsts
  , testProperty "Sigs have variables"          sigsHaveVars
  , testProperty "Constants are distinct"       sigConstsUniqueIndices
  , testProperty "Variables are distinct"       sigVarsUniqueIndices
  , testProperty "Can find closure of term"     canFindClosure
  , testProperty "No classes without equations" noClassesFromEmptyEqs
  , testProperty "Equation induces a class"     oneClassFromEq
  , testProperty "Classes contain given terms"  classesHaveTerms
  , testProperty "Equal terms in same class"    eqPartsAppearInSameClass
  , testProperty "Terms appear in one class"    classesHaveNoDupes
  , testProperty "Class elements are equal"     classElementsAreEqual
  , testProperty "Non-equal elements separate"  nonEqualElementsSeparate
  , testProperty "Classes have one arity"       classHasSameArity
  , testProperty "Class length more than one"   classesNotSingletons
  , testProperty "Can get classes from sig"     canGetClassesFromEqs
  , testProperty "Can get sig from equations"   canGetSigFromEqs
  , testProperty "Sig has equation variables"   eqSigHasVars
  , testProperty "Sig has equation constants"   eqSigHasConsts
  , testProperty "Equations have one arity"     equationsHaveSameArity
  , testProperty "Can render equations"         canRenderEqs
  , testProperty "Can get type of terms"        canGetTermType
  , testProperty "No trivial terms"             noTrivialTerms
  , testProperty "Equations are consistent"     eqsAreConsistent
  , testProperty "Switch function types"        switchFunctionTypes
  , testProperty "Can generate eq variables"    canMakeVars
  , testProperty "Can generate var QS sigs"     canMakeQSSigs
  , testProperty "Can find vars in sig"         lookupVars
  , testProperty "Can prune"                    justPrune
  , testProperty "New reduce"                   newReduce
  , testProperty "Can prune equations"          canPruneEqs
  , testProperty "Type parsing regression"      regressionTypeParse
  ]

-- Tests

genNormalisedVar = do
  eqs' <- genNormalisedEqs
  case sigFromEqs eqs' of
       Sig _ []    -> discard
       Sig _ (v:_) -> return v

genNormalisedEqs = do
  eqs <- arbitrary
  let (_, eqs') = replaceTypes eqs
  return eqs'

canMakeVars = do
  v <- genNormalisedVar
  return True

canMakeQSSigs = do
  v <- genNormalisedVar
  let sig = renderQSVars [v]
  return (length (show sig) > 0)

lookupVars = once $ do
  eqs <- resize 42 genEqsWithVars
  let Sig _ vs  = sigFromEqs eqs'
      (_, eqs') = replaceTypes eqs
  v <- elements vs
  let expectName = unName (varName v)
      sig        = renderQSVars [v]
      symbol     = sigToSymN (V v) sig
      foundName  = Test.QuickSpec.Term.name symbol
  return (expectName == foundName)

genEqsWithVars = arbitrary `suchThat` hasVars
  where hasVars eqs = case sigFromEqs eqs of
          Sig _ [] -> False
          _        -> True

justPrune = once $ do
    eqs <- resize 20 arbitrary
    let (_, eqs') = replaceTypes eqs
        o = pruneEqsN eqs'
    return (length o >= 0)

newReduce = once (forAll (resize 20 arbitrary) newReduce')
newReduce' eqs = monadicIO $ do
  result <- run $ reductionN eqs
  monitor . counterexample . show $ (("eqs",    eqs),
                                     ("result", result))
  assert (length (show result) > 0)

canParseEquations = all try [
      "{\"relation\":\"~=\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}},\"rhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}}}",
      "{\"relation\":\"~=\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":8}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":8}},\"rhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}}}"
    ]
  where try x = case decode x of
                     Nothing       -> False
                     Just (Eq l r) -> True

canParseTerms = all try [
      "{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"}",
      "{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}",
      "{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}",
      "{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":8}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":8}}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}}",
      "{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":8}},\"rhs\":{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":8}}"
    ]
  where try x = case decode x :: Maybe Term of
                     Nothing -> error ("Couldn't decode " ++ S.toString x)
                     Just _  -> True

canParseVars = all try [
      "{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":7}",
      "{\"role\":\"variable\",\"type\":\"[Integer]\",\"id\":6}"
    ]
  where try x = case decode x :: Maybe Var of
          Nothing -> error ("Couldn't decode " ++ S.toString x)
          Just _  -> True

canParseConsts = all try [
      "{\"role\":\"constant\",\"type\":\"[Integer] -> [Integer] -> Ordering\",\"symbol\":\"lengthCompare\"}"
    ]
  where try x = case decode x :: Maybe Const of
          Nothing -> error ("Couldn't decode " ++ S.toString x)
          Just _  -> True

canParseExamples = not (null exampleEqs)

canEvalExamples = withExamples allStrict
  where allStrict = foldr ((&&) . strict) True
        strict (Eq !l !r) = True

canMakeSignature = withExamples makeSig
  where makeSig xs = case sigFromEqs xs of
                          Sig !cs !vs -> True

constantsAdded cs s = case withConsts cs s of
  Sig cs' _ -> all (`elem` cs') cs

variablesAdded vs s = case withVars vs s of
  Sig _ vs' -> all (`elem` vs') vs

sigsRender = once $ do
    eqs <- resize 20 genNormalisedEqs
    let sig = sigFromEqs eqs
        s   = show (renderN sig :: Test.QuickSpec.Signature.Sig)
    return (length s >= 0)

sigsHaveConsts = once $ do
  eqs <- resize 42 genNormalisedEqs
  let s@(Sig cs vs) = sigFromEqs eqs
      rendered      = renderN s
      consts        = Test.QuickSpec.Signature.constantSymbols rendered
      names         = map constName cs
  return (checkNames names consts)

sigsHaveVars = once (forAll (resize 42 genNormalisedEqs) sigsHaveVars')
sigsHaveVars' eqs =
  let s@(Sig _ vs) = sigFromEqs eqs

      rendered = renderN s

      variables = Test.QuickSpec.Signature.variableSymbols rendered

      hasVars :: Bool
      hasVars = checkVars variables

      checkVars  = checkNames names
      names      = map varName vs
      foundNames = map Test.QuickSpec.Term.name variables
      dbg        = show (--("eqs",   eqs),
                         --("s",     s),
                         ("expect names", names),
                         ("found names", foundNames)
                         --("vs",    vs)
                        )
  in counterexample dbg (return hasVars :: Gen Bool)

sigConstsUniqueIndices = doOnce sigConstsUniqueIndices'

-- Use `c` to generate a bunch of similar constants `consts`, add them to `s` to
-- get `sig`. Render `sig` to a QuickSpec signature, then print out its constant
-- symbols and compare with those of `sig`.
sigConstsUniqueIndices' s (Const a (Name n') t) = testEval mkExpr hasConsts
  where n = 'x' : n'  -- Avoid issues with linefeed being cut off
        mkExpr () = let syms  = constantSymbols' $$$ render sig
                        names = (map' $$$ name') $$$ syms
                        e     = unlines' $$$ names
                     in (e, (("consts",    consts),
                             ("sigconsts", sigConsts sig)))
        hasConsts Nothing    = error "Failed to evaluate"
        hasConsts (Just out) = setEq (map Name (lines out))
                                     (map constName (sigConsts sig))
        consts = [Const a (Name (n ++ show i)) t | i <- [0..10]]
        sig    = withConsts consts s

sigVarsUniqueIndices :: Property
sigVarsUniqueIndices = once (property sigVarsUniqueIndices')

-- Use `v` to generate a bunch of `Var`s of the same type, `vars`, add them to
-- `s` to get `sig`. Render `sig` to a QuickSpec signature, then print out its
-- variable symbols and compare with those of `sig`.
sigVarsUniqueIndices' :: Sig -> Var -> Property
sigVarsUniqueIndices' s (Var t _ a) = testEval mkExpr hasVars
  where mkExpr :: () -> (TypedExpr String, _)
        mkExpr () = let syms  = variableSymbols' $$$ render sig
                        names = (map' $$$ name') $$$ syms
                        e     = unlines' $$$ names
                     in (e, (("vars" :: String, vars),
                             ("sig"  :: String, sig)))
        hasVars :: Maybe String -> Bool
        hasVars Nothing    = error "Failed to evaluate"
        hasVars (Just out) = setEq (map Name (readVars out))
                                   (map varName (sigVars sig))
        vars = [Var t i a | i <- [0..10]]
        sig  = withVars vars s

-- Some vars get split over multiple lines
readVars s = accumulate [] (lines s)
  where accumulate (v:vs) (l@(' ':_):ls) = accumulate ((v ++ l):vs) ls
        accumulate    vs  (l        :ls) = accumulate       (l :vs) ls
        accumulate    vs  []             = vs

noClassesFromEmptyEqs = null (classesFromEqs [])

oneClassFromEq eq = length (classesFromEqs [eq]) == 1

classesHaveTerms eqs = found `all` terms
  where terms            = concatMap termsOf eqs
        termsOf (Eq l r) = [l, r]
        found t          = (t `elem`) `any` classes
        classes          = classesFromEqs eqs

eqPartsAppearInSameClass eqs = counterexample (show debug) test
  where test                        = all eqPartsInSameClass eqs
        classes                     = classesFromEqs eqs
        matchingClass t             = head $ filter (t `elem`) classes
        eqPartsInSameClass (Eq l r) = r `elem` matchingClass l &&
                                      l `elem` matchingClass r
        debug                       = (("eqs", eqs), ("classes", classes))

classesHaveNoDupes eqs = counterexample (show debug) test
  where test         = all appearOnce terms
        classes      = classesFromEqs eqs
        terms        = concat classes
        appearOnce t = length (filter (t `elem`) classes) == 1
        debug        = (("eqs", eqs), ("classes", classes), ("terms", terms))

classHasSameArity eqs = all oneArity classes
  where classes     = classesFromEqs eqs
        oneArity ts = length (nub (map termArity ts)) == 1

equationsHaveSameArity (Eqs eqs) = all sameArity eqs
  where sameArity (Eq l r) = termArity l == termArity r

nonEqualElementsSeparate ty = forAll (iterable ty) nonEqualElementsSeparate'

nonEqualElementsSeparate' (t, v) = match classes expected && match expected classes
  where (a:b:c:d:e:f:_) = map extend [0..]

        extend 0 = t
        extend n = app v (extend (n-1))

        eqs = [Eq a b, Eq b c, Eq d e, Eq e f]

        classes = classesFromEqs eqs

        expected = [[a, b, c], [d, e, f]]

        match xs ys = all (\x -> any (setEq x) ys) xs

classElementsAreEqual = once (forAll (resize 42 arbitrary) classElementsAreEqual')
classElementsAreEqual' (Eqs eqs) = all elementsAreEqual classes
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

classesNotSingletons (Eqs eqs) = all nonSingle classes
  where nonSingle c = length c > 1
        classes     = classesFromEqs eqs

canFindClosure ty = forAll (iterable ty) canFindClosure'

canFindClosure' (t, v) = all match expected
  where -- Generate unique terms by wrapping in "app c"
        (a:b:c:d:e:f:g:h:_) = map extend [0..]
        extend 0 = t
        extend n = app v (extend (n-1))

        match (x, xs) = setEq (eqClosure eqs x) xs

        eqs = [Eq a b, Eq a c, Eq b d, Eq b b, Eq f g, Eq f h]

        abcd     = [a, b, c, d]
        fgh      = [f, g, h]
        expected = [(a, abcd), (b, abcd), (c, abcd), (d, abcd),
                    (e, [e]),
                    (f, fgh), (g, fgh), (h, fgh)]

canGetClassesFromEqs (Eqs eqs) = True
  where typeCheck = classesFromEqs eqs

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

canRenderEqs = doOnce canRenderEqs'

canRenderEqs' (Eqs eqs) = run
  where run          = testEval mkExpr haveEqs
        mkExpr ()    = (indent expr, debug)
        expr         = renderWithSig (WS (unlines' $$$ shownEqs')) sig
        sig          = sigFromEqs eqs
        WS shownEqs' = WS ((map' $$$ (showEquation' $$$ "givenSig")) $$$ eqs')
        WS eqs'      = renderEqs eqs
        debug        = (("eqs",  eqs),
                        ("sig",  sig),
                        ("eqs'", eqs'))
        haveEqs Nothing  = error "Failed to eval"
        haveEqs (Just s) = length (filter ("==" `isInfixOf`) (lines s)) == length eqs

canPruneEqs = once (forAll (resize 20 arbitrary) canPruneEqs')
canPruneEqs' (Eqs eqs) = monadicIO $ do
    eqs' <- run $ reductionN eqs
    monitor (counterexample (show (("eqs", eqs), ("eqs'", eqs'))))
    assert (expected eqs')
  where expected []     =      null eqs -- No output when no eqs
        expected (x:xs) = not (null eqs)

canGetTermType input output = expected (termType' term)
  where term  = app (C (Const undefined undefined func))
                    (C (Const undefined undefined input))
        func  = tyFun input output
        strip = filter (/= ' ')
        expected t = strip (typeName t) === strip (typeName output)

noTrivialTerms t = forAll (termOfType t) (not . trivial)

eqsAreConsistent (Eqs eqs) = consistentEqs eqs

-- Given 'i' and 'o', we should be able to replace 'i -> o'
switchFunctionTypes i1 i2 o1 o2 = check <$> termOfType (HSE.Syntax.TyFun () i1 o1)
  where db      = [(i1, i2), (o1, o2)]
        check f = let [Eq lhs rhs] = restoreTypes db [replaceEqTypes db (Eq f f)]
                   in termType lhs == termType rhs

regressionTypeParse = once . monadicIO $ do
    result <- run $ parseAndReduceN ex
    assert (LB.length (encode result) > 0)
  where ex = "{\"relation\":\"~=\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"List Integer -> List Integer\",\"symbol\":\"reverse\"},\"rhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"Integer -> List Integer -> List Integer\",\"symbol\":\"cCons\"},\"rhs\":{\"role\":\"variable\",\"type\":\"Integer\",\"id\":3}},\"rhs\":{\"role\":\"constant\",\"type\":\"List Integer\",\"symbol\":\"cNil\"}}},\"rhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"Integer -> List Integer -> List Integer\",\"symbol\":\"cCons\"},\"rhs\":{\"role\":\"variable\",\"type\":\"Integer\",\"id\":3}},\"rhs\":{\"role\":\"constant\",\"type\":\"List Integer\",\"symbol\":\"cNil\"}}}"

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
testEval' evl mkExpr expect = once $ monadicIO $ do
  arg <- run (generate arbitrary)
  monitor . counterexample . show $ ("arg", arg)
  let (e, dbg) = mkExpr arg
  result <- run (evl (indent e))
  monitor . counterexample . show $ (("expr",   e),
                                     ("result", result),
                                     ("debug",  dbg))
  assert (expect result)

indent (TE e) = TE (withPkgs ["hindent"] e)

constantSymbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
constantSymbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $
                                           "constantSymbols"

variableSymbols' :: TypedExpr (QSSig -> [Test.QuickSpec.Term.Symbol])
variableSymbols' = TE . withQS . qualified "Test.QuickSpec.Signature" $
                                           "variableSymbols"

-- Data generators

-- Example input from files

exampleEqs :: [[Equation]]
exampleEqs = map (parseLines . S.fromString) exampleJson

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

newtype Equations = Eqs [Equation] deriving (Show, Eq)

instance Arbitrary Equations where
  shrink (Eqs [])  = []
  shrink (Eqs eqs) = [Eqs eqs' | eqs' <- shrink eqs, consistentEqs eqs']

  arbitrary = do
      eqs  <- arbitrary
      eqs' <- renameEqs eqs
      return (Eqs eqs')

-- | Keep renaming constants until each name only refers to one type
renameEqs eqs = if consistentEqs eqs
                   then return eqs
                   else mapM renameEq eqs >>= renameEqs
  where renameEq (Eq l r) = Eq <$> renameTerm l <*> renameTerm r
        renameTerm (C (Const a _ t)) = C <$> (Const a <$> arbitrary <*> pure t)
        renameTerm (V v)             = pure (V v)
        renameTerm (App l r _)       = app <$> renameTerm l <*> renameTerm r

consistentEqs eqs = let nts = concatMap eqNames eqs
                     in consistentNames nts

instance Arbitrary Equation where
  arbitrary = do t <- arbitrary
                 l <- termOfType t
                 r <- termOfType t
                 if trivial l && trivial r || l == r || allVar l || allVar r
                    then discard
                    else return $ Eq l r

  shrink (Eq l r) = [Eq l' r' | (l', r') <- shrink (l, r),
                     not (trivial l' && trivial r'),
                     not (allVar l'),
                     not (allVar r'),
                     termType' l' == termType' r']

-- | Generate a "non-trivial" Term, i.e. containing at least one App, one Const
--   and one Var, with the given Type
termOfType :: Type -> Gen Term
termOfType t = do
  -- Generate a random Term of the correct type, of the form `app l r`
  term <- appOfTypeArity 0 t
  -- Force one branch to contain a Var and the other to contain a Const
  giveVarConst term

-- | Force one branch of an `App` to contain a Const and the other to contain a
--   Var
giveVarConst (App l r _) = do
  which <- arbitrary
  l'    <- if     which then giveVar l else giveConst l
  r'    <- if not which then giveVar r else giveConst r
  return (app l' r')

-- | Randomly replace part of the given Term with a Var
giveVar :: Term -> Gen Term

-- If the Term is already a Var, there is no work to do
giveVar (V v) = return (V v)

-- Turn Consts into Vars. Since Consts may have higher arity (up to 5) than Vars
-- (up to 2), we rely on the App cases to prevent hitting high-arity Terms
giveVar (C c) = V <$> varOfTypeArity (constArity c) (constType c)

-- Don't recurse any further if we reach an arity of 2, since we might reach a
-- sub-Term with an arity above 2, which cannot be turned into a Var
giveVar t | termArity t >= 2 = V <$> varOfTypeArity (termArity t)
                                                    (termType' t)

-- If it's safe to recurse, choose a branch at random to force a Var into
giveVar (App l r _) = do
  which <- arbitrary
  l'    <- if     which then giveVar l else return l
  r'    <- if not which then giveVar r else return r
  return (app l' r')

-- | Randomly replace part of a Term with a Const
giveConst :: Term -> Gen Term

-- Constants can just be returned as-is
giveConst (C c) = return (C c)

-- Variable arity should always be lower than 3, which a Const should have no
-- problem with
giveConst (V v) = C <$> constOfTypeArity (varArity v) (varType v)

-- Don't recurse into Terms with arity 5, since we might hit a Term with a
-- higher arity which we can't replace with a Const
giveConst t | termArity t >= 5 = C <$> constOfTypeArity (termArity t)
                                                        (termType' t)

-- It's safe to recurse into low-arity Apps. We pick a branch randomly to put a
-- Const into
giveConst (App l r _) = do
  which <- arbitrary
  l'    <- if     which then giveConst l else return l
  r'    <- if not which then giveConst r else return r
  return (app l' r')

constOfTypeArity :: Arity -> Type -> Gen Const
constOfTypeArity a t = if a > 5
  then error ("Can't make Const of type " ++ show t ++ " and arity " ++ show a)
  else Const a <$> arbitrary <*> pure t

varOfTypeArity :: Arity -> Type -> Gen Var
varOfTypeArity a t = if a > 2
  then error ("Can't make Var of type " ++ show t ++ " and arity " ++ show a)
  else Var t <$> choose (0, 4) <*> pure a

appOfTypeArity :: Arity -> Type -> Gen Term
appOfTypeArity a t = do
  arg <- arbitrary
  r   <- termOfTypeArity 0 arg
  l   <- termOfTypeArity (a+1) (tyFun arg t)
  return $ app l r

termOfTypeArity :: Arity -> Type -> Gen Term
termOfTypeArity a t = oneof (mkConst ++ mkVar ++ mkApp)
  where -- We can only generate constants up to arity 5
        mkConst = if a > 5
                     then error ("Can't gen Term of arity " ++ show a)
                     else [C <$> constOfTypeArity a t]

        -- We can only generate variables up to arity 2
        mkVar = if a > 2
                   then []
                   else [V <$> varOfTypeArity a t]

        mkApp = if a > 4
                   then []
                   else [appOfTypeArity a t]

-- "Trivial" equations will be pruned, so we need to avoid generating (or
-- shrinking down to) equations where both sides only have one symbol, or which
-- don't contain any variables
trivial (C _)                = True
trivial (V _)                = True
trivial x | not (hasVar   x) = True
trivial x | not (hasConst x) = True
trivial x                    = False

hasConst (V _)       = False
hasConst (C _)       = True
hasConst (App l r _) = hasConst l || hasConst r

hasVar (V _)       = True
hasVar (C _)       = False
hasVar (App l r _) = hasVar l || hasVar r

allVar (V _)       = True
allVar (C _)       = False
allVar (App l r _) = allVar l && allVar r

-- | Make sure no name is used for constants of two types
termNames :: Term -> [(Name, Type)]
termNames (C (Const _ n t)) = [(n, t)]
termNames (V _)             = []
termNames (App l r _)       = nub (termNames l ++ termNames r)

eqNames :: Equation -> [(Name, Type)]
eqNames (Eq l r) = termNames l ++ termNames r

consistentNames nts = all hasOneType names
  where names        = map fst nts
        hasOneType n = length (typesOf n) == 1
        typesOf    n = nub (map snd (entriesOf n))
        entriesOf  n = filter ((== n) . fst) nts

instance Arbitrary Term where
  arbitrary = do
    t <- arbitrary
    termOfType t

  shrink (C c)         = C <$> shrink c
  shrink (V v)         = V <$> shrink v
  shrink t@(App l r _) = C (Const (termArity t) (termName t) (termType' t)) :
                         [app l' r' | (l', r') <- shrink (l, r)]

termName (C c)       = constName c
termName (V v)       = Name (filter isAlpha (show (varType v) ++ show (varArity v)))
termName (App l r _) = let Name l' = termName l
                           Name r' = termName r
                        in Name ("app" ++ l' ++ r')

instance Arbitrary Var where
  arbitrary = sized $ \n -> do
    arity <- elements [0, 1, 2]
    typ   <- naryType arity n
    index <- elements [0, 1, 2]
    return $ Var typ index (Arity arity)

  shrink (Var t i a) = if i == 0
                          then []
                          else [Var t 0 a]

instance Arbitrary Const where
  arbitrary = sized $ \n -> do
    arity <- elements [0..5]
    name  <- arbitrary
    typ   <- naryType arity n
    return $ Const (Arity arity) name typ

  shrink (Const a n t) = do n' <- shrink n
                            return (Const a n' t)

instance Arbitrary Sig where
  arbitrary = Sig <$> listOf arbitrary <*> listOf arbitrary
  shrink (Sig [] []) = []
  shrink (Sig cs vs) = Sig [] [] : [Sig cs' vs' | (cs', vs') <- shrink (cs, vs)]

instance Arbitrary Type where
  arbitrary = sized sizedType

instance Arbitrary Name where
  arbitrary = Name <$> listOf1 (arbitrary `suchThat` isAlpha `suchThat` isAscii) `suchThat` valid
    where valid s = let t = S.fromString s
                        b = S.fromString s
                     in s == S.toString b   &&
                        s == S.toString t   &&
                        b == S.fromString s &&
                        b == encodeUtf8 t   &&
                        t == S.fromString s &&
                        t == decodeUtf8 b

  shrink (Name x) = let suffices = tail (tails x)
                        nonEmpty = filter (not . null) suffices
                        names    = map Name nonEmpty
                     in reverse names -- Try shortest first

sizedType :: Int -> Gen Type
sizedType 0 = elements [tyCon "Int", tyCon "Bool", tyCon "Float"]
sizedType n = oneof [
    sizedType 0,
    do x <- sizedType (n - 1)
       return $ tyCon ("[" ++ typeName x ++ "]"),
    do n' <- choose (0, n - 1)
       l  <- sizedType n'
       r  <- sizedType (n - n')
       return $ tyCon ("(" ++ typeName l ++ ", " ++ typeName r ++ ")")
  ]

naryType 0 n = sizedType n
naryType a n = do
  arg <- sizedType n
  ret <- naryType (a-1) n
  return $ tyFun arg ret

dbg :: (Show a, Monad m) => a -> PropertyM m ()
dbg = monitor . counterexample . show

doOnce :: (Show a, Arbitrary a, Testable prop) => (a -> prop) -> Property
doOnce = once . forAll (resize 42 arbitrary)

-- | The list of all terms equal to `x`, according to `eqs`
eqClosure :: [Equation] -> Term -> Seq.Seq Term
eqClosure eqs x = indirect eqs Seq.empty (directEq eqs x)

indirect :: [Equation] -> Seq.Seq Term -> Seq.Seq Term -> Seq.Seq Term
indirect eqs seen xs | null xs = seen
indirect eqs seen xs           = indirect eqs (nub' $ seen Seq.>< unseen) unseen
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

app l r = case termType l of
    Just (HSE.Syntax.TyFun _ _ o) -> App l r (Just o)
    _                             -> x
  where [Eq x _] = setAllTypes [Eq (App l r Nothing)
                                   (App l r Nothing)]

iterable ty = do t <- termOfType ty
                 v <- termOfType (tyFun ty ty)
                 return (t, v)

tyFun = HSE.Syntax.TyFun ()
