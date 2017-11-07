{-# LANGUAGE BangPatterns, OverloadedStrings, PartialTypeSignatures,
    ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances,
    FlexibleContexts #-}

module Main where

import           Control.DeepSeq (deepseq)
import           Control.Monad
import           Data.Aeson
import qualified Data.ByteString              as B
import qualified Data.ByteString.Lazy         as LB
import           Data.Char
import           Data.List
import           Data.Maybe
import qualified Data.Sequence                as Seq
import qualified Data.Stringable              as S
import qualified Data.String                  as DS
import           Data.String.Utils
import           Data.Text.Encoding
import           Data.Typeable
import qualified Language.Haskell.Exts.Parser as HSE.Parser
import qualified Language.Haskell.Exts.Syntax as HSE.Syntax
import           Algebra.Equation.Internal
import           Algebra.Equation.Reduce
import           Numeric.Natural
import           System.Directory
import           System.IO.Unsafe
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import qualified Test.QuickSpec.Equation
import qualified Test.QuickSpec.Generate
import qualified Test.QuickSpec.Main
import qualified Test.QuickSpec.Reasoning.CongruenceClosure
import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning
import qualified Test.QuickSpec.Signature
import qualified Test.QuickSpec.TestTree
import qualified Test.QuickSpec.Utils.Typeable
import qualified Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap
import qualified Test.QuickSpec.Term
import           Test.Tasty (defaultMain, testGroup, localOption)
import           Test.Tasty.QuickCheck

main = defaultMain $ testGroup "All tests" [
    testProperty "Can parse equations"             canParseEquations
  , testProperty "Can parse terms"                 canParseTerms
  , testProperty "Can parse variables"             canParseVars
  , testProperty "Can parse constants"             canParseConsts
  , testProperty "Can parse examples"              canParseExamples
  , testProperty "Can evaluate examples"           canEvalExamples
  , testProperty "Can make example signature"      canMakeSignature
  , testProperty "Constants added"                 constantsAdded
  , testProperty "Variables added"                 variablesAdded
  , testProperty "Sigs render"                     sigsRender
  , testProperty "Sigs have constants"             sigsHaveConsts
  , testProperty "Sigs have variables"             sigsHaveVars
  , testProperty "Constants are distinct"          sigConstsUniqueIndices
  , testProperty "Variables are distinct"          sigVarsUniqueIndices
  , testProperty "No classes without equations"    noClassesFromEmptyEqs
  , testProperty "Equation induces a class"        getClassFromEq
  , testProperty "Classes contain given terms"     classesHaveTerms
  , testProperty "Equal terms in same class"       eqPartsAppearInSameClass
  , testProperty "Terms appear in one class"       classesHaveNoDupes
  , testProperty "Classes have one arity"          classHasSameArity
  , testProperty "Equations have one arity"        equationsHaveSameArity
  , testProperty "Non-equal elements separate"     nonEqualElementsSeparate
  , testProperty "Class elements are equal"        classElementsAreEqual
  , testProperty "Class length more than one"      classesNotSingletons
  , testProperty "Can find closure of term"        canFindClosure
  , testProperty "Can get classes from sig"        canGetClassesFromEqs
  , testProperty "Can get sig from equations"      canGetSigFromEqs
  , testProperty "Sig has equation variables"      eqSigHasVars
  , testProperty "Sig has equation constants"      eqSigHasConsts
  , testProperty "Can prune equations"             canPruneEqs
  , testProperty "Can get type of terms"           canGetTermType
  , testProperty "No trivial terms"                noTrivialTerms
  , testProperty "Equations are consistent"        eqsAreConsistent
  , testProperty "Switch function types"           switchFunctionTypes
  , testProperty "Type parsing regression"         regressionTypeParse
  , testProperty "Nat example has eqs"             natHasEqs
  , testProperty "Nat example outputs eqs"         natKeepsEqs
  , testProperty "Nat classes are nontrivial"      natClassesNontrivial
  , testProperty "Commutativity is nontrivial"     commClassesNontrivial
  , testProperty "Nat equations are pruned"        natEqsPruned
  , testProperty "Reduction matches QuickSpec"     natEqsMatchQS
  , testProperty "Replacement types unique"        extractedTypesUnique
  , testProperty "QuickSpec conversions invert"    convertTypesIso
  , testProperty "Symmetric equations equal"       eqsSymmetric
  , testProperty "Spot symmetric equations"        eqsSetEq
  , testProperty "Can generate eq variables"       canMakeVars
  , testProperty "Can generate var QS sigs"        canMakeQSSigs
  , testProperty "Can find vars in sig"            lookupVars
  , testProperty "Can prune"                       justPrune
  , testProperty "New reduce"                      newReduce
  , testProperty "Reduce is idempotent"            reduceIdem
  , testProperty "Generated terms have type"       termsHaveType
  , testProperty "Manual Nat finds eqs"            manualNatFindsEqs
  , testProperty "Fresh sig + parsed eqs works"    manualNatAllowsGiven
  , testProperty "Fresh classes match parsed"      manualNatClassesMatch
  , testProperty "Fresh classes have parsed terms" topNatTermsFound
  , testProperty "Parsed classes have fresh terms" qsNatTermsFound
  , testProperty "Singleton classes generated"     natClassesIncludeSingletons
  , testProperty "Can prune converted equations"   convertPrunes
  , testProperty "Pruned eqs match"                parsedEqsPrune
  , testProperty "Fresh Nat reduces own eqs"       manualNatReducesSelf
  , testProperty "Show makes array"                showMakesArray
  ]

-- Tests

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
    s `deepseq` return True

sigsHaveConsts = once $ do
  eqs <- resize 42 genNormalisedEqs
  let s@(Sig cs vs) = sigFromEqs eqs
      rendered      = renderN s
      consts        = Test.QuickSpec.Signature.constantSymbols rendered
      names         = map constName cs
  return (checkNames names consts)

sigsHaveVars = once (forAllShrink (resize 42 genNormalisedEqs)
                                  shrink
                                  sigsHaveVars')
sigsHaveVars' eqs =
  let s@(Sig _ vs) = sigFromEqs eqs

      rendered = renderN s

      variables = Test.QuickSpec.Signature.variableSymbols rendered

      hasVars :: Bool
      hasVars = checkVars variables

      checkVars  = checkNames names
      names      = map varName vs
      foundNames = map Test.QuickSpec.Term.name variables
      dbg        = show (("expect names", names),
                         ("found names", foundNames))
  in counterexample dbg (return hasVars :: Gen Bool)

sigConstsUniqueIndices = once . resize 20 $ do
  s <- genNormalisedSig
  c <- genNormalisedConst
  return (sigConstsUniqueIndices' s c)

-- Use `c` to generate a bunch of similar constants `consts`, add them to `s` to
-- get `sig`. Render `sig` to a QuickSpec signature, then print out its constant
-- symbols and compare with those of `sig`.
sigConstsUniqueIndices' s (Const a (Name n) t) = hasConsts
  where syms      = Test.QuickSpec.Signature.constantSymbols (renderN sig)
        names     = map Test.QuickSpec.Term.name syms
        hasConsts = setEq (map Name names)
                          (map constName (sigConsts sig))
        consts    = [Const a (Name (n ++ show i)) t | i <- [0..10]]
        sig       = withConsts consts s

sigVarsUniqueIndices :: Property
sigVarsUniqueIndices = once $ resize 20 $ do
  s <- genNormalisedSig
  v <- genNormalisedVar
  return (sigVarsUniqueIndices' s v)

-- Use `v` to generate a bunch of `Var`s of the same type, `vars`, add them to
-- `s` to get `sig`. Render `sig` to a QuickSpec signature, then print out its
-- variable symbols and compare with those of `sig`.
sigVarsUniqueIndices' :: Sig -> Var -> Bool
sigVarsUniqueIndices' s (Var t _ a) = hasVars
  where syms    = Test.QuickSpec.Signature.variableSymbols (renderN sig)
        names   = map Test.QuickSpec.Term.name syms
        hasVars = setEq (map Name names)
                        (map varName (sigVars sig))
        vars    = [Var t i a | i <- [0..10]]
        sig     = withVars vars s

noClassesFromEmptyEqs = null (classesFromEqs [])

-- Sub-terms are added, which can make more than one class
getClassFromEq eq = show cls `deepseq` not (null cls)
  where cls = classesFromEqs [eq]

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

nonEqualElementsSeparate' (t, v) = all found expected
  where (a:b:c:d:e:f:_) = map extend [0..]

        extend 0 = t
        extend n = app v (extend (n-1))

        eqs = [Eq a b, Eq b c, Eq d e, Eq e f]

        classes = classesFromEqs eqs

        expected = [[a, b, c], [d, e, f]]

        found xs = any (setEq xs) classes

        match xs ys = all (\x -> any (setEq x) ys) xs

classElementsAreEqual = once (forAllShrink (resize 42 arbitrary)
                                           shrink
                                           classElementsAreEqual')
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

classesNotSingletons (Eqs eqs) = all nonSingle classes'
  where nonSingle c = length (nub c) > 1
        classes     = classesFromEqs eqs  -- All classes, even subterms
        classes'    = filter (\c -> any (`elem` c) terms) classes  -- Top-level
        terms       = getTerms [] eqs
        getTerms acc []          = acc
        getTerms acc (Eq l r:es) = getTerms (l:r:acc) es

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

canPruneEqs = once (forAllShrink (resize 20 arbitrary)
                                 shrink
                                 canPruneEqs')
canPruneEqs' (Eqs eqs) = counterexample (show (("eqs", eqs), ("eqs'", eqs')))
                                        (expected eqs')
  where expected []     =      null eqs -- No output when no eqs
        expected (x:xs) = not (null eqs)

        eqs' = reduction eqs

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

regressionTypeParse = LB.length (encode result) > 0
  where ex = "[{\"relation\":\"~=\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"List Integer -> List Integer\",\"symbol\":\"reverse\"},\"rhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"Integer -> List Integer -> List Integer\",\"symbol\":\"cCons\"},\"rhs\":{\"role\":\"variable\",\"type\":\"Integer\",\"id\":3}},\"rhs\":{\"role\":\"constant\",\"type\":\"List Integer\",\"symbol\":\"cNil\"}}},\"rhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"application\",\"lhs\":{\"role\":\"constant\",\"type\":\"Integer -> List Integer -> List Integer\",\"symbol\":\"cCons\"},\"rhs\":{\"role\":\"variable\",\"type\":\"Integer\",\"id\":3}},\"rhs\":{\"role\":\"constant\",\"type\":\"List Integer\",\"symbol\":\"cNil\"}}}]"
        result = parseAndReduce ex

natHasEqs = case eitherDecode rawNatEqs :: Either String [Equation] of
                 Left err  -> error err
                 Right []  -> error "No equations found"
                 Right eqs -> True

natKeepsEqs = case parseAndReduce rawNatEqs of
                   [] -> error "No equations found"
                   _  -> True

natClassesNontrivial =
  let raw = rawNatEqs
      rawEqs = parsedNatEqs
      (_, rawEqs') = replaceTypes rawEqs
      classes      = classesFromEqs rawEqs'
   in counterexample (show classes)
                     (any (\c -> length c > 2) classes)

commClassesNontrivial n1 n2 i o = once $
    counterexample (show (("eqs",  eqs),
                          ("clss", clss),
                          ("comm", comm)))
      (all ((> 1) . length . nub) clss')
  where f = C $ Const (Arity 2) n1 (HSE.Syntax.TyFun () i (HSE.Syntax.TyFun () i o))
        q = C $ Const (Arity 1) n2 (HSE.Syntax.TyFun () o o)
        x = V $ Var i 0 (Arity iArity)
        y = V $ Var i 1 (Arity iArity)

        iArity = countArity i

        (cl, cr) = (App (App f x Nothing) y Nothing, App (App f y Nothing) x Nothing)
        (ql, qr) = (App q (App (App f x Nothing) y Nothing) Nothing,
                    App q (App (App f y Nothing) x Nothing) Nothing)
        comm = Eq cl cr
        eqs  = [comm, Eq ql qr]

        clss  = classesFromEqs eqs
        clss' = filter topLevel clss
        topLevel c = any (`elem` c) [cl, cr, ql, qr]

natEqsPruned = length pruned < length rawEqs'
  where (_, rawEqs') = replaceTypes parsedNatEqs
        pruned       = pruneEqsN rawEqs'

natEqsMatchQS = once $ monadicIO $ do
  expect <- run $ LB.readFile "test/data/nat-simple-expect.json"
  let Right expectEqs = eitherDecode expect :: Either String [Equation]
      foundEqs = parseAndReduce rawNatEqs
      fLen = length foundEqs
      eLen = length expectEqs
  monitor . counterexample $ show (("foundEqs",  foundEqs),
                                   ("expectEqs", expectEqs),
                                   ("length foundEqs",  length foundEqs),
                                   ("length expectEqs", length expectEqs))
  assert (length foundEqs == length expectEqs)

extractedTypesUnique (Eqs eqs) = counterexample (show types)
                                                (nub types == types)
  where types = allTypes eqs

convertTypesIso = forAllShrink (resize 20 arbitrary)
                               shrink
                               (\x -> case convertTypesIso' x of
                                 ([],        [])        -> property True
                                 y@(extraEqs', extraConv) ->
                                   counterexample (show ("y", y))
                                                  (property False))
convertTypesIso' (Eqs eqs) =
  let (_, eqs') = replaceTypes eqs
      qsEqs     = Test.QuickSpec.Equation.equations qsClss
      sig       = renderN (sigFromEqs eqs')
      qsClss    = unSomeClassesN2 eqs' sig
      conv      = map (qsEqToEq . Test.QuickSpec.Utils.Typed.some Test.QuickSpec.Equation.eraseEquation) qsEqs
      conv'     = map (Test.QuickSpec.Utils.Typed.several
                        (map (qsTermToTerm . Test.QuickSpec.Term.term)))
                      qsClss
      clss      = classesFromEqs eqs'
      result    = setEq clss conv'
      cmp (Eq l1 r1) (Eq l2 r2) = (show l1 == show l2 && show r1 == show r2) ||
                                  (show l1 == show r2 && show r1 == show l2)
   in setDiffBy setEq clss conv'

eqsSymmetric [] = return True
eqsSymmetric eqs = do
  Eq l r <- elements eqs
  return (Eq r l `elem` eqs)

eqsSetEq eqs = setEq eqs (map swap eqs)
  where swap (Eq l r) = Eq r l

canMakeVars = do
  v <- genNormalisedVar
  return True

canMakeQSSigs = do
  v <- genNormalisedVar
  let sig = renderQSVars [v]
      str = show sig
  str `deepseq` return True

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

justPrune = once $ do
    eqs <- resize 20 arbitrary
    let (_, eqs') = replaceTypes eqs
        o = pruneEqsN eqs'
    show o `deepseq` return True

newReduce = once (forAllShrink (resize 20 arbitrary)
                               shrink
                               newReduce')

newReduce' (Eqs eqs) = counterexample (show (("eqs",    eqs),
                                             ("result", result)))
                                      (str `deepseq` True)
  where result = reduction eqs
        str    = show result

reduceIdem = once (forAllShrink (resize 20 arbitrary)
                                shrink
                                reduceIdem')
reduceIdem' (Eqs eqs) = setEq eqs' eqs''
  where eqs'  = reduction eqs
        eqs'' = reduction eqs'

termsHaveType ty = forAll (termOfType ty) checkType
  where checkType trm = termType (setForTerm trm) == Just ty

manualNatFindsEqs = once . monadicIO $ do
  -- Our raw equations, for comparison
  let rawEqs = parsedNatEqs
      clss   = rawNatClasses
      eqs    = Test.QuickSpec.Equation.equations clss
      eqs'   = dbgEqs eqs
  monitor . counterexample . show $ ("eqs'", eqs')

  -- Our golden input should match these
  assert (length eqs == length rawEqs)

manualNatAllowsGiven = counterexample (show eqs) check
  where check = not (null eqs) && length eqs <= length parsedNatEqs
        eqs   = unSomePruneN clss natSig
        clss  = sort (map (sort . mkUnSomeClassN natSig) clss')
        clss' = classesFromEqs naturalEqs

manualNatClassesMatch = counterexample dbg result
  where ourClss   = classesFromEqs naturalEqs
        ourClss'  = sort (map (sort . mkUnSomeClassN natSig) ourClss)
        ourClss'' = map (map Test.QuickSpec.Term.term) ourClss'

        result = setEq natNonTrivial ourClss''

        natNonTrivial = filter ((> 1) . length) natClasses

        dbg    = show (("qs non-trivial", length natNonTrivial),
                       ("our classes",    length ourClss''))

topNatTermsFound = all termInClasses (termsOf [] naturalEqs)
  where termsOf acc []          = acc
        termsOf acc (Eq l r:xs) = termsOf (l:r:acc) xs
        termInClasses t = let qs = any (renderTermN t natSig `elem`) natClasses
                              us = any (t `elem`) clss
                           in case (qs, us) of
                                (False, False) -> error $ show t ++ " not found in either"
                                (False, _)     -> error $ show t ++ " not in QS"
                                (_, False)     -> error $ show t ++ " not in ours"
                                _              -> True
        clss = classesFromEqs naturalEqs

qsNatTermsFound = case unfoundInOurs of
    [] -> True
    us -> error (show ("unfound", us))
  where allTerms = concat (filter ((> 1) . length) natClasses)

        clss = classesFromEqs naturalEqs

        inOurs t = any (t `elem`) (map (map (`renderTermN` natSig)) clss)

        unfoundInOurs = filter (not . inOurs) allTerms

natClassesIncludeSingletons = any ((== 1) . length) natClasses

convertPrunes = length (doPrune qsClasses natSig') == 10
  where qsClasses  = filter (Test.QuickSpec.Utils.Typed.several ((> 1) . length))
                            rawNatClasses'

-- We don't compare equations directly, since they may differ slightly e.g. due
-- to commutativity
parsedEqsPrune = nub [length ourPrune, length qsPrune] == [10]
  where (db, eqs') = replaceTypes parsedNatEqs
        ourPrune   = doPrune classes sig
        classes    = unSomeClassesN2 eqs' sig
        sig        = let sig'  = renderN (sigFromEqs eqs')
                         sig'' = Test.QuickSpec.Signature.signature sig'
                      in sig'' `mappend` Test.QuickSpec.Main.undefinedsSig sig''

        qsPrune    = doPrune rawNatClasses natSig

manualNatReducesSelf = counterexample (show ("pruned", pruned))
                                      ((length pruned < 20) &&
                                       (length pruned > 1))
  where pruned = doPrune rawNatClasses natSig

showMakesArray (Eqs eqs) = show (Eqs (go eqs)) `deepseq` True
  where go eqs = case eitherDecode (doReduce (encode eqs)) of
                   Left  err  -> error err
                   Right eqs' -> eqs'

-- Helpers

natSig = mconcat [
  Test.QuickSpec.Signature.fun0 "cZ"    (0    :: Natural),
  Test.QuickSpec.Signature.fun1 "cS"    ((+1) :: Natural -> Natural),
  Test.QuickSpec.Signature.fun2 "plus"  ((+)  :: Natural -> Natural -> Natural),
  Test.QuickSpec.Signature.fun2 "times" ((*)  :: Natural -> Natural -> Natural),
  Test.QuickSpec.Signature.gvars (map (\n -> "(var, Natural, " ++ show n ++ ")")
                                      [0, 1, 2])
    (((fromInteger . abs) <$> arbitrary) :: Gen Natural)]

natSig' = mconcat [
  Test.QuickSpec.Signature.fun0 "cZ"    (undefined :: Z),
  Test.QuickSpec.Signature.fun1 "cS"    (undefined :: Z -> Z),
  Test.QuickSpec.Signature.fun2 "plus"  (undefined :: Z -> Z -> Z),
  Test.QuickSpec.Signature.fun2 "times" (undefined :: Z -> Z -> Z),
  Test.QuickSpec.Signature.gvars (map (\n -> "(var, Z, " ++ show n ++ ")")
                                      [0, 1, 2])
    (return undefined :: Gen Z)]


genEqsWithVars = arbitrary `suchThat` hasVars
  where hasVars eqs = case sigFromEqs eqs of
          Sig _ [] -> False
          _        -> True

genNormalisedVar = do
  eqs' <- genNormalisedEqs
  case sigFromEqs eqs' of
       Sig _ []    -> scale (+1) genNormalisedVar
       Sig _ (v:_) -> return v

genNormalisedConst = do
  eqs' <- genNormalisedEqs
  case sigFromEqs eqs' of
       Sig []    _ -> scale (+1) genNormalisedConst
       Sig (c:_) _ -> return c

genNormalisedEqs = do
  eqs <- arbitrary
  let (_, eqs') = replaceTypes eqs
  return eqs'

genNormalisedSig = sigFromEqs <$> genNormalisedEqs

setEq :: (Foldable t1, Foldable t2, Eq a) => t1 a -> t2 a -> Bool
setEq = setEqBy (==)

setEqBy :: (Foldable t1, Foldable t2) => (a -> b -> Bool) -> t1 a -> t2 b -> Bool
setEqBy f xs ys = all (\y -> any (`f` y) xs) ys &&
                  all (\x -> any (x `f`) ys) xs

setDiff :: Eq a => [a] -> [a] -> ([a], [a])
setDiff = setDiffBy (==)

setDiffBy :: (a -> b -> Bool)
          -> [a]
          -> [b]
          -> ([a], [b])
setDiffBy f xs ys = (xs', ys')
  where xs' = filter (\x -> not (any (x `f`) ys)) xs
        ys' = filter (\y -> not (any (`f` y) xs)) ys

-- Data generators

-- Example input from files

exampleEqs :: [[Equation]]
exampleEqs = map (fromJust . decode) exampleJson

exampleJson :: [LB.ByteString]
{-# NOINLINE exampleJson #-}
exampleJson = unsafePerformIO $ exampleFiles >>= mapM LB.readFile

exampleDir = "test/data"

exampleFiles = do
    fs <- getDirectoryContents exampleDir
    return (prefix (json fs))
  where prefix   = map ((exampleDir ++ "/") ++)
        json     = filter isJson
        isJson :: String -> Bool
        isJson x = reverse ".json" == take 5 (reverse x)

withExamples = forAllShrink (elements exampleEqs) shrink

-- Random input generators

newtype Equations = Eqs [Equation] deriving (Show, Eq)

instance Arbitrary Equations where
  shrink (Eqs [])  = []
  shrink (Eqs eqs) = [Eqs eqs' | eqs' <- shrink eqs, consistentEqs eqs']

  arbitrary = do
      -- Make a bunch of terms and declare them equal
      classEqs <- scale (\s -> min 5 (s `div` 2)) (listOf mkClass)
      let eqs = concat classEqs

      -- Pad out with filler
      pre  <- scale (\s -> min 5 (s `div` 2)) arbitrary
      post <- scale (\s -> min 5 (s `div` 2)) arbitrary

      -- Make sure it's consistent
      eqs' <- renameEqs (pre ++ eqs ++ post)
      return (Eqs eqs')
    where mkClass = do
            t  <- arbitrary
            ts <- scale (`div` 2) (listOf (termOfType t))
            return $ case ts of
                          [] -> []
                          (x:xs) -> [Eq x y | y <- xs]

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
doOnce = once . forAllShrink (resize 42 arbitrary) shrink

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

instance Show Test.QuickSpec.Reasoning.NaiveEquationalReasoning.Context where
  show cxt = concat ["(context\n  (universe ",
                     show (Test.QuickSpec.Reasoning.NaiveEquationalReasoning.universe cxt),
                     ")\n  (maxDepth ",
                     show (Test.QuickSpec.Reasoning.NaiveEquationalReasoning.maxDepth cxt),
                     ")\n  (rel ",
                     show (Test.QuickSpec.Reasoning.NaiveEquationalReasoning.rel cxt),
                     ")\n)"]

instance Show Test.QuickSpec.Reasoning.CongruenceClosure.S where
  show s = concat ["(S\n  (funUse ",
                   show (Test.QuickSpec.Reasoning.CongruenceClosure.funUse s),
                   ")\n  (argUse ",
                   show (Test.QuickSpec.Reasoning.CongruenceClosure.argUse s),
                   ")\n  (lookup ",
                   show (Test.QuickSpec.Reasoning.CongruenceClosure.lookup s)
                   ]

dbgEqs = map (Test.QuickSpec.Utils.Typed.some
               (Test.QuickSpec.Equation.showTypedEquation natSig))

{-# NOINLINE rawNatEqs #-}
rawNatEqs = unsafePerformIO (LB.readFile "test/data/nat-simple-raw.json")

Right parsedNatEqs = eitherDecode rawNatEqs :: Either String [Equation]

(typeDb, parsedNatEqs') = replaceTypes parsedNatEqs

naturalEqs = map (replaceEqTypes [(tyCon "Nat", tyCon "Natural")])
                 parsedNatEqs

doReps = map (Test.QuickSpec.Utils.Typed.some2
               (Test.QuickSpec.Utils.Typed.tagged term . head))

natClasses = map (Test.QuickSpec.Utils.Typed.several
                   (map Test.QuickSpec.Term.term))
                 rawNatClasses


rawNatClasses' = swapTypes' naturalDb rawNatClasses

swapTypes' db = map (Test.QuickSpec.Utils.Typed.several
                      (\xs -> let trep = head (typeRepArgs (typeRep xs))  -- Strip off [] and Expr
                                  typ  = case HSE.Parser.parseType (show trep) of
                                    HSE.Parser.ParseOk x -> unwrapParens (void x)
                                  typ' = replaceInType db typ
                               in case getVal (getRep typ') of
                                    MkHT x -> Test.QuickSpec.Utils.Typed.Some
                                                (Test.QuickSpec.Utils.Typed.O
                                                  (map (\e -> let trm = replaceQSType db (Test.QuickSpec.Term.term e)
                                                               in e {
                                                           Test.QuickSpec.Term.term = trm,
                                                           Test.QuickSpec.Term.eval = \env -> case trm of
                                                               Test.QuickSpec.Term.Var   s -> Test.QuickSpec.Term.unValuation env (Test.QuickSpec.Term.Variable (Test.QuickSpec.Term.Atom s (Test.QuickSpec.Term.pgen (return x))))
                                                               Test.QuickSpec.Term.Const s -> x
                                                               Test.QuickSpec.Term.App l r -> x
                                                         })
                                                       xs))))

{-# NOINLINE rawNatClasses #-}
rawNatClasses :: [Test.QuickSpec.Utils.Typed.Several Test.QuickSpec.Term.Expr]
rawNatClasses = concatMap (Test.QuickSpec.Utils.Typed.some2
                            (map (Test.QuickSpec.Utils.Typed.Some .
                                  Test.QuickSpec.Utils.Typed.O)   .
                            Test.QuickSpec.TestTree.classes))
                          (Test.QuickSpec.Utils.TypeMap.toList r)
  where r = unsafePerformIO $ Test.QuickSpec.Generate.generate
                                False
                                (const Test.QuickSpec.Term.partialGen)
                                natSig

tType (Test.QuickSpec.Term.Var   s) = Test.QuickSpec.Utils.Typeable.unTypeRep (Test.QuickSpec.Term.symbolType s)
tType (Test.QuickSpec.Term.Const s) = Test.QuickSpec.Utils.Typeable.unTypeRep (Test.QuickSpec.Term.symbolType s)
tType (Test.QuickSpec.Term.App l r) =
  fromMaybe (error (concat ["Incompatible types (", show (tType l), ") (",
                                                    show (tType r), ")"]))
            (funResultTy (tType l) (tType r))

replaceQSTypes :: [(Type, Type)] -> [[Test.QuickSpec.Term.Term]] -> [[Test.QuickSpec.Term.Term]]
replaceQSTypes db = map rep
  where rep = map (replaceQSType db)

replaceQSType db t =
    case t of
         Test.QuickSpec.Term.Var   s -> Test.QuickSpec.Term.Var (
           let ty = prnt (Test.QuickSpec.Utils.Typeable.unTypeRep
                           (Test.QuickSpec.Term.symbolType s))
               tr = repToQSRep (getRep ty)
               n = let suf = reverse
                               (takeWhile (/= ',')
                                 (reverse (Test.QuickSpec.Term.name s)))
                       idx = read (init suf) :: Int
                    in unName (varName (Var
                         ty
                         idx
                         (Arity (Test.QuickSpec.Term.symbolArity s))))
            in s {
             Test.QuickSpec.Term.symbolType = tr,
             Test.QuickSpec.Term.name = n
           })
         Test.QuickSpec.Term.Const s -> Test.QuickSpec.Term.Const (s {
             Test.QuickSpec.Term.symbolType =
               repToQSRep
                 (getRep
                   (prnt (Test.QuickSpec.Utils.Typeable.unTypeRep
                           (Test.QuickSpec.Term.symbolType s))))
           })
         Test.QuickSpec.Term.App l r -> Test.QuickSpec.Term.App
           (replaceQSType db l)
           (replaceQSType db r)
  where prs x = case HSE.Parser.parseType (show x) of
          HSE.Parser.ParseOk typ -> unwrapParens (void typ)
          HSE.Parser.ParseFailed _ e -> error (concat [
                               "Failed to replace QuickSpec type '",
                               show t,
                               "'. Error is: ",
                               e])
        prnt = replaceInType db . prs

naturalDb = [(tyCon "Natural", tyCon "Z")]
