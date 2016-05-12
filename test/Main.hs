{-# LANGUAGE BangPatterns, OverloadedStrings, PartialTypeSignatures, ScopedTypeVariables #-}

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
  , testProperty "Classes have one arity"       classHasSameArity
  , testProperty "Class length more than one"   classesNotSingletons
  , testProperty "Can get classes from sig"     canGetClassesFromEqs
  , testProperty "Can get universe from sig"    canGetUnivFromSig
  , testProperty "Can get context from sig"     canGetCxtFromSig
  , testProperty "Can get sig from equations"   canGetSigFromEqs
  , testProperty "Sig has equation variables"   eqSigHasVars
  , testProperty "Sig has equation constants"   eqSigHasConsts
  , testProperty "Equations have one arity"     equationsHaveSameArity
  , testProperty "Can render equations"         canRenderEqs
  , testProperty "Can prune equations"          canPruneEqs
  , testProperty "Expression types match up"    checkEvalTypes
  , testProperty "Can get type of terms"        canGetTermType
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

sigConstsUniqueIndices = doOnce sigConstsUniqueIndices'

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

sigVarsUniqueIndices = doOnce sigVarsUniqueIndices'

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
  where mkExpr s = let e = doGenerate' s >>$ putTrue
                    in (e, ())

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
        eqPartsInSameClass (Eq l r) = r `elem` (matchingClass l) &&
                                      l `elem` (matchingClass r)
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

nonEqualElementsSeparate t v = match classes expected && match expected classes
  where (a:b:c:d:e:f:_) = map extend [0..]

        extend 0 = t
        extend n = App v (extend (n-1))

        eqs = [Eq a b, Eq b c, Eq d e, Eq e f]

        classes = classesFromEqs eqs

        expected = [[a, b, c], [d, e, f]]

        match    []  ys = True
        match (x:xs) ys = any (setEq x) ys && match xs ys

classElementsAreEqual (Eqs eqs) = all elementsAreEqual classes
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

canGetClassesFromEqs (Eqs eqs) = True
  where typeCheck = classesFromEqs eqs

canGetUnivFromSig (Eqs eqs) = testExec mkExpr endsInTrue
  where mkExpr s = let e = doUniv' eqs s $>>$ putTrue
                    in (e, ())

canGetCxtFromSig eqs = testExec mkExpr endsInTrue
  where mkExpr s = let e = doCtx' eqs s $>>$ putTrue
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

canRenderEqs = doOnce canRenderEqs'

canRenderEqs' (Eqs eqs) = testEval mkExpr haveEqs
  where mkExpr () = (indent expr, debug)
        expr      = unlines' $$$ shownEqs'
        sig'      = render (sigFromEqs eqs)
        shownEqs' = (map' $$$ (showEquation' $$$ sig')) $$$ eqs'
        eqs'      = unSomePrune sig' clss
        clss      = unSomeClasses eqs
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
        haveEqs (Just s) = unsafePerformIO $ do
          print ("Got output: " ++ s)
          return $ setEq (map lToEq (lines s)) -- (filter keep (lines s)))
                         eqs

-- | Check whether we can convince the type-checker that various expressions
--   have the types we think they do
checkEvalTypes = doOnce checkEvalTypes'

checkEvalTypes' term = monadicIO . checkTypes $ exprs
  where checkTypes [] = return ()
        checkTypes ((e, t, ms):es) = do
          out <- run . exec $ mkExpr ms (e `withType` t)
          case out of
               Nothing -> do dbg (("expr", e), ("type", t))
                             assert False
               Just "" -> assert True
               Just s  -> do dbg (("expr", e), ("type", t), ("result", s))
          checkTypes es

        mkExpr :: [Mod] -> TypedExpr a -> TypedExpr (IO ())
        mkExpr ms e = ("const" $$$ "return ()") $$$ (withMods' ms e)

        -- The expressions we want to check the types of
        exprs :: [(TypedExpr a, String, [Mod])]
        exprs = [

          (unType strip', "Test.QuickSpec.Term.Expr a -> a",
           ["Test.QuickSpec.Term"]),

          (unType prune', "Context -> [Term] -> (a -> Equation) -> [a] -> [a]",
           ["Test.QuickSpec.Term", "Test.QuickSpec.Equation",
            "Test.QuickSpec.Reasoning.NaiveEquationalReasoning"]),

          (unType id', "a -> a",
           []),

          (unType initial', "Int -> [Symbol] -> [Tagged Term] -> Context",
           ["Test.QuickSpec.Reasoning.NaiveEquationalReasoning",
            "Test.QuickSpec.Utils.Typed"]),

          (unType maxDepth', "Sig -> Int",
           []),

          (unType symbols', "Sig -> [Symbol]",
           []),

          (unType filter', "(a -> Bool) -> [a] -> [a]",
           []),

          (unType not', "Bool -> Bool",
           []),

          (unType isUndefined', "Term -> Bool",
           []),

          (unType (sort' :: TypedExpr ([Bool] -> [Bool])), "[Bool] -> [Bool]",
           []),

          (unType append', "[a] -> [a] -> [a]",
           []),

          (unType map', "(a -> b) -> [a] -> [b]",
           []),

          (unType conTagged', "Witness -> a -> Tagged a",
           ["Test.QuickSpec.Utils.Typed"]),

          (unType conSome', "f Bool -> Some f",
           ["Data.Typeable"]),

          (unType conWitness', "a -> Witnessed a",
           []),

          (unType term', "Expr a -> Term",
           []),

          (unType univ2, "Test.QuickSpec.Term.Expr Bool -> Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term",
           ["Test.QuickSpec.Term", "Test.QuickSpec.Utils.Typed",
            "Data.Typeable"]),

          (unType (map' $$$ univ2), "[Test.QuickSpec.Term.Expr Bool] -> [Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]",
           []),

          (unType (mkUniv2 [(cons' $$$ termToExpr term) $$$ nil']),
           "[Test.QuickSpec.Utils.Typed.Tagged Test.QuickSpec.Term.Term]",
           ["Test.QuickSpec.Term", "Test.QuickSpec.Utils.Typed"])

          ]

canPruneEqs = canPruneEqs'

canPruneEqs' eqs = monadicIO $ do
    out <- run $ pruneEqs' format eqs
    monitor (counterexample (show (("eqs", eqs), ("out", out))))
    assert (expected out)
  where format pruned = showEqsOnLines eqs (indent pruned)
        expected Nothing  = False
        expected (Just x) = case eqs of
                                 [] -> x == ""  -- No output when no eqs
                                 _  -> "==" `isInfixOf` (x :: String)

canGetTermType (Type input) (Type output) = expected (termType term)
  where term  = App (C (Const undefined undefined func))
                    (C (Const undefined undefined (Type input)))
        func  = Type $ concat ["(", input, ") -> (", output, ")"]
        strip = filter (/= ' ')
        expected (Just (Type x)) = strip x === strip output

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

termOfType (Type t) = termOfTypeArity 0 t

termOfTypeArity a t = oneof [
  if a > 5
     then discard
     else C <$> (Const (Arity a) <$> arbitrary <*> return (Type t)),

  -- We can only generate variables up to arity 2
  if a > 2
     then discard
     else V <$> (Var (Type t) <$> choose (0, 4) <*> return (Arity a)),
  do Type arg <- arbitrary
     r        <- termOfTypeArity 0     arg
     l        <- termOfTypeArity (a+1) (concat ["(", arg, ") -> (", t, ")"])
     return $ App l r]

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
        renameTerm (V v)             = pure (V c)
        renameTerm (App l r)         = App <$> renameTerm l <*> renameTerm r

consistentEqs eqs = let nts = concatMap eqNames eqs
                     in consistentNames nts

instance Arbitrary Equation where
  arbitrary = do Type t <- arbitrary
                 l <- termOfType (Type t)
                 r <- termOfType (Type t)
                 if trivial l && trivial r || l == r || allVar l || allVar r
                    then discard
                    else return $ Eq l r

  shrink (Eq l r) = [Eq l' r' | (l', r') <- shrink (l, r),
                     termType' l' == termType' r',
                     not (trivial l' && trivial r')]

-- "Trivial" equations will be pruned, so we need to avoid generating (or
-- shrinking down to) equations where both sides only have one symbol, or which
-- don't contain any variables
trivial (C _)              = True
trivial (V _)              = True
trivial x | not (hasVar x) = True
trivial x | allVar x       = True

hasVar (V _)     = True
hasVar (C _)     = False
hasVar (App l r) = hasVar l || hasVar r

allVar (V _) = True
allVar (C _) = True
allVar (App l r) = allVar l && allVar r

-- | Make sure no name is used for constants of two types
termNames :: Term -> [(Name, Type)]
termNames (C (Const _ n t)) = [(n, t)]
termNames (V _)             = []
termNames (App l r)         = nub (termNames l ++ termNames r)

eqNames :: Equation -> [(Name, Type)]
eqNames (Eq l r) = termNames l ++ termNames r

consistentNames nts = all hasOneType names
  where names        = map fst nts
        hasOneType n = length (typesOf n) == 1
        typesOf    n = nub (map snd (entriesOf n))
        entriesOf  n = filter ((== n) . fst) nts

instance Arbitrary Term where
  arbitrary = oneof [C <$> arbitrary, V <$> arbitrary,
    do r         <- arbitrary
       x         <- arbitrary
       vc        <- arbitrary
       Type retT <- arbitrary
       i         <- choose (0, 4)
       let Type argT = termType' r
           funT      = "(" ++ argT ++ ") -> (" ++ retT ++ ")"
           l         = if vc
                          then C (Const (Arity 1) (constName x) (Type funT))
                          else V (Var (Type funT) i (Arity 1))
       return $ App l r]

  shrink (C c)       = C <$> shrink c
  shrink (V v)       = V <$> shrink v
  shrink t@(App l r) = [C (Const (termArity t) (termName t) (termType' t))] ++
                       [App l' r' | (l', r') <- shrink (l, r)]

termName (C c)     = constName c
termName (V v)     = Name (filter isAlpha (show (varType v) ++ show (varArity v)))
termName (App l r) = let Name l' = termName l
                         Name r' = termName r
                      in Name ("app" ++ l' ++ r')

instance Arbitrary Var where
  arbitrary = sized $ \n -> do
    arity <- elements [0, 1, 2]
    typ   <- naryType arity n
    index <- elements [0, 1, 2]
    return $ Var (Type typ) index (Arity arity)

  shrink (Var t i a) = if i == 0
                          then []
                          else [Var t 0 a]

instance Arbitrary Const where
  arbitrary = sized $ \n -> do
    arity <- elements [0..5]
    name  <- arbitrary
    typ   <- naryType arity n
    return $ Const (Arity arity) name (Type typ)

  shrink (Const a n t) = do n' <- shrink n
                            return (Const a n' t)

instance Arbitrary Sig where
  arbitrary = Sig <$> listOf arbitrary <*> listOf arbitrary
  shrink (Sig [] []) = []
  shrink (Sig cs vs) = Sig [] [] : [Sig cs' vs' | (cs', vs') <- shrink (cs, vs)]

instance Arbitrary Type where
  arbitrary = Type <$> sized sizedType

instance Arbitrary Name where
  arbitrary = Name <$> listOf1 (arbitrary `suchThat` isAlpha)

  shrink (Name x) = let suffices = tail (tails x)
                        nonEmpty = filter (not . null) suffices
                        names    = map Name nonEmpty
                     in reverse names -- Try shortest first

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

dbg :: (Show a, Monad m) => a -> PropertyM m ()
dbg = monitor . counterexample . show

doOnce :: (Show a, Arbitrary a, Testable prop) => (a -> prop) -> Property
doOnce = once . forAll (resize 3 arbitrary)

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
