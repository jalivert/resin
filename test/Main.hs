module Main (main) where

-- Tests for the resin theorem prover.
--
-- The suite is split into three groups:
--   1. Parser tests (Formula and Module level).
--   2. Tests of the pure formula transformations in Given'Clause
--      (NNF, PNF, skolemisation, CNF/DNF, substitution, unification).
--   3. End-to-end resolution tests (valid goals must be proved,
--      unprovable-but-harmless goals must be refuted with Nothing).


import Control.Exception (SomeException, evaluate, try)
import Data.Maybe (isJust, isNothing)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (exitFailure, exitSuccess)

import Syntax (Formula, Rel(..), Term(..))
import qualified Syntax as S
import qualified Given'Clause as G
import qualified Parser as P


-- Test harness -----------------------------------------------------------

check :: String -> Bool -> IO Bool
check label True = do
  putStrLn ("ok    " ++ label)
  return True
check label False = do
  putStrLn ("FAIL  " ++ label)
  return False


checkEq :: (Eq a, Show a) => String -> a -> a -> IO Bool
checkEq label expected actual
  | expected == actual = check label True
  | otherwise = do
      _ <- check label False
      putStrLn ("  expected: " ++ show expected)
      putStrLn ("  actual:   " ++ show actual)
      return False


parsesAs :: String -> String -> Formula -> IO Bool
parsesAs label src expected =
  checkEq label (Right expected :: Either (String, Int) Formula) (P.parse'formula src)


parseFails :: String -> String -> IO Bool
parseFails label src =
  case P.parse'formula src of
    Left _ -> check (label ++ " (rejected)") True
    Right fm -> do
      _ <- check (label ++ " (rejected)") False
      putStrLn ("  unexpectedly parsed as: " ++ show fm)
      return False


isProved :: String -> Maybe a -> IO Bool
isProved label = check (label ++ " (proved)") . isJust


isUnprovable :: String -> Maybe a -> IO Bool
isUnprovable label = check (label ++ " (correctly unprovable)") . isNothing


-- Small formula fixtures -------------------------------------------------

p, q :: Formula
p = S.Atom (Rel "P" [])
q = S.Atom (Rel "Q" [])

pa :: Formula
pa = S.Atom (Rel "P" [Fn "a" []])

qb :: Formula
qb = S.Atom (Rel "Q" [Fn "b" []])


-- Structural helpers (independent re-implementation for property tests) --

hasImplEq :: Formula -> Bool
hasImplEq S.True = False
hasImplEq S.False = False
hasImplEq (S.Atom _) = False
hasImplEq (S.Not f) = hasImplEq f
hasImplEq (S.And f g) = hasImplEq f || hasImplEq g
hasImplEq (S.Or f g) = hasImplEq f || hasImplEq g
hasImplEq (S.Impl _ _) = True
hasImplEq (S.Eq _ _) = True
hasImplEq (S.Forall _ f) = hasImplEq f
hasImplEq (S.Exists _ f) = hasImplEq f


-- True when every quantifier is in a front prefix (prenex shape).
isPrenex :: Formula -> Bool
isPrenex (S.Forall _ f) = isPrenex f
isPrenex (S.Exists _ f) = isPrenex f
isPrenex f = not (hasQuantifier f)


hasQuantifier :: Formula -> Bool
hasQuantifier S.True = False
hasQuantifier S.False = False
hasQuantifier (S.Atom _) = False
hasQuantifier (S.Not f) = hasQuantifier f
hasQuantifier (S.And f g) = hasQuantifier f || hasQuantifier g
hasQuantifier (S.Or f g) = hasQuantifier f || hasQuantifier g
hasQuantifier (S.Impl f g) = hasQuantifier f || hasQuantifier g
hasQuantifier (S.Eq f g) = hasQuantifier f || hasQuantifier g
hasQuantifier (S.Forall _ _) = True
hasQuantifier (S.Exists _ _) = True


-- Parser tests -----------------------------------------------------------

parserTests :: IO Bool
parserTests = do
  putStrLn "-- parser: propositional connectives --"
  a1 <- parsesAs "tautology literal" "True" S.True
  a2 <- parsesAs "tautology word" "Tautology" S.True
  a3 <- parsesAs "contradiction literal" "False" S.False
  a4 <- parsesAs "contradiction word" "Contradiction" S.False
  a5 <- parsesAs "atom" "P" p
  a6 <- parsesAs "negation" "NOT P" (S.Not p)
  a7 <- parsesAs "conjunction" "P AND Q" (S.And p q)
  a8 <- parsesAs "disjunction" "P OR Q" (S.Or p q)
  a9 <- parsesAs "implication ascii" "P ==> Q" (S.Impl p q)
  a10 <- parsesAs "implication unicode" "P \10233 Q" (S.Impl p q)
  a11 <- parsesAs "equivalence ascii" "P <=> Q" (S.Eq p q)
  a12 <- parsesAs "equivalence unicode" "P \10234 Q" (S.Eq p q)
  a13 <- parsesAs "unicode and" "P \8743 Q" (S.And p q)
  a14 <- parsesAs "unicode or" "P \8744 Q" (S.Or p q)
  a15 <- parsesAs "unicode not" "\172P" (S.Not p)
  a16 <- parsesAs "ampersand" "P && Q" (S.And p q)
  a17 <- parsesAs "double pipe" "P || Q" (S.Or p q)

  putStrLn "-- parser: precedence and associativity --"
  b1 <- parsesAs "and binds tighter than or" "P OR Q AND R"
          (S.Or p (S.And q (S.Atom (Rel "R" []))))
  b2 <- parsesAs "left assoc and" "P AND Q AND R"
          (S.And (S.And p q) (S.Atom (Rel "R" [])))
  b3 <- parsesAs "right assoc impl" "P ==> Q ==> R"
          (S.Impl p (S.Impl q (S.Atom (Rel "R" []))))
  b4 <- parsesAs "not binds tightest" "NOT P AND Q"
          (S.And (S.Not p) q)
  b5 <- parsesAs "parens override" "(P OR Q) AND R"
          (S.And (S.Or p q) (S.Atom (Rel "R" [])))

  putStrLn "-- parser: quantifiers, variables, constants --"
  c1 <- parsesAs "forall ascii" "forall x P(x)"
          (S.Forall "x" (S.Atom (Rel "P" [Var "x"])))
  c2 <- parsesAs "forall unicode" "\8704 x P(x)"
          (S.Forall "x" (S.Atom (Rel "P" [Var "x"])))
  c3 <- parsesAs "exists unicode" "\8707 x P(x)"
          (S.Exists "x" (S.Atom (Rel "P" [Var "x"])))
  c4 <- parsesAs "multi binder is nested" "forall x y P(x, y)"
          (S.Forall "x" (S.Forall "y" (S.Atom (Rel "P" [Var "x", Var "y"]))))
  c5 <- parsesAs "constant marker" "P(Zero\7580)"
          (S.Atom (Rel "P" [Fn "Zero" []]))
  c6 <- parsesAs "numeric constant marker" "P(0\7580)"
          (S.Atom (Rel "P" [Fn "0" []]))
  c7 <- parseFails "unbound object variable" "P(x)"
  c8 <- parseFails "unknown numeric constant" "P(0)"
  c9 <- parseFails "single binder scope ends" "(forall x P(x)) OR Q(x)"
  c10 <- parseFails "first binder of many does not leak" "(forall x y P(x, y)) OR Q(x)"
  c11 <- parseFails "later binders of many do not leak" "(forall x y P(x, y)) OR Q(y)"
  c12 <- parseFails "three binders do not leak" "(forall x y z P(x, y, z)) OR Q(z)"
  c13 <- parseFails "nested quantifier scope still ends" "forall x (forall y P(x, y)) OR Q(y)"
  c14 <- parsesAs "binders stay visible in body" "forall x y (P(x, y) AND Q(y))"
          (S.Forall "x" (S.Forall "y" (S.And (S.Atom (Rel "P" [Var "x", Var "y"]))
                                             (S.Atom (Rel "Q" [Var "y"])))) )

  putStrLn "-- parser: modules --"
  d1 <- checkModuleValid
  d2 <- checkModuleUsing
  d3 <- checkModuleBadUsing
  d4 <- checkModuleDupAlias
  return (and [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
               a15, a16, a17, b1, b2, b3, b4, b5, c1, c2, c3, c4, c5, c6, c7,
               c8, c9, c10, c11, c12, c13, c14, d1, d2, d3, d4])


checkModuleValid :: IO Bool
checkModuleValid = do
  let src = "constants: zero .\naxioms: Nat(zero) .\ntheorem zero-is-nat: Nat(zero) .\n"
  case P.parse'module src of
    Left (err, _) -> do
      _ <- check "valid module parses" False
      putStrLn ("  error: " ++ err)
      return False
    Right (consts, _aliases, axioms, theorems) -> do
      r1 <- checkEq "module constants" ["zero"] consts
      r2 <- checkEq "module axiom count" 1 (length axioms)
      r3 <- checkEq "module theorem names" ["zero-is-nat"] (map S.name theorems)
      return (and [r1, r2, r3])


checkModuleUsing :: IO Bool
checkModuleUsing = do
  let src = "constants: zero .\naxioms: (ax1: Nat(zero)) .\ntheorem t: Nat(zero) . using { ax1 }\n"
  case P.parse'module src of
    Left (err, _) -> do
      _ <- check "using with bound name parses" False
      putStrLn ("  error: " ++ err)
      return False
    Right (_, _, _, theorems) ->
      checkEq "using clause recorded" [Just ["ax1"]] (map S.allowed theorems)


checkModuleBadUsing :: IO Bool
checkModuleBadUsing =
  case P.parse'module "theorem t: P . using { nope }\n" of
    Left _ -> check "using with unbound name rejected" True
    Right _ -> check "using with unbound name rejected" False


checkModuleDupAlias :: IO Bool
checkModuleDupAlias =
  case P.parse'module "constants: zero .\naliases: a = zero, a = zero .\n" of
    Left _ -> check "duplicate alias rejected" True
    Right _ -> check "duplicate alias rejected" False


-- Pure transformation tests ----------------------------------------------

pureTests :: IO Bool
pureTests = do
  putStrLn "-- syntax: show --"
  s1 <- checkEq "show true" "\8868" (show S.True)
  s2 <- checkEq "show false" "\8869" (show S.False)
  s3 <- checkEq "show term" "f(x, a)" (show (Fn "f" [Var "x", Fn "a" []]))
  s4 <- checkEq "show negation" "\172P" (show (S.Not p))
  s5 <- checkEq "show conjunction" "P \8743 Q" (show (S.And p q))

  putStrLn "-- basics: negate, conj/disj lists --"
  t1 <- checkEq "double negation" p (G.negate (G.negate p))
  t2 <- checkEq "negate atom" (S.Not p) (G.negate p)
  t3 <- check "negative detects Not" (G.negative (S.Not p))
  t4 <- check "positive detects atom" (G.positive p)
  t5 <- checkEq "empty conjunction is true" S.True (G.list'conj [])
  t6 <- checkEq "empty disjunction is false" S.False (G.list'disj [])
  t7 <- checkEq "conjunction list" (S.And p q) (G.list'conj [p, q])
  t8 <- checkEq "disjunction list" (S.Or p q) (G.list'disj [p, q])

  putStrLn "-- nnf and simplify --"
  n1 <- checkEq "nnf de morgan" (S.Or (S.Not p) (S.Not q)) (G.nnf (S.Not (S.And p q)))
  n2 <- checkEq "nnf implication" (S.Or (S.Not p) q) (G.nnf (S.Impl p q))
  n3 <- checkEq "nnf double negation" p (G.nnf (S.Not (S.Not p)))
  n4 <- check "nnf removes impl/equiv"
          (not (hasImplEq (G.nnf (S.Impl (S.Not (S.And p q)) (S.Eq p (S.Not q))))))
  n5 <- checkEq "simplify drops vacuous forall"
          p (G.simplify (S.Forall "x" p))
  n6 <- checkEq "simplify keeps live forall"
          (S.Forall "x" (S.Atom (Rel "P" [Var "x"])))
          (G.simplify (S.Forall "x" (S.Atom (Rel "P" [Var "x"]))))
  n7 <- checkEq "simplify and-true" p (G.simplify (S.And S.True p))

  putStrLn "-- free variables, substitution, generalisation --"
  f1 <- checkEq "fv respects binder"
          (Set.singleton "y")
          (G.fv (S.Forall "x" (S.Atom (Rel "P" [Var "x", Var "y"]))))
  f2 <- checkEq "term substitution"
          (Fn "f" [Fn "a" [], Var "y"])
          (G.t'subst (Map.singleton "x" (Fn "a" [])) (Fn "f" [Var "x", Var "y"]))
  f3 <- checkEq "substitution avoids capture"
          (S.Forall "y'" (S.Atom (Rel "P" [Var "y", Var "y'"])))
          (G.subst (Map.singleton "x" (Var "y"))
                   (S.Forall "y" (S.Atom (Rel "P" [Var "x", Var "y"]))))
  f4 <- checkEq "generalize binds free vars"
          (S.Forall "x" (S.Forall "y" (S.Atom (Rel "P" [Var "y", Var "x"]))))
          (G.generalize (S.Atom (Rel "P" [Var "y", Var "x"])))

  putStrLn "-- normal forms --"
  m1 <- checkEq "dnf false" [] (G.simp'dnf S.False)
  m2 <- checkEq "dnf true" [[]] (G.simp'dnf S.True)
  m3 <- checkEq "cnf false" [[]] (G.simp'cnf S.False)
  m4 <- checkEq "cnf true" [] (G.simp'cnf S.True)
  m5 <- checkEq "cnf of disjunction"
          [[p, q]] (G.simp'cnf (S.Or p q))
  m6 <- check "pnf pulls quantifiers out"
          (isPrenex (G.pren'norm'form (S.Impl (S.Forall "x" (S.Atom (Rel "P" [Var "x"])))
                                             (S.Exists "y" (S.Atom (Rel "Q" [Var "y"]))))))
  m7 <- check "skolem removes existentials"
          (not (G.contains'exists (G.skol'norm'form
                  (S.Forall "x" (S.Exists "y" (S.Atom (Rel "R" [Var "x", Var "y"])))))))
  m8 <- check "conjunction normal form is quantifier free"
          (not (hasQuantifier (G.con'norm'form
                  (S.Forall "x" (S.Exists "y" (S.Atom (Rel "R" [Var "x", Var "y"])))))))

  putStrLn "-- unification --"
  u1 <- checkEq "variable binds to constant"
          (Just (Map.singleton "x" (Fn "a" [])))
          (G.unify Map.empty [(Var "x", Fn "a" [])])
  u2 <- check "occurs check rejects x = f(x)"
          (isNothing (G.unify Map.empty [(Var "x", Fn "f" [Var "x"])]))
  u3 <- checkEq "function args unify"
          (Just (Map.singleton "x" (Fn "a" [])))
          (G.unify Map.empty [(Fn "f" [Var "x"], Fn "f" [Fn "a" []])])
  u4 <- check "different constants do not unify"
          (isNothing (G.unify Map.empty [(Fn "a" [], Fn "b" [])]))
  u5 <- check "different arities do not unify"
          (isNothing (G.unify Map.empty [(Fn "f" [Var "x"], Fn "f" [Var "x", Var "y"])]))
  u6 <- check "literals with same relation unify"
          (isJust (G.unify'literals Map.empty
            (S.Atom (Rel "P" [Var "x"]), S.Atom (Rel "P" [Fn "a" []]))))
  u7 <- check "literals with different relations do not unify"
          (isNothing (G.unify'literals Map.empty
            (S.Atom (Rel "P" [Var "x"]), S.Atom (Rel "Q" [Var "x"]))))
  u8 <- check "mgu chains substitutions"
          (isJust (G.mgu [S.Atom (Rel "P" [Var "x"]),
                          S.Atom (Rel "P" [Var "y"]),
                          S.Atom (Rel "P" [Fn "a" []])] Map.empty))
  u9 <- check "trivial detects complementary pair"
          (G.trivial [p, S.Not p])
  u10 <- check "trivial ignores unrelated pair"
          (not (G.trivial [p, q]))

  putStrLn "-- subsumption and clause resolution --"
  v1 <- check "ground instance is subsumed"
          (G.subsumes'clause [S.Atom (Rel "P" [Var "x"])]
                             [S.Atom (Rel "P" [Fn "a" []])])
  v2 <- check "general is not subsumed by instance"
          (not (G.subsumes'clause [S.Atom (Rel "P" [Fn "a" []])]
                                  [S.Atom (Rel "P" [Var "x"])]))
  v3 <- check "subsumption respects function arity"
          (not (G.subsumes'clause [S.Atom (Rel "P" [Fn "f" [Fn "a" []]])]
                                  [S.Atom (Rel "P" [Fn "f" [Fn "a" [], Fn "b" []]])]))
  v4 <- check "complementary units resolve to empty clause"
          (Set.member [] (G.resolve'clauses [pa] [S.Not pa]))

  return (and [s1, s2, s3, s4, s5, t1, t2, t3, t4, t5, t6, t7, t8,
               n1, n2, n3, n4, n5, n6, n7, f1, f2, f3, f4,
               m1, m2, m3, m4, m5, m6, m7, m8,
               u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, v1, v2, v3, v4])


-- Resolution tests -------------------------------------------------------

resolutionTests :: IO Bool
resolutionTests = do
  putStrLn "-- resolution: propositional logic --"
  r1 <- isProved "assumption proves itself" (G.resolution [p] p)
  r2 <- isProved "tautology needs no assumptions" (G.resolution [] (S.Impl p p))
  r3 <- isProved "modus ponens" (G.resolution [S.Impl p q, p] q)
  r4 <- isProved "modus tollens" (G.resolution [S.Impl p q, S.Not q] (S.Not p))
  r5 <- isProved "excluded middle" (G.resolution [] (S.Or p (S.Not p)))
  r6 <- isProved "contradiction is detected" (G.pure'resolution (S.And p (S.Not p)))
  r7 <- isProved "false is refutable" (G.pure'resolution S.False)
  r8 <- isUnprovable "atomic goal without assumptions" (G.resolution [] pa)
  r9 <- isUnprovable "unrelated assumption" (G.resolution [pa] qb)
  r10 <- isUnprovable "satisfiable formula" (G.pure'resolution pa)
  r11 <- isUnprovable "truth needs no refutation" (G.pure'resolution S.True)

  putStrLn "-- resolution: first-order logic --"
  let forallP = S.Forall "x" (S.Atom (Rel "P" [Var "x"]))
  f1 <- isProved "universal instantiation" (G.resolution [forallP] pa)
  f2 <- checkEq "existential goal yields witness"
          (Just [("x", Fn "a" [])])
          (G.resolution [pa] (S.Exists "x" (S.Atom (Rel "P" [Var "x"]))))
  f3 <- isProved "modus ponens with predicates"
          (G.resolution [S.Forall "x" (S.Impl (S.Atom (Rel "P" [Var "x"]))
                                             (S.Atom (Rel "Q" [Var "x"]))), pa]
                        (S.Atom (Rel "Q" [Fn "a" []])))
  f4 <- isUnprovable "cannot prove unrelated predicate" (G.resolution [pa] qb)

  return (and [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, f1, f2, f3, f4])


-- Example files parse (best effort: skipped when not run from repo root) --

exampleTests :: IO Bool
exampleTests = do
  putStrLn "-- examples: all .rin files still parse --"
  let files = ["examples/curiosity.rin", "examples/fact.rin",
               "examples/list.rin", "examples/manual.rin",
               "examples/modi.rin", "examples/nats.rin",
               "examples/siblings.rin", "examples/west.rin"]
  results <- mapM checkExample files
  return (and results)


checkExample :: FilePath -> IO Bool
checkExample path = do
  content <- try (readFile path) :: IO (Either SomeException String)
  case content of
    Left _ -> do
      putStrLn ("skip  " ++ path ++ " (not readable from here)")
      return True
    Right src -> do
      forced <- try (evaluate (length src)) :: IO (Either SomeException Int)
      case forced of
        Left _ -> do
          putStrLn ("skip  " ++ path ++ " (not readable from here)")
          return True
        Right _ ->
          case P.parse'module src of
            Right _ -> check ("parses " ++ path) True
            Left (err, _) -> do
              _ <- check ("parses " ++ path) False
              putStrLn ("  error: " ++ take 200 err)
              return False


-- Main -------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "== parser =="
  rParser <- parserTests
  putStrLn "== pure transformations =="
  rPure <- pureTests
  putStrLn "== resolution =="
  rResolution <- resolutionTests
  putStrLn "== examples =="
  rExamples <- exampleTests
  putStrLn ""
  if and [rParser, rPure, rResolution, rExamples]
    then do
      putStrLn "All tests passed."
      exitSuccess
    else do
      putStrLn "Some tests FAILED."
      exitFailure
