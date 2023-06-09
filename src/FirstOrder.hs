module FirstOrder where

import Data.List
import Data.Ord (comparing)
import Control.Monad
import Control.Monad.State
import Test.QuickCheck hiding (Fun, (===))

import Utils

-- Variable names are just strings
type VarName = String
type FunName = String
type RelName = String

-- enumerate variants of a variable name
variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

data GenTerm a = Var a | Fun FunName [GenTerm a] deriving (Eq, Ord,Show)

type Term = GenTerm VarName

variables :: Term -> [VarName]
variables (Var x) = [x]
variables (Fun _ ts) = nub $ concatMap variables ts

type FunInt a = FunName -> [a] -> a
type Env a = VarName -> a

evalTerm :: FunInt a -> Env a -> Term -> a
evalTerm _ rho (Var x) = rho x
evalTerm int rho (Fun f ts) = int f $ map (evalTerm int rho) ts

-- our inductive type for first-order logic formulas
data Formula =
      F
    | T
    | Rel RelName [Term]
    | Not Formula
    | Or Formula Formula
    | And Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    | Exists VarName Formula
    | Forall VarName Formula deriving (Eq, Ord, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, -->
(\/) = Or
(∨) = Or
(-->) = Implies

infixr 4 <-->
(<-->) = Iff

infix 9 ===, =/=
(===), (=/=) :: Term -> Term -> Formula
u === v = Rel "=" [u, v]
u =/= v = Not (u === v)

type Substitution = Env Term

-- apply a substitution on all free variables
apply :: Substitution -> Formula -> Formula
apply _ F = F
apply _ T = T
apply f (Rel r ts) = Rel r $ map (evalTerm Fun f) ts
apply f (Not phi) = Not (apply f phi)
apply f (Or phi psi) = Or (apply f phi) (apply f psi)
apply f (And phi psi) = And (apply f phi) (apply f psi)
apply f (Implies phi psi) = Implies (apply f phi) (apply f psi)
apply f (Iff phi psi) = Iff (apply f phi) (apply f psi)
apply f (Exists x phi) = Exists x (apply (update f x (Var x)) phi)
apply f (Forall x phi) = Forall x (apply (update f x (Var x)) phi)

instance {-# OVERLAPPING #-} Arbitrary VarName where
  arbitrary = elements ["x", "y", "z", "t"]

instance Arbitrary Term where
  arbitrary = resize 8 $ sized f where
    f size | size == 0 || size == 1 = do x <- arbitrary
                                         return $ Var x
           | otherwise = frequency [ (1, go sizes) | sizes <- catalan size]
              where go sizes = do ts <- mapM f sizes
                                  return $ Fun "f" ts

instance Arbitrary Formula where
  arbitrary = resize 30 $ sized f where
    f 0 = do ts <- arbitrary
             return $ Rel "R" ts
    f size = frequency [
      (1, fmap Not (f (size - 1))),
      (4, do
        size' <- choose (0, size - 1)
        conn <- oneof $ map return [And, Or, Implies, Iff]
        left <- f size'
        right <- f $ size - size' - 1
        return $ conn left right),
      (5, do
        conn <- oneof $ map return [Exists, Forall]
        phi <- f $ size - 1
        x <- arbitrary
        return $ conn x phi)
      ]

  shrink (Not varphi) = [varphi]
  shrink (Or varphi psi) = [varphi, psi]
  shrink (And varphi psi) = [varphi, psi]
  shrink (Implies varphi psi) = [varphi, psi]
  shrink (Iff varphi psi) = [varphi, psi]
  shrink (Exists _ varphi) = [varphi]
  shrink (Forall _ varphi) = [varphi]
  shrink _ = []

type SATSolver = Formula -> Bool
type FOProver = Formula -> Bool

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nub $ concatMap varsT ts

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = x `notElem` vars phi

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

fv :: Formula -> [VarName]
fv T = []
fv F = []
fv (Rel _ ts) = varsT (Fun "dummy" ts)
fv (Not phi) = fv phi
fv (And phi psi) = nub $ fv phi ++ fv psi
fv (Or phi psi) = nub $ fv phi ++ fv psi
fv (Implies phi psi) = nub $ fv phi ++ fv psi
fv (Iff phi psi) = nub $ fv phi ++ fv psi
fv (Exists x phi) = delete x $ fv phi
fv (Forall x phi) = delete x $ fv phi

prop_fv :: Bool
prop_fv = fv (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == ["y", "z"]

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename _ _ T = T
rename _ _ F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

prop_generalise :: Bool
prop_generalise = generalise (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == Forall "y" (Forall "z" (Exists "x" (Rel "R" [Fun "f" [Var "x",Var "y"],Var "z"])))

fresh :: Formula -> Formula
fresh phi = evalState (go phi) $ fv phi
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = fmap Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi

        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, y `notElem` xs]
             let psi = rename x y phi
             put $ y : xs
             fmap (quantifier y) $ go psi

nnf :: Formula -> Formula
nnf = \case
  (Not T) -> F
  (Not F) -> T

  phi@(Rel _ _) -> phi
  phi@(Not (Rel _ _)) -> phi

  (And phi psi) -> And (nnf phi) (nnf psi)
  (Not (And phi psi)) -> Or (nnf (Not phi)) (nnf (Not psi))

  (Or phi psi) -> Or (nnf phi) (nnf psi)
  (Not (Or phi psi)) -> And (nnf (Not phi)) (nnf (Not psi))

  (Implies phi psi) -> Or (nnf (Not phi)) (nnf psi)
  (Not (Implies phi psi)) -> And (nnf phi) (nnf (Not psi))

  (Iff phi psi) -> And (Or (nnf (Not phi)) (nnf psi)) (Or (nnf (Not psi)) (nnf phi))
  (Not (Iff phi psi)) -> Or (And (nnf phi) (nnf (Not psi))) (And (nnf psi) (nnf (Not phi)))

  (Not (Not phi)) -> nnf phi

  (Exists x phi) -> Exists x (nnf phi)
  (Not (Exists x phi)) -> Forall x (nnf (Not phi))

  (Forall x phi) -> Forall x (nnf phi)
  (Not (Forall x phi)) -> Exists x (nnf (Not phi))

  phi -> phi

pnf :: Formula -> Formula
pnf = pnf' . nnf
  where
    pnf' :: Formula -> Formula
    pnf' = \case
      (Forall x phi) -> Forall x (pnf' phi)
      (Exists x phi) -> Exists x (pnf' phi)
      (And phi psi) -> pull_quantifiers (And (pnf' phi) (pnf' psi))
      (Or phi psi) -> pull_quantifiers (Or (pnf' phi) (pnf' psi))
      phi -> phi

    pull_quantifiers = \case
      (And (Forall x phi) (Forall x' psi)) -> if x == x' then
          Forall x (pull_quantifiers $ And phi psi)
        else
          let y = freshVariant x (And phi psi) in Forall y (pull_quantifiers $ And (rename x y phi) (rename x' y psi))

      (And (Forall x phi) psi) ->
        if x `freshIn` psi then
          Forall x (pull_quantifiers $ And phi psi)
        else
          let y = freshVariant x (And phi psi) in Forall y (pull_quantifiers $ And (rename x y phi) psi)

      (And phi psi@(Forall _ _)) -> pull_quantifiers (And psi phi)

      (Or (Forall x phi) psi) -> if x `freshIn` psi then
          Forall x (pull_quantifiers $ Or phi psi)
        else
          let y = freshVariant x (Or phi psi) in Forall y (pull_quantifiers $ Or (rename x y phi) psi)

      (Or phi psi@(Forall _ _)) -> pull_quantifiers (Or psi phi)

      (And (Exists x phi) psi) -> if x `freshIn` psi then
          Exists x (pull_quantifiers $ And phi psi)
        else
          let y = freshVariant x (And phi psi) in Exists y (pull_quantifiers $ And (rename x y phi) psi)

      (And phi psi@(Exists _ _)) -> pull_quantifiers (And psi phi)

      (Or (Exists x phi) (Exists x' psi)) -> if x == x' then
          Exists x (pull_quantifiers $ Or phi psi)
        else
          let y = freshVariant x (Or phi psi) in Exists y (pull_quantifiers $ Or (rename x y phi) (rename x' y psi))

      (Or (Exists x phi) psi) -> if x `freshIn` psi then
          Exists x (pull_quantifiers $ Or phi psi)
        else
          let y = freshVariant x (Or phi psi) in Exists y (pull_quantifiers $ Or (rename x y phi) psi)

      (Or phi psi@(Exists _ _)) -> pull_quantifiers (Or psi phi)

      phi -> phi

miniscope :: Formula -> Formula
miniscope = nnf . go where
  go :: Formula -> Formula
  go = \case
    (Exists x (And phi psi)) | not $ x `freshIn` phi, x `freshIn` psi -> And (go $ Exists x phi) (go psi)
                            | x `freshIn` phi, not $ x `freshIn` psi -> And (go phi) (go $ Exists x psi)
    (Exists x (Or phi psi)) | not $ x `freshIn` phi, not $ x `freshIn` psi -> Or (go $ Exists x phi) (go $ Exists x psi)
                            | not $ x `freshIn` phi -> Or (go $ Exists x phi) (go psi)
                            | not $ x `freshIn` psi -> Or (go phi) (go $ Exists x psi)
    (Forall x (And phi psi)) | not $ x `freshIn` phi, not $ x `freshIn` psi -> And (go $ Forall x phi) (go $ Forall x psi)
                            | not $ x `freshIn` phi -> And (go $ Forall x phi) (go psi)
                            | not $ x `freshIn` psi -> And (go phi) (go $ Forall x psi)
    (Forall x (Or phi psi)) | not $ x `freshIn` phi, x `freshIn` psi -> Or (go $ Forall x phi) (go psi)
                            | x `freshIn` phi, not $ x `freshIn` psi -> Or (go phi) (go $ Forall x psi)
    phi -> phi


skolemise :: Formula -> Formula
skolemise = pnf . skolemise' . miniscope . fresh . nnf . close . removeUnusedQuantifiers
  where
    removeUnusedQuantifiers :: Formula -> Formula
    removeUnusedQuantifiers = \case
      F -> F
      T -> T
      phi@(Rel _ _) -> phi
      Not phi -> Not (removeUnusedQuantifiers phi)
      Or phi psi -> Or (removeUnusedQuantifiers phi) (removeUnusedQuantifiers psi)
      And phi psi -> And (removeUnusedQuantifiers phi) (removeUnusedQuantifiers psi)
      Implies phi psi -> Implies (removeUnusedQuantifiers phi) (removeUnusedQuantifiers psi)
      Iff phi psi -> Iff (removeUnusedQuantifiers phi) (removeUnusedQuantifiers psi)
      Exists x phi | x `freshIn` phi -> removeUnusedQuantifiers phi
                   | otherwise -> Exists x (removeUnusedQuantifiers phi)
      Forall x phi | x `freshIn` phi -> removeUnusedQuantifiers phi
                   | otherwise -> Forall x (removeUnusedQuantifiers phi)

    close :: Formula -> Formula
    close phi = go phi (fv phi) where
      go :: Formula -> [VarName] -> Formula
      go phi = \case
        [] -> phi
        (v:vs) -> go (Exists v phi) vs

    skolemise' :: Formula -> Formula
    skolemise' phi = go phi [] where
      go :: Formula -> [VarName] -> Formula
      go phi vs = case phi of
        (Forall x phi) -> Forall x (go phi (x:vs))
        (Exists x phi) -> apply s (go phi vs) where
          s y | y == x = Fun x (map Var vs)
              | otherwise = Var y
        (And phi psi) -> And (go phi vs) (go psi vs)
        (Or phi psi) -> Or (go phi vs) (go psi vs)
        phi -> phi

prop_skolemise1 :: Bool
prop_skolemise1 = skolemise (Forall "x" $ Exists "y" $ Rel "P" [Var "x", Var "y"] /\ Rel "Q" [Var "y"]) == Forall "x" (And (Rel "P" [Var "x", Fun "y" [Var "x"]]) (Rel "Q" [Fun "y" [Var "x"]]))

type Arity = Int
type Signature = [(FunName, Arity)]

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel _ ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

constants :: Signature -> [Term]
constants s = [Fun c [] | (c, 0) <- s]

nonConstants :: Signature -> Signature
nonConstants = filter (\(_, c) -> c > 0)

sortSignature :: Signature -> Signature
sortSignature = sortBy (comparing snd)

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances phi ts = [apply s phi | s <- functions (fv phi) ts]

prop_groundInstances :: Bool
prop_groundInstances = groundInstances
  (Rel "r" [Var "x", Var "x", Var "y"])
  [Fun "c" [], Fun "d" []]
    == [
      Rel "r" [Fun "c" [],Fun "c" [],Fun "c" []],
      Rel "r" [Fun "d" [],Fun "d" [],Fun "c" []],
      Rel "r" [Fun "c" [],Fun "c" [],Fun "d" []],
      Rel "r" [Fun "d" [],Fun "d" [],Fun "d" []]
      ]
