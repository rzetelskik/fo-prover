module Formula where

import System.IO
import Data.List
import Control.Monad
import Text.Parsec
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Test.QuickCheck hiding (Fun, (===))

import Utils

-- Variable names are just strings
type VarName = String
type FunName = String
type RelName = String

-- enumerate variants of a variable name
variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

data GenTerm a = Var a | Fun FunName [GenTerm a] deriving (Eq, Show)

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
    | Forall VarName Formula deriving (Eq, Show)

-- type Formula = GenFormula VarName

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
              where go sizes = do ts <- sequence $ map f sizes
                                  return $ Fun "f" ts

instance Arbitrary Formula where
  arbitrary = resize 30 $ sized f where
    f 0 = do ts <- arbitrary
             return $ Rel "R" ts
    f size = frequency [
      (1, liftM Not (f (size - 1))),
      (4, do
        size' <- choose (0, size - 1)
        conn <- oneof $ map return [And, Or, Implies, Iff]
        left <- f $ size'
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
x `freshIn` phi = not $ x `elem` vars phi

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