module Propositional where

import Data.List
import qualified Data.HashSet as HashSet
import Control.Monad
import Control.Monad.State
import Test.QuickCheck
import Utils (update, converge)

-- Variable names are just strings
type PropName = String

-- generation of fresh variable names
fresh :: [PropName] -> PropName
fresh vars = head $ filter (not . (`elem` vars)) $ map (("p"++) . show) [0..]

data Formula =
      T
    | F
    | Prop PropName -- atomic formulas
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Ord, Show)

p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, -->
(\/) = Or
(∨) = Or -- input with "\or"
(-->) = Implies

infixr 4 <-->
(<-->) = Iff

instance Arbitrary Formula where
    arbitrary = sized f where

      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, fmap Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

    shrink (Not phi) = [phi]
    shrink (Or phi psi) = [phi, psi]
    shrink (And phi psi) = [phi, psi]
    shrink (Implies phi psi) = [phi, psi]
    shrink (Iff phi psi) = [phi, psi]
    shrink _ = []

type Valuation = PropName -> Bool

eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) rho = rho p
eval (Not phi) rho = not (eval phi rho)
eval (And phi psi) rho = eval phi rho && eval psi rho
eval (Or phi psi) rho = eval phi rho || eval psi rho
eval (Implies phi psi) rho = not (eval phi rho) || eval psi rho
eval (Iff phi psi) rho = eval phi rho == eval psi rho

variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi


valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update rho x True, update rho x False] | rho <- valuations xs]

type SATSolver = Formula -> Bool

satisfiable :: SATSolver
satisfiable phi = or [eval phi rho | rho <- valuations (variables phi)]

tautology :: Formula -> Bool
tautology phi = and [eval phi rho | rho <- valuations (variables phi)]

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf r@(Prop p) = r
nnf (Not phi) = case nnf phi of
  T -> F
  F -> T
  Not phi' -> phi'
  Or phi' psi' -> And (nnf (Not phi')) (nnf (Not psi'))
  And phi' psi' -> Or (nnf (Not phi')) (nnf (Not psi'))
  phi' -> Not phi'
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) = nnf ((phi --> psi) /\ (psi --> phi))

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type CNFClause = [Literal]
type CNF = [CNFClause]

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)

positiveLiterals :: CNFClause -> HashSet.HashSet PropName
positiveLiterals ls = HashSet.fromList [p | Pos p <- ls]

negativeLiterals :: CNFClause -> HashSet.HashSet PropName
negativeLiterals ls = HashSet.fromList [p | Neg p <- ls]

literals :: [Literal] -> HashSet.HashSet PropName
literals ls = HashSet.union (positiveLiterals ls) (negativeLiterals ls)

cnf :: Formula -> CNF
cnf = go . nnf where
  go T = []
  go F = [[]]
  go (Prop p) = [[Pos p]]
  go (Not (Prop p)) = [[Neg p]]
  go (phi `And` psi) = go phi ++ go psi
  go (phi `Or` psi) = [as ++ bs | as <- go phi, bs <- go psi]
  go _ = error "unexpected formula"

equiSatisfiable :: Formula -> Formula -> Bool
equiSatisfiable phi psi = satisfiable phi == satisfiable psi

ecnf :: Formula -> CNF
ecnf phi = cnf $ evalState (transform phi) (variables phi)
  where
    transform phi = do
      (x, phi') <- transform' phi
      return $ foldr1 And (x:phi')

    transform' = \case
      Not phi -> do
        vars <- get
        let var = fresh vars
        put (var:vars)
        (x, phi') <- transform' phi
        let self = Prop var
        return (self, Iff self (Not x):phi')
      And phi psi -> transform'' And phi psi
      Or phi psi -> transform'' Or phi psi
      Implies phi psi -> transform'' Implies phi psi
      Iff phi psi -> transform'' Iff phi psi
      phi -> do
        return (phi, [])

    transform'' op phi psi = do
        vars <- get
        let var = fresh vars
        put (var:vars)
        (l, phi') <- transform' phi
        (r, psi') <- transform' psi
        let self = Prop var
        return (self, Iff self (op l r) : (phi' ++ psi'))

prop_ecnf :: Formula -> Bool
prop_ecnf phi = equiSatisfiable phi (cnf2formula $ ecnf phi)

removeTautologies :: CNF -> CNF
removeTautologies = filter (\xs -> null $ HashSet.intersection (positiveLiterals xs) (negativeLiterals xs))

prop_removeTautologies :: Bool
prop_removeTautologies = removeTautologies [[Pos "p", Neg "p"], [Pos "p", Pos "q"], [Pos "q", Neg "q"]] == [[Pos "p", Pos "q"]]

oneLiteral :: CNF -> CNF
oneLiteral = converge oneLiteral'
  where
    oneLiteral' :: CNF -> CNF
    oneLiteral' cnf = foldr clear cnf (singles cnf)

    singles :: CNF -> [Literal]
    singles = concat . filter (\xs -> length xs == 1)

    clear :: Literal -> CNF -> CNF
    clear l = map (filter (/= opposite l)) . filter (notElem l)

prop_oneLiteral :: Bool
prop_oneLiteral =
  oneLiteral
    [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] ==
    [[Pos "r",Pos "s"]] &&
  oneLiteral
    [[Pos "p"],[Pos "p1"],[Neg "p",Pos "q"],[Pos "p1",Pos "p0"],[Pos "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "q0",Neg "p"],[Neg "s",Neg "p",Pos "p0"]] ==
    [[Neg "p0",Pos "s"],[Neg "s",Pos "p0"]] &&
  oneLiteral
    [[Pos "q"],[Pos "p0"],[Neg "p0",Pos "s"],[Neg "p0"]] ==
    [[]]

affirmativeNegative :: CNF -> CNF
affirmativeNegative cnf = filter (null . HashSet.intersection pureAll . HashSet.fromList . map literal2var) cnf
  where
    ps = foldr (HashSet.union . positiveLiterals) HashSet.empty cnf
    ns = foldr (HashSet.union . negativeLiterals) HashSet.empty cnf
    pureAll = HashSet.union (HashSet.difference ps ns) (HashSet.difference ns ps)

prop_affirmativeNegative :: Bool
prop_affirmativeNegative =
  affirmativeNegative
    [[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Neg "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  null (affirmativeNegative
    [[Pos "p", Pos "q"], [Pos "p", Neg "q"]])

resolution :: CNF -> CNF
resolution [] = []
resolution ([]:_) = [[]]
resolution cnf@((p:_):_) = filter (\c -> notElem p c && notElem (opposite p) c) cnf ++
    liftM2 (++) (map (filter (p /=)) (filter (elem p) cnf)) (map (filter (opposite p /=)) (filter (elem (opposite p)) cnf))

prop_resolution :: Bool
prop_resolution = resolution [[Pos "p", Pos "q"],[Neg "p", Neg "q"]] == [[Pos "q", Neg "q"]]

dp :: CNF -> Bool
dp [] = True
dp cnf | [] `elem` cnf = False
       | otherwise = dp (resolution (converge (converge affirmativeNegative . converge oneLiteral . removeTautologies) cnf))

satDP :: SATSolver
satDP form = dp cnf where
  cnf = ecnf form

