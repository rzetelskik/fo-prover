module Prover where

import Control.Monad
import Control.Monad.State

import qualified Alternator
import qualified Data.HashSet as HashSet
import FirstOrder
import Propositional (satDPLL)
import FirstOrderToPropositional (convert)
import Utils (debug)

removeUniveralQuantifiers :: Formula -> Formula
removeUniveralQuantifiers = \case
    (Forall _ phi) -> removeUniveralQuantifiers phi
    phi -> phi

transform :: Formula -> Formula
transform = removeUniveralQuantifiers . skolemise . Not . generalise

herbrandUniverse :: Signature -> [Term]
herbrandUniverse = Alternator.toList . go . sortSignature
    where
        go s = do
            (n, c) <- Alternator.fromList s
            args <- replicateM c (go s)
            return $ Fun n args

prop_herbrandUniverse1 :: Bool
prop_herbrandUniverse1 = herbrandUniverse (sig (Or (Rel "R" [Var "x", Fun "c" []]) (Rel "R" [Fun "d" [], Var "y"]))) == [Fun "c" [], Fun "d" []]

prop_herbrandUniverse2 :: Bool
prop_herbrandUniverse2 = take 5 ( herbrandUniverse (sig (And (Rel "R" [Var "x", Fun "c" []]) (Not (Rel "R" [Fun "d" [], Fun "f" [Var "y"]]))))) == [Fun "c" [], Fun "d" [], Fun "f" [Fun "c" []], Fun "f" [Fun "d" []], Fun "f" [Fun "f" [Fun "c" []]]]

prover :: FOProver
prover phi = precheckRelations phi' && solve phis
  where
    extendSignature :: Signature -> Signature
    extendSignature s = if null . constants $ s then ("c", 0) : s else s

    gen :: [Formula] -> [[Formula]]
    gen = Alternator.toList . go
      where
        go phis = do
          inf <- Alternator.fromList [1..]
          replicateM inf (Alternator.fromList phis)

    precheckRelations :: Formula -> Bool
    precheckRelations phi = let (prs, nrs) = execState (go phi) ([], []) in (null prs) == (null nrs) where
      go :: Formula -> State ([RelName], [RelName]) ()
      go (Rel r _) = modify (\(prs, nrs) -> (r:prs, nrs))
      go (Not (Rel r _)) = modify (\(prs, nrs) -> (prs, r:nrs))
      go (And phi psi) = do
        go phi
        go psi
      go (Or phi psi) = do
        go phi
        go psi
      go _ = return ()

    solve :: [[Formula]] -> Bool
    solve phis = not (all (satDPLL . convert . foldl And T) phis)

    phi' = transform phi
    signature = extendSignature (sig phi')
    universe = herbrandUniverse signature
    gis = groundInstances phi' universe
    phis = if null (nonConstants signature) then [gis] else gen gis
