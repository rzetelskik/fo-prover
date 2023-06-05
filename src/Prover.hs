module Prover where

import Control.Monad
import Control.Monad.State

import qualified Alternator
import FirstOrder
import Propositional (sat_DP)
import FirstOrderToPropositional (convert)

remove_universal_quantifiers :: Formula -> Formula
remove_universal_quantifiers = \case
    (Forall _ phi) -> remove_universal_quantifiers phi
    phi -> phi

transform :: Formula -> Formula
transform = remove_universal_quantifiers . skolemise . Not . generalise

aedecide :: FOProver
aedecide = not . sat . (foldl And T) . gi . transform
  where
    gi :: Formula -> [Formula]
    gi phi = groundInstances phi (consts phi)
      where
        consts :: Formula -> [Term]
        consts phi = case constants . sig $ phi of
          [] -> [Fun "dummy" []]
          cs -> cs

prop_aedecide :: Bool
prop_aedecide = foldr ((&&) . aedecide) True [forallImpliesExists, lem, swap]
    where
        t x y = Rel "t" [Var x, Var y]

        forallImpliesExists = Forall "x" (Rel "r" [Var "x"]) --> Exists "x" (Rel "r" [Var "x"])
        lem = Forall "x" $ Forall "y" $ t "x" "y" ∨ (Not $ t "x" "y")
        swap = Exists "x" (Forall "y" $ t "x" "y") --> Forall "y" (Exists "x" $ t "x" "y")

herbrandUniverse :: Signature -> [Term]
herbrandUniverse = Alternator.toList . go
    where
        go s = do
            (n, c) <- Alternator.fromList s
            args <- replicateM c (go s)
            return $ Fun n args

prop_herbrandUniverse1 :: Bool
prop_herbrandUniverse1 = (herbrandUniverse (sig (Or (Rel "R" [Var "x", Fun "c" []]) (Rel "R" [Fun "d" [], Var "y"])))) == [Fun "c" [], Fun "d" []]

prop_herbrandUniverse2 :: Bool
prop_herbrandUniverse2 = take 5 ( (herbrandUniverse (sig (And (Rel "R" [Var "x", Fun "c" []]) (Not (Rel "R" [Fun "d" [], Fun "f" [Var "y"]])))))) == [Fun "c" [], Fun "d" [], Fun "f" [Fun "c" []], Fun "f" [Fun "d" []], Fun "f" [Fun "f" [Fun "c" []]]]

prover :: FOProver
prover phi = solve phis
  where
    extendSignature :: Signature -> Signature
    extendSignature s = if null . constants $ s then ("c", 0) : s else s

    gen :: [Formula] -> [[Formula]]
    gen = Alternator.toList . go
      where
        go phis = do 
          inf <- Alternator.fromList [1..]
          replicateM inf (Alternator.fromList phis)
    
    solve :: [[Formula]] -> Bool
    solve phis = or (map (not . sat_DP . convert . (foldl And T)) phis)

    phi' = transform phi
    signature = extendSignature (sig phi')
    universe = herbrandUniverse signature
    gis = groundInstances phi' universe
    phis = if null (nonConstants signature) then [gis] else gen gis