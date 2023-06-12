module FirstOrderToPropositional where

import Control.Monad.State
import Data.Functor
import qualified Data.Map as M

import qualified FirstOrder as FO
import qualified Propositional as P

convert :: FO.Formula -> P.Formula
convert phi = evalState (go phi) M.empty
    where
        go :: FO.Formula -> State (M.Map FO.Formula P.PropName) P.Formula
        go = \case
            FO.T -> return P.T
            FO.F -> return P.F
            r@(FO.Rel _ _) -> do
                s <- get
                case M.lookup r s of
                    Nothing -> do
                        let pn = P.fresh (M.elems s)
                        put (M.insert r pn s)
                        return $ P.Prop pn
                    Just pn -> return $ P.Prop pn
            (FO.Not phi) -> go phi <&> P.Not
            (FO.Or phi psi) -> do
                phi' <- go phi
                psi' <- go psi
                return $ P.Or phi' psi'
            (FO.And phi psi) -> do
                phi' <- go phi
                psi' <- go psi
                return $ P.And phi' psi'
            (FO.Implies phi psi) -> do
                phi' <- go phi
                psi' <- go psi
                return $ P.Implies phi' psi'
            (FO.Iff phi psi) -> do
                phi' <- go phi
                psi' <- go psi
                return $ P.Iff phi' psi'
            _ -> undefined
