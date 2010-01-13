module Ids(
    module Data.Unique.Id,
    
    IdM, runIdM,
    idSupply, fresh
  ) where

import Control.Monad

import Data.Unique.Id


newtype IdM a = IdM { unIdM :: IdSupply -> a }

instance Functor IdM where
    fmap = liftM

instance Monad IdM where
    return = IdM . const
    mx >>= fxmy = IdM $ \ids -> case splitIdSupply ids of (ids1, ids2) -> unIdM (fxmy (unIdM mx ids1)) ids2

runIdM :: IdSupply -> IdM a -> a
runIdM = flip unIdM

idSupply :: IdM IdSupply
idSupply = IdM id

fresh :: String -> IdM String
fresh x = fmap (\ids -> x ++ "_" ++ show (idFromSupply ids)) idSupply
