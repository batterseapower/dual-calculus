module Utilities where

import Control.Arrow ( first, second, (&&&), (***) )

import Data.Unique.Id
import Data.Maybe
import Debug.Trace

import System.IO.Unsafe

import Text.PrettyPrint.HughesPJClass


uncons [] = Nothing
uncons xs = Just (init xs, last xs)

spanRev p xs = case span p (reverse xs) of (sats, unsats) -> (reverse unsats, reverse sats)
