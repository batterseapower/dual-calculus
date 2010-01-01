module Utilities where


uncons [] = Nothing
uncons xs = Just (init xs, last xs)

spanRev p xs = case span p (reverse xs) of (sats, unsats) -> (reverse unsats, reverse sats)
