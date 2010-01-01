module Utilities where


uncons [] = Nothing
uncons xs = Just (init xs, last xs)

spanRev p xs = case span p (reverse xs) of (sats, unsats) -> (reverse unsats, reverse sats)


data InfiniteTree a = Node { tree_node :: a, tree_left :: InfiniteTree a, tree_right :: InfiniteTree a }

flattenInfiniteTree :: InfiniteTree a -> [a]
flattenInfiniteTree (Node x t1 _) = x : flattenInfiniteTree t1

splitInfiniteTree :: InfiniteTree a -> [InfiniteTree a]
splitInfiniteTree (Node _ t1 t2) = t1 : splitInfiniteTree t2

filterInfiniteTree :: (a -> Bool) -> InfiniteTree a -> InfiniteTree a
filterInfiniteTree p (Node x t1 t2) | p x       = Node x (filterInfiniteTree p t1) (filterInfiniteTree p t2)
                                    | otherwise = filterInfiniteTree p t1
