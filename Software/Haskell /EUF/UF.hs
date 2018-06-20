module UF where
-- http://jng.imagine27.com/index.php/2012-08-22-144618_purely-functional-data-structures-algorithms-union-find-haskell.html
-- Disjoint set data type (weighted and using path compression).
-- O((M+N)lg*N + 2MlogN) worst-case union time (practically O(1))
-- For M union operations on a set of N elements.
-- O((M+N)lg*N) worst-case find time (practically O(1))
-- For M connected(find) operations on a set of N elements.
-- IMPORTANT: ids should be of the form `[0 .. count - 1]'
-- Initially, sizes should be of the form `take count $ repeat 1'
import Data.Sequence 

data DisjointSet = DisjointSet
     { count :: Int, ids :: (Seq Int), sizes :: (Seq Int) }
     deriving (Read,  Show)

-- Return id of root object
findRoot :: Int -> DisjointSet -> Int
findRoot p set | p == parent = p
               | otherwise   = findRoot parent set
               where
                parent = index (ids set) p

-- Are objects P and Q connected ?
connected :: Int -> Int -> DisjointSet -> Bool
connected p q set = (findRoot p set) == (findRoot q set)

-- Replace sets containing P and Q with their union
quickUnion :: Int -> Int -> DisjointSet -> DisjointSet
quickUnion p q set | i == j = set
                   | otherwise = DisjointSet (count set - 1) rids rsizes
                     where
                        (i, j)   = (findRoot p set, findRoot q set)
                        (i1, j1) = (index (sizes set) i, index (sizes set) j)
                        -- Always make smaller root point to the larger one
                        (rids, rsizes) = if (i1 < j1) 
                                         then (update i j (ids set), update j (i1 + j1) (sizes set))
                                         else (update j i (ids set), update i (i1 + j1) (sizes set))
                                           
