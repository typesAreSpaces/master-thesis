module Algorithms where
import Terms
import qualified Data.List as List

semiCardProd :: [a] -> [(a, a)]
semiCardProd [] = []
semiCardProd [x] = []
semiCardProd (x : xs) = map (\y -> (x, y)) xs ++ semiCardProd xs

elim :: [String] -> [Oct] -> [Oct]
elim [] oct = oct
elim (x : xs) oct = elim xs (w3 ++ (oct List.\\ w))
  where
    w = filter (\(Ineq a1 a2 n) -> nameAtom a1 == x || nameAtom a2 == x) oct
    w1 = semiCardProd $ map (moveNames x) w
    w2 = filter (\(x, y) -> numberAtom (proj1 x) == -1*(numberAtom (proj1 y))) w1
    -- Since a \elem {-1, 0, 1}, then each step completely removes a given symbol
    -- iff exists Inequalities with different signs for that symbol
    w3 = map (\(x, y) -> Ineq (proj2 x) (proj2 y) (proj3 x + proj3 y)) w2
{-
elim2 :: [String] -> [Oct] -> [Oct]
elim2 ss xs if (xs == xs') then deleteSym ss xs' else newIneq
  where
    xs' = 
-}
preprocess2 :: [Oct] -> [Oct]
preprocess2 [] = []
preprocess2 (x@(Ineq a1 a2 n1) : xs) = w1 : preprocess2 (xs List.\\ w)
  where
    w = filter (\(Ineq b1 b2 n2) -> a1 == b1 && a2 == b2) xs
    w1 = Ineq a1 a2 (foldr min 1000 $ map (\(Ineq b1 b2 n2) -> n2) w)

interpolant :: [String] -> [Oct] -> [Oct]
interpolant xs oct = elim xs (preprocess2 oct)
