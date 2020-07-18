module Main where 

m_ord :: Int -> Int -> Bool
m_ord x y = abs x > abs y 
  || (abs x == abs y && x > y)

p_ord :: (Int, Int) -> (Int, Int) -> Bool
p_ord (x1, y1) (x2, y2) = (m_ord x1 x2) 
  || (x1 == x2 && m_ord y1 y2)

data Inequality = Inequality Int Int

instance Show Inequality where
  show (Inequality x y) = 
    (if x < 0 then "-" else "") ++ "x_{" ++ (show $ abs x) ++ "}"
    ++ (if y < 0 then " - " else " + ") ++ "x_{" ++ (show $ abs y) ++ "}"

instance Eq Inequality where
  Inequality x1 y1 == Inequality x2 y2 = 
    x1 == x2 && y1 == y2

instance Ord Inequality where 
  ine1@(Inequality x1 y1) <= ine2@(Inequality x2 y2) = 
    ine1 == ine2 || p_ord (x2, y2) (x1, y1)

qs :: Ord a => [a] -> [a]
qs [] = []
qs (x : xs) = (qs lesser) ++ [x] ++ (qs greater) 
  where 
    lesser  = filter (<= x) xs
    greater = filter (not . (<= x)) xs

inequalityListToLatex :: [Inequality] -> String
inequalityListToLatex x = "$" ++ aux 0 x ++ "$"
  where 
    aux c []       = "" 
    aux c (x : xs) = show x ++ " \\leq b_{" 
      ++ show c ++ "}, " 
      ++ aux (c + 1) xs

all_utvpi_ineqs lim = 
  (Inequality 0 0) : [Inequality x y | 
    x <- [-lim .. lim], y <- [-lim .. lim], 
    abs x > abs y, not (x == 0)]

--test = map (\(x, y) -> Inequality x y) [(3, 2), (3, -1), (0, 0), (2, 1), (5, 4), (5, -3)] 
test = all_utvpi_ineqs 3 
--test = all_utvpi_ineqs 4 

main :: IO ()
main = putStrLn . inequalityListToLatex . qs $ test
