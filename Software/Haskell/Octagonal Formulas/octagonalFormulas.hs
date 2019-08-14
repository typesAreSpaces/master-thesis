data OctagonalForm = Oct Char Integer Char Integer deriving Show

-----------------------------------------------------------------------------------------------------------
-- position : OctagonalForm -> Positive \union {0}
position :: OctagonalForm -> Integer
position (Oct '-' n1 _ (-1)) = 2*n1^2
position (Oct '+' n1 _ (-1)) = 2*n1^2 + 2*n1 + 1

position (Oct '-' n1 '-' n2) = 2*n1^2 + 2*(n2 + 1) - 1
position (Oct '-' n1 '+' n2) = 2*n1^2 + 2*(n2 + 1)

position (Oct '+' n1 '-' n2) = 2*n1^2 + 2*n1 + 1 + 2*(n2 + 1) - 1
position (Oct '+' n1 '+' n2) = 2*n1^2 + 2*n1 + 1 + 2*(n2 + 1)
-- Check
-----------------------------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------------------------
-- numgroup : Positive \union {0} -> Positive \union {0}
numgroup :: Integer -> Integer
numgroup n = floor $ (sqrt $ (fromIntegral n) / 2)

alg1 :: Integer -> Integer -> [Integer] -> [(Integer, Integer)]
alg1 _ _ [] = []
alg1 x y (z : zs) = if (x /= z) then (x, y) : alg1 z 1 zs else alg1 x (y + 1) zs

alg2 = \x -> alg1 (head x) 0 x

testNumGroup = and $ map (\(x, y) -> (2*(2*x + 1) ==  y)) $ alg2 $ map numgroup [0 .. 1000]
-- Check
-----------------------------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------------------------
-- invPosition : Positive \union {0} -> OctagonalForm
invPosition :: Integer -> OctagonalForm
invPosition n = let p = numgroup n in
  if (n < 2*p^2 + 2*p + 1) then
    let p' = 2*p^2 in
      if (n == p') then Oct '-' p  '+' (-1)
      else
        if (mod (n - p') 2 == 0) then Oct '-' p '+' ((ceiling $ (fromIntegral (n - p')) / 2) - 1)
        else Oct '-' p '-' ((ceiling $ (fromIntegral (n - p')) / 2) - 1)
  else
    let p' = 2*p^2 + 2*p + 1 in
      if (n == p') then Oct '+' p '+' (-1)
      else
        if (mod (n - p') 2 == 0) then Oct '+' p '+' ((ceiling $ (fromIntegral (n - p')) / 2) - 1)
        else Oct '+' p '-' ((ceiling $ (fromIntegral (n - p')) / 2) - 1)

testInvPosition = map (\(Oct s1 n1 s2 n2) -> (Oct s1 (n1 + 1) s2 (n2 + 1))) $ map invPosition [0 .. 1000]
-- Check
-----------------------------------------------------------------------------------------------------------          

-----------------------------------------------------------------------------------------------------------          
-- Ultimate test

uTest = map (position . invPosition) [0 .. 1000000] == [0 .. 1000000]

-----------------------------------------------------------------------------------------------------------          
