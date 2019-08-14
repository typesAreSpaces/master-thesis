module Algorithms where

import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.Map as Map
import Terms
import UF

inverseLPairs :: [(a, b)] -> [(b, a)]
inverseLPairs [] = []
inverseLPairs ((x, y) : xs) = (y, x) : inverseLPairs xs 

inverseMap :: (Ord b) => Map.Map a b -> Map.Map b a
inverseMap x = Map.fromList $ inverseLPairs $ Map.toList x

semiCartProd :: [a] -> [(a, a)]
semiCartProd [] = []
semiCartProd [x] = []
semiCartProd (x : xs) = map (\y -> (x, y)) xs ++ semiCartProd xs

normalAtom :: [Atom] -> [Atom]
normalAtom [] = []
normalAtom ((Eql (Const x) (Func f args)) : xs) = Eql (Func f args) (Const x) : normalAtom xs
normalAtom (x : xs) = x : normalAtom xs

rmdups :: (Ord a) => [a] -> [a]
rmdups = Set.toList . Set.fromList
-------------------------------------------------------------------------------------------------------------------------------------------
-- Phase I:

cc :: Map.Map Form Int -> DisjointSet -> [Atom] -> DisjointSet
cc mapF dSet [] = dSet
cc mapF dSet ((Eql x y) : xs) = cc mapF (quickUnion ((Map.!) mapF x) ((Map.!) mapF y) dSet) xs
-- Rest of equations: We do not include disequation in the
-- constant congruent process
cc mapF dSet (_ : xs) = cc mapF dSet xs

constantCongruence :: [Atom] -> (DisjointSet, Map.Map Form Int)
constantCongruence eqs = (cc (Map.fromList elements) dSet constEq, Map.fromList elements)
  where
    constEq = filter (\x -> isConst1 (proj1 x) && isConst1 (proj2 x)) eqs
    elements = zip (Set.toList $ getTerms constEq) ([0 ..] :: [Int])
    dSet = let w = length elements in DisjointSet w (Seq.fromList $ [0 .. w - 1]) (Seq.fromList $ take w $ repeat 1)

getEquivClasses :: DisjointSet -> Map.Map Form Int -> [[Form]]
getEquivClasses dSet mapF = map (\x -> map (\y -> (Map.!) (inverseMap mapF) y) x) $
  [[j | j <- [0 .. (length (ids dSet) - 1)],  connected i j dSet] | i <- repr]
  where repr = [i | i <- [0 .. (length (ids dSet) - 1)], findRoot i dSet == i]

-- Due to the function f, we guarantee to get representatives for each
-- class common symbols as much as possible
equivClassesRepr :: Set.Set String -> [[Form]] -> [([Form], Form)]
equivClassesRepr _ [] = []
equivClassesRepr com (x : xs) = (x, f com x) : equivClassesRepr com xs
  where
    f _ [x] = x
    f com ((Const x) : xs) = if (Set.member x com) then (Const x) else f com xs 

-- Due to flattening, Func f args is of the form Func f [Const "x1", ..., Const "xn"]
-- thus, the recursive procedure is correct
replacementForm :: ([Form], Form) -> Form -> Form
replacementForm equiv (Const x) = if (elem (Const x) (fst equiv)) then (snd equiv) else Const x
replacementForm equiv (Func f args) = Func f (map (replacementForm equiv) args)

replacementAtom :: ([Form], Form) -> [Atom] -> [Atom]
replacementAtom _ [] = []
replacementAtom equiv ((Eql x y) : xs) =
  if (replacementForm equiv x /= replacementForm equiv y) then (Eql (replacementForm equiv x) (replacementForm equiv y)) : replacementAtom equiv xs
  else (Eql x y) : replacementAtom equiv xs
replacementAtom equiv ((NotEq x y) : xs) = (NotEq (replacementForm equiv x) (replacementForm equiv y)) : replacementAtom equiv xs

replacement :: [([Form], Form)] -> [Atom] -> [Atom]
replacement [] ys = ys
replacement (x : xs) ys = replacement xs (replacementAtom x ys) 

replaceForm :: [([Form], Form)] -> Form -> Form
replaceForm [] x = x
replaceForm (x : xs) (Const y) = if (elem (Const y) (fst x)) then (snd x) else replaceForm xs (Const y) 

replacementPost :: [([Form], Form)] -> Set.Set String -> [Atom] -> [Atom]
replacementPost _ _ [] = []
replacementPost equiv com (x : xs) =
  if (checkEqConst x) then
    if (Set.member (nameConst $ proj1 x) com) then
      if (Set.member (nameConst $ proj2 x) com) then x : replacementPost equiv com xs
      else (Eql (proj1 x) (replaceForm equiv $ proj2 x)) : replacementPost equiv com xs
    else
      if Set.member (nameConst $ proj2 x) com then (Eql (proj2 x) (replaceForm equiv $ proj1 x)) : replacementPost equiv com xs
      else replacementPost equiv com xs
  else x : replacementPost equiv com xs

step2 :: [Atom] -> Set.Set String -> Set.Set String -> ([Atom], Set.Set String, Set.Set String)
step2 xs com uncom = (rmdups $ filter (\x -> proj1 x /= proj2 x) $ replacementPost equiv com $ replacement equiv xs, newcom, newuncom)
  where
    (dSet, mapF) = constantCongruence xs
    (newcom, newuncom) = newComSym xs com uncom
    equiv = equivClassesRepr newcom (getEquivClasses dSet mapF)

step3 :: [Atom] -> [Atom]
step3 xs = [Eql (proj2 x) (proj2 y) | (x, y) <- semiCartProd xs, not $ isConst1 (proj1 x), proj1 x == proj1 y, proj2 x /= proj2 y]

phase1 :: [Atom] -> Set.Set String -> Set.Set String -> ([Atom], Set.Set String, Set.Set String)
phase1 xs com uncom =
  if (null w2) then (w, com', uncom')
  else phase1 (w ++ w2) com' uncom'
  where
    (w, com', uncom') = step2 xs com uncom
    w2 = step3 w
-------------------------------------------------------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------------------------------------------------------
-- Phase II: 

genHornClause :: String -> [Atom] -> [HornClause]
genHornClause f xs = [HornClause (filter (\x -> proj1 x /= proj2 x) $
                                  zipWith (\x y -> Eql x y) (argsFunc $ proj1 $ fst i) (argsFunc $ proj1 $ snd i)) (Eql (proj2 $ fst i) (proj2 $ snd i))  |
                      i <- semiCartProd $ filter (\x -> nameFunc (proj1 x) == f) xs, 
                      proj1 (fst i) /= proj1 (snd i),
                      proj2 (fst i) /= proj2 (snd i)]

genHornClause2 :: String -> Set.Set String -> [Atom] -> [HornClause]
genHornClause2 f uncom xs = [HornClause (filter (\x -> proj1 x /= proj2 x) $
                                  zipWith (\x y -> Eql x y) (argsFunc $ proj1 $ fst i) (argsFunc $ proj1 $ snd i)) (Eql (proj2 $ fst i) (proj2 $ snd i))  |
                      i <- semiCartProd $ filter (\x -> nameFunc (proj1 x) == f && any (\y -> Set.member (nameConst y) uncom) (argsFunc (proj1 x))) xs, 
                      proj1 (fst i) /= proj1 (snd i),
                      proj2 (fst i) /= proj2 (snd i)]                 

-- Here [String] is the list of uncommon function symbols
elimUncomFuncSym :: [String] -> [Atom] -> [HornClause]
elimUncomFuncSym [] _ = []
elimUncomFuncSym (x : xs) ys = genHornClause x ys ++ elimUncomFuncSym xs ys

-- Here [String] is the list of uncommon function symbols
-- uncom stands for uncommon constant symbols
exposeUncomConst :: [String] -> Set.Set String -> [Atom] -> [HornClause]
exposeUncomConst [] _ _ = []
exposeUncomConst (x : xs) uncom ys = genHornClause2 x uncom ys ++ exposeUncomConst xs uncom ys

-- Here [String] is the list of uncommon function symbols
phase2 :: Set.Set String -> Set.Set String -> Set.Set String -> [Atom] -> [HornClause]
phase2 uncomFunc comFunc uncomConst xs = elimUncomFuncSym (Set.toList uncomFunc) xs
  ++ exposeUncomConst (Set.toList comFunc) uncomConst xs
-------------------------------------------------------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------------------------------------------------------
-- Phase III: Eliminating Uncommon symbols conditionally

doesntAppearForm :: String -> Form -> Bool
doesntAppearForm s (Const x) = s /= x
doesntAppearForm s (Func f args) = foldr (&&) True $ map (\x -> doesntAppearForm s x) args

doesntAppearAtom :: String -> Atom -> Bool
doesntAppearAtom s (Eql x y) = doesntAppearForm s x && doesntAppearForm s y
doesntAppearAtom s (NotEq x y) = doesntAppearForm s x && doesntAppearForm s y

doesntAppear :: String -> HornClause -> Bool
doesntAppear s (HornClause conj consequent) = foldr (&&) True $ map (doesntAppearAtom s) (consequent : conj)

-- [Since HornClause at this point are of the form [c1 = e1 \land ... \land ck = ek] => c = e
-- where ci, ei, c, and e are constants, then we only check for constant symbols
checkCond7 :: String -> [HornClause] -> Bool
checkCond7 _ [] = True
checkCond7 s (x : xs) =
  if ((nameConst $ proj1 $ w) == s || (nameConst $ proj2 $ w) == s) then False
  else checkCond7 s xs where w = consequentHorn x

-- Here [String] here denotes the list of uncommon constants
deleteUncomConstHorn :: [String] -> [HornClause] -> [HornClause]
deleteUncomConstHorn [] xs = xs
deleteUncomConstHorn (y : ys) xs =
  if (checkCond7 y xs) then deleteUncomConstHorn ys (filter (\x -> doesntAppear y x) xs)
  else deleteUncomConstHorn ys xs

deleteUncomConst :: [String] -> [String] -> [HornClause] ->[Atom] -> ([String], [HornClause], [Atom])
deleteUncomConst [] s hs xs = (s, hs, xs)
deleteUncomConst (y : ys) s hs xs =
  if (checkCond7 y hs) then deleteUncomConst ys s (filter (\x -> doesntAppear y x) hs) (filter (\x -> doesntAppearAtom y x) xs)
  else deleteUncomConst ys (y : s) hs xs

conditionalRewriting :: String -> Set.Set String -> [HornClause] -> [HornClause] -> ((Bool, HornClause), ([HornClause], [HornClause]))
conditionalRewriting s uncom ys [] = ((False, HornClause [] (Eql (Const "x") (Const "x"))), (ys, []))
conditionalRewriting s uncom ys (x : xs) =
  if ((nameConst $ proj1 w) == s && Set.notMember (nameConst $ proj2 w) uncom) then
    if (foldr (&&) True $ map (\x1 -> Set.notMember (nameConst $ proj1 x1) uncom && Set.notMember (nameConst $ proj2 x1) uncom) (antecedentHorn x)) then ((True, HornClause (antecedentHorn x) (Eql (proj2 w) (proj1 w))), (ys, xs))
    else conditionalRewriting s uncom (x : ys) xs
  else
    if ((nameConst $ proj2 w) == s && Set.notMember (nameConst $ proj1 w) uncom) then
       if (foldr (&&) True $  map (\x1 -> Set.notMember (nameConst $ proj1 x1) uncom && Set.notMember (nameConst $ proj2 x1) uncom) (antecedentHorn x)) then ((True, x), (ys, xs))
       else conditionalRewriting s uncom (x : ys) xs
    else conditionalRewriting s uncom (x : ys) xs
  where
    w = consequentHorn x

candidatesRewrite :: Set.Set String -> [HornClause] -> [HornClause]
candidatesRewrite uncom [] = []
candidatesRewrite uncom ((HornClause a b) : xs) =
  if (Set.member (nameConst $ proj1 b) uncom) then
    if (Set.notMember (nameConst $ proj2 b) uncom) then HornClause a (Eql (proj2 b) (proj1 b)) : candidatesRewrite uncom xs
    else candidatesRewrite uncom xs
  else
    if (Set.member (nameConst $ proj2 b) uncom) then HornClause a b : candidatesRewrite uncom xs
    else candidatesRewrite uncom xs

elimUncomConst :: Set.Set String -> [Atom] -> [HornClause] -> [HornClause] -> ([Atom], [HornClause])
elimUncomConst uncom as [] hs = (as, hs)
elimUncomConst uncom as [x] hs = elimUncomConst uncom (filter (\x1 -> doesntAppearAtom w x1) as) [] (asToHc ++ map (\x1 -> if (doesntAppear w x1) then x1 else
                         (HornClause
                          (antecedentHorn x ++ antecedentHorn x1)
                          (head $ replacementAtom ([proj1 w1, proj2 w1], proj1 w1) $ [consequentHorn x1]) ) ) hs)
  where
    w1 = consequentHorn x
    w = nameConst $ proj2 $ w1
    asToHc = map (\x1 -> HornClause (antecedentHorn x) (head $ replacementAtom ([proj1 w1, proj2 w1], proj1 w1) [x1])) (filter (\x1 -> not $ doesntAppearAtom w x1) as)
    
elimUncomConst uncom as (x : xs) hs = elimUncomConst uncom (filter (\x1 -> doesntAppearAtom w x1) as) xs (hs ++ asToHc ++ map (\x1 -> if (doesntAppear w x1) then x1 else
                         (HornClause
                          (antecedentHorn x ++ antecedentHorn x1)
                          (head $ replacementAtom ([proj1 w1, proj2 w1], proj1 w1) $ [consequentHorn x1]) ) ) hs)
  where
    w1 = consequentHorn x
    w = nameConst $ proj2 $ w1
    asToHc = map (\x1 -> HornClause (antecedentHorn x) (head $ replacementAtom ([proj1 w1, proj2 w1], proj1 w1) [x1])) (filter (\x1 -> not $ doesntAppearAtom w x1) as)
-------------------------------------------------------------------------------------------------------------------------------------------

getInterpolant :: [Atom] -> Set.Set String -> Set.Set String -> Set.Set String -> Set.Set String -> ([Atom], [HornClause])
getInterpolant alpha commonSymConst commonSymFunc unCommonSymConst unCommonSymFunc = (z, z'')
  where
    -- Flattening
    x = flattening "e" (normalAtom alpha)
    -- Phase I
    (x', com, uncom) = phase1 x commonSymConst unCommonSymConst
    -- Phase II
    x'' = phase2 unCommonSymFunc commonSymFunc uncom x'
    -- Phase III
    (uncom', y, y') = deleteUncomConst (Set.toList uncom) [] x'' x'
    (z, z') = elimUncomConst (Set.fromList uncom') y' (candidatesRewrite (Set.fromList uncom') y) y
    z'' = filter (\x -> Set.notMember (nameConst $ proj1 $ consequentHorn x) (Set.fromList uncom') && Set.notMember (nameConst $ proj2 $ consequentHorn x) (Set.fromList uncom')) $ rmdups z'
