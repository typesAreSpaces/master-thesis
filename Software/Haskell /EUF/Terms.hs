module Terms where

import qualified Data.Set as Set

data Form = Const String | Func String [Form] deriving (Eq, Ord)
data FormPos = ConstPos String String | FuncPos String String [FormPos] deriving (Eq, Ord)
data Atom = Eql Form Form | NotEq Form Form deriving (Eq, Ord)
data AtomPos = EqlPos FormPos FormPos | NotEqPos FormPos FormPos deriving (Eq, Ord)
data HornClause = HornClause [Atom] Atom deriving (Eq, Ord)

instance Show Form where
  show (Const x) = x
  show (Func f args) =
    if (length args == 1) then f ++ "(" ++ show (head args) ++ ")"
    else f ++ "(" ++ foldr (\x y -> show x ++ "," ++ y) "" (init args) ++ show (last args) ++ ")"

instance Show Atom where
  show (Eql x y) = show x ++ " = " ++ show y
  show (NotEq x y) = show x ++ " = " ++ show y

instance Show HornClause where
  show (HornClause xs x) =
    if (length xs == 1) then show (head xs) ++ " -> " ++ show x
    else "(" ++ foldr (\z y -> show z ++ " & " ++ y) "" (init xs) ++ show (last xs) ++ ") -> " ++ show x

toPos :: String -> Form -> FormPos
toPos s (Const x) = ConstPos x s
toPos s (Func f args) = FuncPos f s (map (\(x, y) -> toPos (y : s) x) (zip args ['0' ..]))

toNorm :: FormPos -> Form
toNorm (ConstPos x _) = Const x
toNorm (FuncPos f _ args) = Func f (map toNorm args)

toNormAtom :: AtomPos -> Atom
toNormAtom (EqlPos x y) = Eql (toNorm x) (toNorm y)
toNormAtom (NotEqPos x y) = NotEq (toNorm x) (toNorm y)

isConst :: FormPos -> Bool
isConst (ConstPos _ _) = True
isConst _ = False

nameConst :: Form -> String
nameConst (Const x) = x
nameConst _ = "error"

nameFunc :: Form -> String
nameFunc (Func f _) = f
nameFunc _ = "error"

argsFunc :: Form -> [Form]
argsFunc (Func _ args) = args
argsFunc _ = [Const "error"]

isConst1 :: Form -> Bool
isConst1 (Const _) = True
isConst1 _ = False

allConst :: [FormPos] -> Bool
allConst [] = True
allConst (ConstPos _ _ : xs) = allConst xs
allConst (FuncPos _ _ _ : _) = False

allConst1 :: [Form] -> Bool
allConst1 [] = True
allConst1 (Const _ : xs) = allConst1 xs
allConst1 (Func _  _ : _) = False

antecedentHorn :: HornClause -> [Atom]
antecedentHorn (HornClause a _) = a

consequentHorn :: HornClause -> Atom
consequentHorn (HornClause _ c) = c

transform :: (FormPos, [AtomPos]) -> (FormPos, [AtomPos])
transform (ConstPos x y, r) = (ConstPos x y, [])
transform (FuncPos f g args, r) =
  if (allConst args) then (ConstPos g g, [EqlPos (FuncPos f g args) (ConstPos g g)])
  else (FuncPos f g (map fst w), foldr (++) [] $ map snd w) where w = map (\z -> transform (z, r)) args 

transformT :: FormPos -> [AtomPos] -> [AtomPos]
transformT x y = if (isConst $ fst $ z) then (y ++ snd z) else transformT (fst z) (y ++ snd z) where z = transform (x, y)

transformD :: String -> Form -> [Atom]
transformD s x = map toNormAtom $ transformT (toPos s x) []

needTransformQ :: Form -> Bool
needTransformQ (Const _) = False
needTransformQ (Func _ args) = if (allConst1 args) then False else True

getTerms :: [Atom] -> Set.Set Form
getTerms [] = Set.fromList []
getTerms ((Eql x y) : xs) = Set.insert x (Set.insert y (getTerms xs))
getTerms ((NotEq x y) : xs) = Set.insert x (Set.insert y (getTerms xs))

proj1 :: Atom -> Form
proj1 (Eql x y) = x
proj1 (NotEq x y) = x

proj2 :: Atom -> Form
proj2 (Eql x y) = y
proj2 (NotEq x y) = y

checkEqConst :: Atom -> Bool
checkEqConst (Eql (Const _) (Const _)) = True
checkEqConst _ = False

flattening :: String -> [Atom] -> [Atom]
flattening _ [] = []
flattening s ((Eql x y) : xs) =
  if (needTransformQ x) then
    if (isConst1 y) then let (a, b) = splitAt (length (transformD s x) - 1) (transformD s x) in
      a ++ [Eql (proj1 $ head $ b) y] ++ flattening (s ++ "'") xs
    else transformD s x ++ flattening (s ++ "'") (Eql y (proj2 $ last $ transformD s x) : xs)
  else (Eql x y) : flattening s xs
flattening s ((NotEq x y) : xs) =
  if (needTransformQ x) then
    if (isConst1 y) then let (a, b) = splitAt (length (transformD s x) - 1) (transformD s x) in
      a ++ [NotEq (proj1 $ head $ b) y] ++ flattening (s ++ "'") xs
    else transformD s x ++ flattening (s ++ "'") (NotEq y (proj2 $ last $ transformD s x) : xs)
  else (NotEq x y) : flattening s xs

getConstSym :: [Form] -> [String]
getConstSym [] = []
getConstSym (Const x : xs) = x : getConstSym xs

getConstSymSet :: [Form] -> Set.Set String
getConstSymSet [] = Set.fromList []
getConstSymSet (Const x : xs) = Set.insert x (getConstSymSet xs)

newComSym :: [Atom] -> Set.Set String -> Set.Set String -> (Set.Set String, Set.Set String)
newComSym [] com uncom = (com, uncom)
newComSym ((Eql (Const x) (Const y)) : xs) com uncom =
  if (Set.notMember y com && Set.notMember y uncom) then
    if (Set.member x com) then newComSym xs (Set.insert y com) uncom 
    else newComSym xs com (Set.insert y uncom)
  else newComSym xs com uncom 
newComSym ((Eql (Func f args) (Const y)) : xs) com uncom =
  if (Set.notMember y com && Set.notMember y uncom) then
    if (all (\x -> Set.member x com) (getConstSym args)) then newComSym xs (Set.insert y com) uncom
    else newComSym xs com (Set.insert y uncom)
  else newComSym xs com uncom
newComSym ((NotEq (Const x) (Const y)) : xs) com uncom =
  if (Set.notMember y com && Set.notMember y uncom) then
    if (Set.member x com) then newComSym xs (Set.insert y com) uncom 
    else newComSym xs com (Set.insert y uncom)
  else newComSym xs com uncom
newComSym ((NotEq (Func f args) (Const y)) : xs) com uncom =
  if (Set.notMember y com && Set.notMember y uncom) then
    if (all (\x -> Set.member x com) (getConstSym args)) then newComSym xs (Set.insert y com) uncom
    else newComSym xs com (Set.insert y uncom)
  else newComSym xs com uncom
-- Rest of symbols
newComSym (_ : xs) com uncom = newComSym xs com uncom
