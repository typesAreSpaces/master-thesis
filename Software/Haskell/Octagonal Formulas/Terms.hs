module Terms where

-- An Atom is an expression Expr x y
-- where x \elem {-1, 0, 1} and y is a String
data Atom = Expr Int String deriving (Eq, Ord)
-- An Oct is an expression of the form
-- Ineq Atom_1 Atom_2 n that means
-- Atom_1 + Atom_2 \geq n
data Oct = Ineq Atom Atom Int deriving (Eq, Ord)

data Form = Tvalue | Fvalue | Octx

instance Show Atom where
  show (Expr n x) = "(" ++ show n ++ ")*" ++ x

instance Show Oct where
  show (Ineq a1 a2 n) = show a1 ++ " + " ++ show a2 ++ " >= " ++ show n

nameAtom :: Atom -> String
nameAtom (Expr _ x) = x

numberAtom :: Atom -> Int
numberAtom (Expr x _) = x

proj1 :: Oct -> Atom
proj1 (Ineq a _ _) = a

proj2 :: Oct -> Atom
proj2 (Ineq _ a _) = a

proj3 :: Oct -> Int
proj3 (Ineq _ _ a) = a

moveNames :: String -> Oct -> Oct
moveNames s x@(Ineq x1@(Expr n1 s1) x2@(Expr n2 s2) n) = if (s1 == s) then x else Ineq x2 x1 n
