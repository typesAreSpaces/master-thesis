import Terms
import Algorithms
-----------------------------------------------
-- Example 4.26
alpha1 = [
  Ineq (Expr (1) "x1") (Expr (-1) "x2") (-4),
  Ineq (Expr (-1) "x2") (Expr (-1) "x3") (5),
  Ineq (Expr (1) "x2") (Expr (1) "x6") (4),
  Ineq (Expr (1) "x2") (Expr (1) "x5") (-3)
  ]

x1 = elim ["x2"] alpha1
------------------------------------------------
-- Example 4.17
alpha2 = [
  Ineq (Expr (-1) "x2") (Expr (-1) "x1") (-3),
  Ineq (Expr (1) "x1") (Expr (1) "x3") (-1),
  Ineq (Expr (-1) "x3") (Expr (-1) "x4") (6),
  Ineq (Expr (1) "x5") (Expr (1) "x4") (-1)
         ]
x2 = elim ["x1"] alpha2         
------------------------------------------------
-- Example 4.20
alpha3 = [
  Ineq (Expr (1) "x3") (Expr (-1) "x1") (-2),
  Ineq (Expr (-1) "x6") (Expr (-1) "x4") (0),
  Ineq (Expr (1) "x4") (Expr (-1) "x5") (0)
         ]
x3 = elim ["x4"] alpha3         
------------------------------------------------
-- Example 4.22
alpha4 = [
  Ineq (Expr (1) "x1") (Expr (-1) "x2") (-4),
  Ineq (Expr (1) "x2") (Expr (1) "x6") (4),
  Ineq (Expr (-1) "x4") (Expr (-1) "x6") (0),
  Ineq (Expr (-1) "x1") (Expr (1) "x3") (-2)
         ]
x4 = elim ["x1", "x6"] alpha4         
------------------------------------------------
-- Example 4
alpha5 = [
  Ineq (Expr (1) "x1") (Expr (-1) "x2") (-4),
  Ineq (Expr (1) "x2") (Expr (1) "x6") (4),
  Ineq (Expr (-1) "x1") (Expr (1) "x3") (-2),
  Ineq (Expr (-1) "x2") (Expr (-1) "x3") (5)
         ]
x5 = elim ["x1", "x3"] alpha5         
------------------------------------------------
-- Example 4.24
alpha6 = [
  Ineq (Expr (1) "x1") (Expr (-1) "x2") (-4),
  Ineq (Expr (1) "x2") (Expr (1) "x6") (4),
  Ineq (Expr (-1) "x1") (Expr (1) "x3") (-2),
  Ineq (Expr (-1) "x2") (Expr (-1) "x3") (5),
  Ineq (Expr (1) "x2") (Expr (1) "x5") (-3)
         ]
x6 = elim ["x1", "x2", "x3"] alpha6         
------------------------------------------------
