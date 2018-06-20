import Terms
import UF
import Algorithms
import qualified Data.Set as Set

------------------------------------------------------------------------------------------------------------------
alpha = [
  Eql (Const "x11") (Const "y11"),
  Eql (Func "f" [Const "z1", Const "v"]) (Const "s1"),
  Eql (Func "f" [Const "z2", Const "v"]) (Const "s2"),
  Eql (Func "f" [Func "f" [Const "y1", Const "v"], Func "f" [Const "y2", Const "v"]]) (Const "t")
  ]

comConst = Set.fromList ["x11", "y11", "z1", "z2", "y1", "y2", "s1", "s2", "t"]
comFunc = Set.fromList ["f"]
uncomConst = Set.fromList ["v"]
uncomFunc = Set.empty

(a, b) = getInterpolant alpha comConst comFunc uncomConst uncomFunc

------------------------------------------------------------------------------------------------------------------
alpha2 = [
  Eql (Const "z1") (Const "x1"),
  Eql (Const "x1") (Const "z2"),
  Eql (Const "z2") (Const "x2"),
  Eql (Const "x2") (Func "f" [Const "z3"]),
  Eql (Func "f" [Const "z3"]) (Const "x3"),
  Eql (Const "x3") (Const "z4"),
  Eql (Func "f" [Const "z2"]) (Const "x2"),
  Eql (Const "x2") (Const "z3")
         ]
beta2 = [
  Eql (Const "z1") (Const "y1"),
  Eql (Const "y1") (Func "f" [Const "z2"]),
  Eql (Func "f" [Const "z2"]) (Const "y2"),
  Eql (Const "y2") (Const "z3"),
  Eql (Const "z3") (Const "y3"),
  Eql (Const "z2") (Const "y2"),
  Eql (Const "y2") (Func "f" [Const "z3"]),
  NotEq (Const "y3") (Const "z4")
        ]         

comConst2 = Set.fromList ["z1", "z2", "z3", "z4"]
uncomConst2 = Set.fromList["x1", "x2", "x3", "y1", "y2", "y3"]
comFunc2 = Set.fromList ["f"]
uncomFunc2 = Set.empty

(a2, b2) = getInterpolant alpha2 comConst2 comFunc2 uncomConst2 uncomFunc2

------------------------------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------
