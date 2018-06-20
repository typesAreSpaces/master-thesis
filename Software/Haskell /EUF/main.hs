import Text.Printf
import Control.Exception
import System.CPUTime
import Terms
import UF
import Algorithms
import qualified Data.Set as Set

------------------------------------------------------------------------------------------------------------------
-- Example from [20]
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
------------------------------------------------------------------------------------------------------------------
-- Example 3.1
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
------------------------------------------------------------------------------------------------------------------
-- Example 4.3
alpha3 = [
  Eql (Const "x1") (Const "z1"),
  Eql (Const "z2") (Const "x2"),
  Eql (Const "z3") (Func "f" [Const "x1"]),
  Eql (Func "f" [Const "x2"]) (Const "z4"),
  Eql (Const "x3") (Const "z5"),
  Eql (Const "z6") (Const "x4"),
  Eql (Const "z7") (Func "f" [Const "x3"]),
  Eql (Func "f" [Const "x4"]) (Const "z8")
         ]
beta3 = [
  Eql (Const "z1") (Const "z2"),
  Eql (Const "z5") (Func "f" [Const "z3"]),
  Eql (Func "f" [Const "z4"]) (Const "z6"),
  Eql (Const "y1") (Const "z7"),
  Eql (Const "z8") (Const "y2"),
  NotEq (Const "y1") (Const "y2")
        ]
comConst3 = Set.fromList ["z1", "z2", "z3", "z4", "z5", "z6", "z7", "z8"]
uncomConst3 = Set.fromList ["x1", "x2", "x3", "x4"]
comFunc3 = Set.fromList ["f"]
uncomFunc3 = Set.empty
------------------------------------------------------------------------------------------------------------------
-- Example in Figure 4
alpha4 = [
  Eql (Const "x1") (Const "z1"),
  Eql (Const "z3") (Func "f" [Const "x1"]),
  Eql (Func "f" [Const "z2"]) (Const "x2"),
  Eql (Const "x2") (Const "z4")
         ]
beta4 = [
  Eql (Const "z1") (Const "y1"),
  Eql (Const "y1") (Const "z2"),
  Eql (Const "y2") (Const "z3"),
  Eql (Const "z4") (Const "y3"),
  NotEq (Func "f" [Const "y2"]) (Func "f" [Const "y3"])
        ]
comConst4 = Set.fromList ["z1", "z2", "z3", "z4"]
uncomConst4 = Set.fromList ["x1", "x2"]
comFunc4 = Set.fromList ["f"]
uncomFunc4 = Set.empty
------------------------------------------------------------------------------------------------------------------
-- New Example
alpha5 = [
  Eql (Func "f" [Const "a"]) (Const "u"),
  Eql (Func "f" [Const "b"]) (Const "c"),
  Eql (Func "f" [Const "c"]) (Const "u"),
  Eql (Func "f" [Const "d"]) (Const "d")
         ]
beta5 = [
  Eql (Const "z1") (Const "y1"),
  Eql (Const "y1") (Const "z2"),
  Eql (Const "y2") (Const "z3"),
  Eql (Const "z4") (Const "y3"),
  NotEq (Func "f" [Const "y2"]) (Func "f" [Const "y3"])
        ]
        
comConst5 = Set.fromList ["a", "b", "c", "d"]
uncomConst5 = Set.fromList ["u"]
comFunc5 = Set.empty
uncomFunc5 = Set.fromList ["f"]
------------------------------------------------------------------------------------------------------------------

time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "Computation time: %0.3f sec\n" (diff :: Double)
    return v

main = do
  putStrLn "Example from [20]"
  time $ do {x1 <- return $ getInterpolant alpha comConst comFunc uncomConst uncomFunc; print x1}
  putStrLn "Example 3.1"
  time $ do {x2 <- return $ getInterpolant alpha2 comConst2 comFunc2 uncomConst2 uncomFunc2; print x2}
  putStrLn "Example 4.3"
  time $ do {x3 <- return $ getInterpolant alpha3 comConst3 comFunc3 uncomConst3 uncomFunc3; print x3}
  putStrLn "Example Example in Figure 4"
  time $ do {x4 <- return $ getInterpolant alpha4 comConst4 comFunc4 uncomConst4 uncomFunc4; print x4}
  putStrLn "New Example"
  time $ do {x5 <- return $ getInterpolant alpha5 comConst5 comFunc5 uncomConst5 uncomFunc5; print x5}
