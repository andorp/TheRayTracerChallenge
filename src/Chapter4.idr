module Chapter4

import Chapter1
import Chapter3
import Data.Vect
import Testing


translation : (x,y,z : Double) -> Matrix4x4
translation x y z = MkMatrix
  [ [1,0,0,x]
  , [0,1,0,y]
  , [0,0,1,z]
  , [0,0,0,1]
  ]

tests : IO ()
tests = do
  test "Translation example 1" $ do
    t <- Given $ translation 5 (-3) 2
    p <- Given $ point (-3) 4 5
    Then "Point" (t * p == point 2 1 7)
  
  test "Translation example 2" $ do
    t <- Given $ translation 5 (-3) 2
    p <- Given $ point (-3) 4 5
    i <- When "Invertible" $ invertible t
    Then "Inverse" (inverse4 t * p == point (-8) 7 3)

  test "Translation does not effect vectors" $ do
    t <- Given $ translation 5 (-3) 2
    v <- Given $ vector (-3) (-4) 5
    Then "No effect" (t * v == v)

