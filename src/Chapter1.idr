module Chapter1

import Decidable.Equality
import Data.So
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Control.Relation
import Control.Order
import DoublePath

public export
record Tuple where
  constructor MkTuple
  x,y,z,w : Double

data IsPoint : Tuple -> Type where
  Point : (ok : So (w == 1.0)) -> IsPoint (MkTuple x y z w)

data IsVector : Tuple -> Type where
  Vector : (ok : So (w == 0.0)) -> IsVector (MkTuple x y z w)

public export
tuple : (x,y,z,w : Double) -> Tuple
tuple = MkTuple

public export
point : (x,y,z : Double) -> Tuple
point x y z = MkTuple x y z 1.0

export
vector : (x,y,z : Double) -> Tuple
vector x y z = MkTuple x y z 0.0

public export
EPSILON : Double
EPSILON = 0.00001

public export
eq : Double -> Double -> Bool
eq a b = abs (a - b) < EPSILON

public export
[WithEpsilon] Eq Double where
  (==) = eq

public export
Eq Tuple where
  (MkTuple x0 y0 z0 w0) == (MkTuple x1 y1 z1 w1) = and [eq x0 x1, eq y0 y1, eq z0 z1, eq w0 w1]

(+) : Tuple -> Tuple -> Tuple
(+) (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = MkTuple (x1 + x2) (y1 + y2) (z1 + z2) (w1 + w2)

(-) : Tuple -> Tuple -> Tuple
(-) (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = MkTuple (x1 - x2) (y1 - y2) (z1 - z2) (w1 - w2)

(*) : Tuple -> Double -> Tuple
(*) (MkTuple x y z w) s = MkTuple (x * s) (y * s) (z * s) (w * s)

(/) : Tuple -> Double -> Tuple
(/) (MkTuple x y z w) s = MkTuple (x / s) (y / s) (z / s) (w / s)

negate : Tuple -> Tuple
negate (MkTuple x y z w) = MkTuple (-x) (-y) (-z) (-w)

magnitude : Tuple -> Double
magnitude (MkTuple x y z w) = sqrt (x*x + y*y + z*z + w*w)

normalize : Tuple -> Tuple
normalize (MkTuple x y z w) =
  let m = magnitude (MkTuple x y z w)
  in MkTuple (x / m) (y / m) (z / m) (w / m)

dot : Tuple -> Tuple -> Double
dot (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = (x1*x2) + (y1*y2) + (z1*z2) + (w1*w2)

cross : (a,b : Tuple) -> (oka : IsVector a) => (okb : IsVector b) => (r : Tuple ** IsVector r)
cross (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = (vector (y1 * z2 - z1 * y2) (z1 * x2 - x1 * z2) (x1 * y2 - y1 * x2) ** Vector Oh)

-- * Proofs and examples

-- A tuple with w=1.0 is a point
pointTheorem :
  forall x , y , z , a .
  (a === MkTuple x y z 1.0) ->
  ( a.x === x
  , a.y === y
  , a.z === z
  , a.w === 1.0
  , IsPoint a
  , Not (IsVector a)
  )
pointTheorem Refl =
  ( Refl
  , Refl
  , Refl
  , Refl
  , Point Oh
  , \(Vector oh) => absurd oh
  )

-- A tuple with w=0.0 is a vector
vectorTheorem :
  forall x , y , z , a .
  (a === MkTuple x y z 0.0) ->
  ( a.x === x
  , a.y === y
  , a.z === z
  , a.w === 0.0
  , Not (IsPoint a)
  , IsVector a
  )
vectorTheorem Refl =
  ( Refl
  , Refl
  , Refl
  , Refl
  , \(Point oh) => absurd oh
  , Vector Oh
  )

mkPointTheorem : forall x , y , z . IsPoint (point x y z)
mkPointTheorem = Point Oh

mkVectorTheorem : forall x , y , z . IsVector (vector x y z)
mkVectorTheorem = Vector Oh

-- Adding two tuples is pairwise addition of coordinates
addTheorem : (a,b : Tuple) -> a + b === tuple (a.x + b.x) (a.y + b.y) (a.z + b.z) (a.w + b.w)
addTheorem (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = Refl

-- Substracting two tuples is pairwise substraction of coordinates
subTheorem : (a,b : Tuple) -> a - b === tuple (a.x - b.x) (a.y - b.y) (a.z - b.z) (a.w - b.w)
subTheorem (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = Refl

assumptionOfValue : {x,y : Double} -> So (x == y) -> x === y
assumptionOfValue {x,y} oh = believe_me (Refl {a=Double} {x=y})

-- Substracting two points lead to a vector
subPointsTheorem :
  (a,b : Tuple) ->
  (IsPoint a)   ->
  (IsPoint b)   ->
  IsVector (a - b)
subPointsTheorem (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) (Point pa) (Point pb) with (assumptionOfValue pa) | (assumptionOfValue pb)
  _ | ok1 | ok2 = rewrite ok1 in rewrite ok2 in Vector Oh

subVectorPointTheorem :
  (p,v : Tuple) ->
  (IsPoint p)   ->
  (IsVector v)  ->
  IsPoint (p - v)
subVectorPointTheorem (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) (Point pp) (Vector vv) with (assumptionOfValue pp) | (assumptionOfValue vv)
  _ | ok1 | ok2 = rewrite ok1 in rewrite ok2 in Point Oh

subVectorTheorem :
  (v1, v2 : Tuple) ->
  (IsVector v1) ->
  (IsVector v2) ->
  IsVector (v1 - v2)
subVectorTheorem (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) (Vector v1) (Vector v2) with (assumptionOfValue v1) | (assumptionOfValue v2)
  _ | ok1 | ok2 = rewrite ok1 in rewrite ok2 in Vector Oh

-- Negating a tuple is elementwise negation
negateTheorem :
  forall x , y , z , w , t .
  (t === MkTuple x y z w) ->
  (negate t === MkTuple (-x) (-y) (-z) (-w))
negateTheorem Refl = Refl

-- Scaling a vector with s is an elementwise scaling
scaleTheorem :
  forall x , y , z , w , s , t .
  (t === MkTuple x y z w) ->
  (t * s === MkTuple (x * s) (y * s) (z * s) (w * s))
scaleTheorem Refl = Refl

magnitudeExample1 : magnitude (vector 1 0 0) === 1.0
magnitudeExample1 = Refl

magnitudeExample2 : magnitude (vector 0 1 0) === 1.0
magnitudeExample2 = Refl

magnitudeExample3 : magnitude (vector 0 0 1) === 1.0
magnitudeExample3 = Refl

magnitudeExample4 : magnitude (vector 1 2 3) === sqrt 14
magnitudeExample4 = Refl

magnitudeExample5 : magnitude (vector (-1) (-2) (-3)) === sqrt 14
magnitudeExample5 = Refl

-- Magnitude comes from the Pythagoras theorem
magnitudeTheorem :
  forall x , y , z , w , t , m .
  (t === MkTuple x y z w) ->
  (sqrt (x*x + y*y + z*z + w*w) === magnitude t)
magnitudeTheorem Refl = Refl

normalizeExample1 : normalize (vector 4 0 0) === vector 1 0 0
normalizeExample1 = Refl

normalizeExample2 : ((normalize (vector 1 2 3)) == (vector 0.26726 0.53452 0.80178)) === True
normalizeExample2 = Refl

magnitudeNormalizeExample : magnitude (normalize (vector 1 2 3)) === 1.0
magnitudeNormalizeExample = Refl

fourAdditionDRefl :
  {a,b,c,d,a',b',c',d' : Double} ->
  DoublePath a a' -> DoublePath b b' -> DoublePath c c' -> DoublePath d d' ->
  DoublePath (a + b + c + d) (a' + b' + c' + d')
fourAdditionDRefl da db dc dd = CalcWith {leq=DoublePath} $
  |~ a + b + c + d
  <~ (((a + b) + c) + d)
    ... (Ref)  
  <~ (((a + b) + c) + d')
    ... (Cng (((a+b)+c)+) dd)
  <~ (((a + b) + c') + d')
    ... (Cng (\p => ((a+b)+p+d')) dc)
  <~ (((a + b') + c') + d')
    ... (Cng (\p => (((a+p)+c')+d')) db)
  <~ (((a' + b') + c') + d')
    ... (Cng (\p => (((p+b')+c')+d')) da)
  <~ a' + b' + c' + d'
    ... (Ref)

magnitudeOfNormalizedTheorem : (v : Tuple) -> (magnitude (normalize v)) === 1.0
magnitudeOfNormalizedTheorem (MkTuple x y z w) = Calc $
  |~ (magnitude (normalize (MkTuple x y z w)))
  ~~ (magnitude (let m = magnitude (MkTuple x y z w)
                 in MkTuple (x / m) (y / m) (z / m) (w / m)))
    ... (Refl)
  ~~ (magnitude (let m = sqrt (x*x + y*y + z*z + w*w)
                 in MkTuple (x / m) (y / m) (z / m) (w / m)))
    ... (Refl)
  ~~ (magnitude (MkTuple
                  (x / sqrt (x*x + y*y + z*z + w*w))
                  (y / sqrt (x*x + y*y + z*z + w*w))
                  (z / sqrt (x*x + y*y + z*z + w*w))
                  (w / sqrt (x*x + y*y + z*z + w*w))))
    ... (Refl)
  ~~ (sqrt
        ( (x / sqrt (x*x + y*y + z*z + w*w)) * (x / sqrt (x*x + y*y + z*z + w*w))
        + (y / sqrt (x*x + y*y + z*z + w*w)) * (y / sqrt (x*x + y*y + z*z + w*w))
        + (z / sqrt (x*x + y*y + z*z + w*w)) * (z / sqrt (x*x + y*y + z*z + w*w))
        + (w / sqrt (x*x + y*y + z*z + w*w)) * (w / sqrt (x*x + y*y + z*z + w*w))
        ))
    ... (Refl)
  ~~ (sqrt
        ( (x * x) / ((sqrt (x*x + y*y + z*z + w*w)) * (sqrt (x*x + y*y + z*z + w*w)))
        + (y * y) / ((sqrt (x*x + y*y + z*z + w*w)) * (sqrt (x*x + y*y + z*z + w*w)))
        + (z * z) / ((sqrt (x*x + y*y + z*z + w*w)) * (sqrt (x*x + y*y + z*z + w*w)))
        + (w * w) / ((sqrt (x*x + y*y + z*z + w*w)) * (sqrt (x*x + y*y + z*z + w*w)))))
    ... (cong sqrt (doublePathRefl (fourAdditionDRefl DivMul DivMul DivMul DivMul)))
  ~~ (sqrt
        (((x * x) / (x*x + y*y + z*z + w*w)) +
         ((y * y) / (x*x + y*y + z*z + w*w)) +
         ((z * z) / (x*x + y*y + z*z + w*w)) +
         ((w * w) / (x*x + y*y + z*z + w*w))))
    ... (cong sqrt (doublePathRefl (fourAdditionDRefl (DivDen SqrMul) (DivDen SqrMul) (DivDen SqrMul) (DivDen SqrMul))))
  ~~ (sqrt ((x*x + y*y + z*z + w*w) / (x*x + y*y + z*z + w*w)))
    ... (cong sqrt (doublePathRefl (CalcWith {leq=DoublePath} $
          |~ (((x*x)/(x*x+y*y+z*z+w*w))+((y*y)/(x*x+y*y+z*z+w*w))+((z*z)/(x*x+y*y+z*z+w*w))+((w*w)/(x*x+y*y+z*z+w*w)))
          <~ (((((x*x)/(x*x+y*y+z*z+w*w))+((y*y)/(x*x+y*y+z*z+w*w)))+((z*z)/(x*x+y*y+z*z+w*w)))+((w*w)/(x*x+y*y+z*z+w*w)))
            ... (Ref)
          <~ ((((x*x)/(x*x+y*y+z*z+w*w))+((y*y)/(x*x+y*y+z*z+w*w))) +
              (((z*z)/(x*x+y*y+z*z+w*w))+((w*w)/(x*x+y*y+z*z+w*w))))
            ... (AddAsc)
          <~ (((x*x+y*y)/(x*x+y*y+z*z+w*w))+(((z*z)/(x*x+y*y+z*z+w*w))+((w*w)/(x*x+y*y+z*z+w*w))))
            ... (Cng (+(((z*z)/(x*x+y*y+z*z+w*w))+((w*w)/(x*x+y*y+z*z+w*w)))) DivAdd)
          <~ (((x*x+y*y)/(x*x+y*y+z*z+w*w))+(((z*z+w*w)/(x*x+y*y+z*z+w*w))))
            ... (Cng (((x*x+y*y)/(x*x+y*y+z*z+w*w))+) DivAdd)
          <~ (((x*x+y*y)+(z*z+w*w))/(x*x+y*y+z*z+w*w))
            ... (DivAdd)
          <~ ((x*x+y*y+z*z+w*w)/(x*x+y*y+z*z+w*w))
            ... (DivNum (Sym AddAsc)))))
  ~~ (sqrt 1.0)
    ... (cong sqrt (doublePathRefl DivSam))
  ~~ 1.0
    ... (Refl)

dotProductExample : (dot (vector 1 2 3) (vector 2 3 4)) === 20
dotProductExample = Refl

dotProductTheorem :
  forall x1,y1,z1,w1,t1,x2,y2,z2,w2,t2 .
  (t1 === MkTuple x1 y1 z1 w1) ->
  (t2 === MkTuple x2 y2 z2 w2) ->
  (dot t1 t2 === ((x1*x2) + (y1*y2) + (z1*z2) + (w1*w2)))
dotProductTheorem Refl Refl = Refl

crossProductExample :
  forall a,b .
  (a === vector 1 2 3) -> IsVector a =>
  (b === vector 2 3 4) -> IsVector b =>
  ( (fst (cross a b)) === vector (-1) 2 (-1)
  , (fst (cross b a)) === vector 1 (-2) 1
  )
crossProductExample Refl Refl = (Refl, Refl)

crossProductTheorem :
  (a,b : Tuple) ->
  (IsVector a) =>
  (IsVector b) =>
  (fst (cross a b) === negate (fst (cross b a)))
crossProductTheorem (MkTuple x1 y1 z1 w1) (MkTuple x2 y2 z2 w2) = ?tod_1
