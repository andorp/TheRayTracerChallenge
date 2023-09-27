module DoublePath

import Data.So
import Control.Relation
import Control.Order

||| Relation on Double equality from theoretical point of view.
|||
||| Although we define this relation, but this is not true as operations
||| on Doubles are not safe. But from theoretical point of view these
||| associations should hold and the end result.
public export
data DoublePath : Double -> Double -> Type where
  NegZ   : DoublePath 0.0 (-0.0)
  EqR    : x === y     -> DoublePath x y
  EqS    : So (x == y) -> DoublePath x y
  Cng    : (f :  Double -> Double) -> DoublePath x y -> DoublePath (f x) (f y)
  Ref    : DoublePath x x
  Sym    : DoublePath x y -> DoublePath y x
  Trn    : DoublePath x y -> DoublePath y z -> DoublePath x z
  AddUnL : DoublePath (0.0 + x) x
  AddUnR : DoublePath (x + 0.0) x
  AddCom : DoublePath (x + y) (y + x)
  AddAsc : DoublePath ((x + y) + z) (x + (y + z))
  MulUnL : DoublePath (1.0 * x) x
  MulUnR : DoublePath (x * 1.0) x
  MulCom : DoublePath (x * y) (y * x)
  MulAsc : DoublePath ((x * y) * z) (x * (y * z))
  DivUni : DoublePath (x / 1) x
  DivAdd : DoublePath ((x / z) + (y / z)) ((x + y) / z)
  DivMul : DoublePath ((x1 / z1) * (x2 / z2)) ((x1 * x2) / (z1 * z2))
  DivSam : DoublePath (x / x) 1.0
  DivNum : DoublePath x y -> DoublePath (x / z) (y / z)
  DivDen : DoublePath x y -> DoublePath (z / x) (z / y)
  SqrMul : DoublePath (sqrt x * sqrt x) x

public export Reflexive Double DoublePath where reflexive = Ref
public export Transitive Double DoublePath where transitive = Trn
public export Preorder Double DoublePath

export
doublePathRefl : {x,y : Double} -> DoublePath x y -> x === y
doublePathRefl {x,y} _ = believe_me (Refl {a=Double} {x=y})

export
reflToEq : {x,y : Double} -> (x === y) -> So (x == y)
reflToEq {y} Refl = believe_me (Oh)