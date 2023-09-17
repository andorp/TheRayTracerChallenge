module DRefl

import Data.So
import Control.Relation
import Control.Order

||| Relation on Double equality from theoretical point of view.
|||
||| Although we define this relation, but this is not true as operations
||| on Doubles are not safe. But from theoretical point of view these
||| associations should hold and the end result.
public export
data DRefl : Double -> Double -> Type where
  NegZ   : DRefl 0.0 (-0.0)
  EqR    : x === y     -> DRefl x y
  EqS    : So (x == y) -> DRefl x y
  Cng    : (f :  Double -> Double) -> DRefl x y -> DRefl (f x) (f y)
  Ref    : DRefl x x
  Sym    : DRefl x y -> DRefl y x
  Trn    : DRefl x y -> DRefl y z -> DRefl x z
  AddUnL : DRefl (0.0 + x) x
  AddUnR : DRefl (x + 0.0) x
  AddCom : DRefl (x + y) (y + x)
  AddAsc : DRefl ((x + y) + z) (x + (y + z))
  MulUnL : DRefl (1.0 * x) x
  MulUnR : DRefl (x * 1.0) x
  MulCom : DRefl (x * y) (y * x)
  MulAsc : DRefl ((x * y) * z) (x * (y * z))
  DivUni : DRefl (x / 1) x
  DivAdd : DRefl ((x / z) + (y / z)) ((x + y) / z)
  DivMul : DRefl ((x1 / z1) * (x2 / z2)) ((x1 * x2) / (z1 * z2))
  DivSam : DRefl (x / x) 1.0
  DivNum : DRefl x y -> DRefl (x / z) (y / z)
  DivDen : DRefl x y -> DRefl (z / x) (z / y)
  SqrMul : DRefl (sqrt x * sqrt x) x

public export Reflexive Double DRefl where reflexive = Ref
public export Transitive Double DRefl where transitive = Trn
public export Preorder Double DRefl

export
deq : {x,y : Double} -> DRefl x y -> x === y
deq {x,y} _ = believe_me (Refl {a=Double} {x=y})
