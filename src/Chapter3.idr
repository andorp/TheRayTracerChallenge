module Chapter3

import Chapter1

import Data.So
import Data.Vect
import Data.Fin
import DoublePath

record Matrix row col where
  constructor MkMatrix
  elems : Vect row (Vect col Double)

Eq (Matrix row col) where
  MkMatrix e1 == MkMatrix e2 = all id $ zipWith (\r1 , r2 => all id $ zipWith eq r1 r2) e1 e2

Matrix2x2 : Type
Matrix2x2 = Matrix 2 2

Matrix3x3 : Type
Matrix3x3 = Matrix 3 3

Matrix4x4 : Type
Matrix4x4 = Matrix 4 4

public export
(*) : Matrix4x4 -> Matrix4x4 -> Matrix4x4
(*) (MkMatrix [ [ a00, a01, a02, a03 ]
              , [ a10, a11, a12, a13 ]
              , [ a20, a21, a22, a23 ]
              , [ a30, a31, a32, a33 ]
              ])
    (MkMatrix [ [ b00, b01, b02, b03 ]
              , [ b10, b11, b12, b13 ]
              , [ b20, b21, b22, b23 ]
              , [ b30, b31, b32, b33 ]
              ])
    = MkMatrix
        --             c0                             c1                             c2                              c3
        [ [a00*b00+a01*b10+a02*b20+a03*b30,a00*b01+a01*b11+a02*b21+a03*b31,a00*b02+a01*b12+a02*b22+a03*b32,a00*b03+a01*b13+a02*b23+a03*b33] -- r0
        , [a10*b00+a11*b10+a12*b20+a13*b30,a10*b01+a11*b11+a12*b21+a13*b31,a10*b02+a11*b12+a12*b22+a13*b32,a10*b03+a11*b13+a12*b23+a13*b33] -- r1
        , [a20*b00+a21*b10+a22*b20+a23*b30,a20*b01+a21*b11+a22*b21+a23*b31,a20*b02+a21*b12+a22*b22+a23*b32,a20*b03+a21*b13+a22*b23+a23*b33] -- r2
        , [a30*b00+a31*b10+a32*b20+a33*b30,a30*b01+a31*b11+a32*b21+a33*b31,a30*b02+a31*b12+a32*b22+a33*b32,a30*b03+a31*b13+a32*b23+a33*b33] -- r3
        ]

namespace TupleMult

  public export
  (*) : Matrix4x4 -> Tuple -> Tuple
  (*) (MkMatrix [ [ a00, a01, a02, a03 ]
                , [ a10, a11, a12, a13 ]
                , [ a20, a21, a22, a23 ]
                , [ a30, a31, a32, a33 ]
                ])
      (MkTuple t0 t1 t2 t3)
        = tuple
            (a00*t0+a01*t1+a02*t2+a03*t3)
            (a10*t0+a11*t1+a12*t2+a13*t3)
            (a20*t0+a21*t1+a22*t2+a23*t3)
            (a30*t0+a31*t1+a32*t2+a33*t3)

(.at) : (m : Matrix row col) -> (r : Fin row) -> (c : Fin col) -> Double
(.at) (MkMatrix elems) r c = index c (index r elems)

matrix : {row, col : Nat} -> Vect row (Vect col Double) -> Matrix row col
matrix = MkMatrix

matrix2x2 : Vect 2 (Vect 2 Double) -> Matrix2x2
matrix2x2 = MkMatrix

matrix3x3 : Vect 3 (Vect 3 Double) -> Matrix3x3
matrix3x3 = MkMatrix

matrix4x4 : Vect 4 (Vect 4 Double) -> Matrix4x4
matrix4x4 = MkMatrix

identity4 : Matrix4x4
identity4 = MkMatrix
  [ [1,0,0,0]
  , [0,1,0,0]
  , [0,0,1,0]
  , [0,0,0,1]
  ]

identity : (n : Nat) -> Matrix n n
identity 0     = MkMatrix []
identity 1     = MkMatrix [[1]]
identity (S k) = case (identity k) of
  MkMatrix elems => MkMatrix ((1 :: (replicate k 0)) :: map (0 ::) elems)

transpose : Matrix4x4 -> Matrix4x4
transpose (MkMatrix
            [ [ a00, a01, a02, a03 ]
            , [ a10, a11, a12, a13 ]
            , [ a20, a21, a22, a23 ]
            , [ a30, a31, a32, a33 ]
            ]) =
  MkMatrix
    [ [a00,a10,a20,a30]
    , [a01,a11,a21,a31]
    , [a02,a12,a22,a32]
    , [a03,a13,a23,a33]
    ]

mutual

  data AtLeast2 : Nat -> Type where
    YesAtLeast2 : {n : Nat} -> AtLeast2 (S (S n))

  zeroNotAtLeast2 : AtLeast2 0 -> Void
  zeroNotAtLeast2 _ impossible

  oneNotAtLeast2 : AtLeast2 1 -> Void
  oneNotAtLeast2 _ impossible

  determinant : (m : Nat) -> (ok : AtLeast2 m) => Matrix m m -> Double
  determinant Z     {ok} m = void (zeroNotAtLeast2 ok)
  determinant (S Z) {ok} m = void (oneNotAtLeast2 ok)
  determinant
    (S (S Z))
    (MkMatrix [ [a,b]
              , [c,d]
              ])
    = a*d - b*c
  determinant
    (S (S (S k))) m
    = sum $ map (\c => (m.at 0 c) * (cofactor _ m 0 c)) (Vect.Fin.range {len=(S (S (S k)))})

  submatrix : (n : Nat) -> Matrix (S n) (S n) -> Fin (S n) -> Fin (S n) -> Matrix n n
  submatrix n (MkMatrix elems) r c = MkMatrix (map (deleteAt c) (deleteAt r elems))

  minor : (n : Nat) -> (ok : AtLeast2 n) => Matrix (S n) (S n) -> Fin (S n) -> Fin (S n) -> Double
  minor n {ok} m r c = determinant n (submatrix n m r c)

  negateMinor : Fin n -> Fin n -> Double -> Double
  negateMinor r c m = if (finToInteger r + finToInteger c) `mod` 2 == 1 then (-m) else m

  cofactor : (n : Nat) -> (ok : AtLeast2 n) => Matrix (S n) (S n) -> Fin (S n) -> Fin (S n) -> Double
  cofactor n m r c = negateMinor r c (minor n m r c)

data Invertible : Matrix n n -> Type where
  YesInvertible :
    (AtLeast2 n)                =>
    (d : Double)                ->
    (o : d === determinant n m) =>
    (Not (d === 0.0))           ->
    ------------------------------
    Invertible m

invertible : (m : Matrix 4 4) -> Dec (Invertible m)
invertible m with (determinant 4 m) proof p1
  _ | d with (decSo (d == 0.0))
    _ | Yes isZero = No (\(YesInvertible x {o} notZero) => notZero (doublePathRefl (EqS (rewrite (trans o p1) in isZero))))
    _ | No notZero = Yes (YesInvertible d {o=sym p1} (\dReflZero => notZero (reflToEq dReflZero)))

inverse4 :
  (m : Matrix 4 4) ->
  (i : Invertible m) =>
  Matrix 4 4
inverse4 m {i=YesInvertible d notZero}
  = MkMatrix 
  $ Vect.Fin.tabulate
  $ \r => Vect.Fin.tabulate
    $ \c => (cofactor _ m c r) / d
      --    ^^^^^^^^^^^^^^^^^^ The original matrix is transposed

inverseTheorem :
  (m : Matrix 4 4) ->
  (i : Invertible m) ->
  Invertible (inverse4 m)
inverseTheorem = ?inversetheorem

-- * Algebra?

data MatrixPath : Matrix 4 4 -> Matrix 4 4 -> Type where
  Reflexivity   : MatrixPath a a
  Symmetry      : MatrixPath a b -> MatrixPath b a
  MultAssoc     : MatrixPath (a * (b * c)) ((a * b) * c)
  MultIdentity  : MatrixPath (a * identity _) (identity _ * a)
  Transpose     : MatrixPath (transpose (transpose a)) a
  Inverse1      : (i : Invertible m) -> MatrixPath (inverse4 (inverse4 m) {i=inverseTheorem m i}) m
  Inverse2      : Invertible m -> MatrixPath ((inverse4 m) * m) (identity 4)


-- * Examples

matrixExample1 :
  ( m === matrix4x4
            [ [ 1.0,  2.0,  3.0,  4.0]
            , [ 5.5,  6.5,  7.5,  8.5]
            , [ 9.0, 10.0, 11.0, 12.0]
            , [13.5, 14.5, 15.5, 16.5]
            ]) ->
  ( m.at 0 0 === 1.0
  , m.at 0 3 === 4.0
  , m.at 1 0 === 5.5
  , m.at 1 2 === 7.5
  , m.at 2 2 === 11.0
  , m.at 3 0 === 13.5
  , m.at 3 2 === 15.5
  )
matrixExample1 Refl =
  ( Refl
  , Refl
  , Refl
  , Refl
  , Refl
  , Refl
  , Refl
  )

matrixExample2 :
  ( m === matrix2x2
            [ [-3,5]
            , [1,-2]
            ]
  ) ->
  ( m.at 0 0 === -3
  , m.at 0 1 === 5
  , m.at 1 0 === 1
  , m.at 1 1 === -2
  )
matrixExample2 Refl =
  ( Refl
  , Refl
  , Refl
  , Refl
  )

matrixMultiplicationExample1 :
  (a === matrix4x4
            [ [1,2,3,4]
            , [5,6,7,8]
            , [9,8,7,6]
            , [5,4,3,2]
            ]) ->
  (b === matrix4x4
            [ [-2,1,2,3]
            , [3,2,1,-1]
            , [4,3,6,5]
            , [1,2,7,8]
            ]) ->
  (a * b === matrix4x4
              [ [20,22,50,48]
              , [44,54,114,108]
              , [40,58,110,102]
              , [16,26,46,42]
              ])
matrixMultiplicationExample1 Refl Refl = Refl

tupleMultExample :
  (a === matrix4x4
          [ [1,2,3,4]
          , [2,4,4,2]
          , [8,6,4,1]
          , [0,0,0,1]
          ]) ->
  (b === tuple 1 2 3 1) ->
  (a * b === tuple 18 24 33 1)
tupleMultExample Refl Refl = Refl

transposeExample1 :
  (a === matrix4x4
          [ [0,9,3,0]
          , [9,8,0,8]
          , [1,8,5,3]
          , [0,0,5,8]
          ]) ->
  (transpose a === matrix4x4
    [ [0,9,1,0]
    , [9,8,8,0]
    , [3,0,5,5]
    , [0,8,3,8]
    ])
transposeExample1 Refl = Refl

submatrixExample1 :
  (a === matrix3x3
          [ [1 , 5, 0]
          , [-3, 2, 7]
          , [0 , 6,-3]
          ]) ->
  (submatrix 2 a 0 2 === matrix2x2
          [ [-3, 2]
          , [ 0, 6]
          ])
submatrixExample1 Refl = Refl

submatrixExample2 : 
  (a === matrix4x4
          [ [-6, 1, 1, 6]
          , [-8, 5, 8, 6]
          , [-1, 0, 8, 2]
          , [-7, 1,-1, 1]
          ]) ->
  (submatrix 3 a 2 1 === matrix3x3
          [ [-6, 1, 6]
          , [-8, 8, 6]
          , [-7,-1, 1]
          ])
submatrixExample2 Refl = Refl

determinantExample1 :
  (a === matrix2x2
          [ [ 1,5]
          , [-3,2]
          ]) ->
  (determinant _ a === 17)
determinantExample1 Refl = Refl

minorExample1 :
  (a === matrix3x3
          [ [3, 5, 0]
          , [2,-1,-7]
          , [6,-1, 5]
          ]) ->
  (b === submatrix _ a 1 0) ->
  ( determinant _ b === 25
  , minor _ a 1 0 === 25
  )
minorExample1 Refl Refl = (Refl, Refl)

cofactorExample1 :
  (a === matrix3x3
          [ [3, 5, 0]
          , [2,-1,-7]
          , [6,-1, 5]
          ]) ->
  ( minor _ a 0 0 === -12
  , cofactor _ a 0 0 === -12
  , minor _ a 1 0 === 25
  , cofactor _ a 1 0 === -25
  )
cofactorExample1 Refl = (Refl, Refl, Refl, Refl)

determinantExample2 :
  (a === matrix3x3
          [ [ 1,2, 6]
          , [-5,8,-4]
          , [ 2,6, 4]
          ]) ->
  ( cofactor _ a 0 0 === 56
  , cofactor _ a 0 1 === 12
  , cofactor _ a 0 2 === -46
  , determinant _ a === -196
  )
determinantExample2 Refl = (Refl, Refl, Refl, Refl)

determinantExample3 :
  (a === matrix4x4
          [ [-2,-8, 3, 5]
          , [-3, 1, 7, 3]
          , [ 1, 2,-9, 6]
          , [-6, 7, 7,-9]
          ]) ->
  ( cofactor _ a 0 0 === 690
  , cofactor _ a 0 1 === 447
  , cofactor _ a 0 2 === 210
  , cofactor _ a 0 3 === 51
  , determinant _ a === -4071
  )
determinantExample3 Refl = (Refl, Refl, Refl, Refl, Refl)

invertiblePredicateExample1 :
  Invertible (matrix4x4
          [ [ 6, 4, 4, 4]
          , [ 5, 5, 7, 6]
          , [ 4,-9, 3,-7]
          , [ 9, 1, 7,-6]
          ])
invertiblePredicateExample1
  = YesInvertible
      (determinant 4 (matrix4x4
          [ [ 6, 4, 4, 4]
          , [ 5, 5, 7, 6]
          , [ 4,-9, 3,-7]
          , [ 9, 1, 7,-6]
          ]))
      (\x => case x of {})

invertiblePredicateExample2 :
  (a === matrix4x4
          [ [-4, 2,-2,-3]
          , [ 9, 6, 2, 6]
          , [ 0,-5, 1,-5]
          , [ 0, 0, 0,-0]
          ]) ->
  Not (Invertible a)
invertiblePredicateExample2 Refl (YesInvertible d {o} contra) = contra (rewrite o in Refl)

partial
inverseExample1 : Bool
inverseExample1 =
  let a = matrix4x4
          [ [-5, 2, 6,-8]
          , [ 1,-5, 1, 8]
          , [ 7, 7,-6,-7]
          , [ 1,-3, 7, 4]
          ] in
  let Yes i = invertible a in -- partial
  let b = inverse4 a in
  all id $ the (List Bool)
    [ True
    , determinant _ a  ==  532
    , cofactor _ a 2 3 == -160
    , b.at 3 2         == -160/532
    , cofactor _ a 3 2 ==  105
    , b.at 2 3         ==  105/532
    , b == matrix4x4
            [ [ 0.21805, 0.45113, 0.24060,-0.04511]
            , [-0.80827,-1.45677,-0.44361, 0.52068]
            , [-0.07895,-0.22368,-0.05263, 0.19737]
            , [-0.52256,-0.81391,-0.30075, 0.30639]
            ]
    ]

partial
inverseExample2 : Bool
inverseExample2 =
  let a = matrix4x4
            [ [ 3,-9, 7, 3]
            , [ 3,-8, 2,-9]
            , [-4, 4, 4, 1]
            , [-6, 5,-1, 1]
            ] in
  let b = matrix4x4
            [ [ 8, 2, 2, 2]
            , [ 3,-1, 7, 0]
            , [ 7, 0, 5, 4]
            , [ 6,-2, 0, 5]
            ] in
  let Yes i = invertible b in
  let c = a * b in
  c * (inverse4 b) == a
