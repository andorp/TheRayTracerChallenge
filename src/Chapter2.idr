module Chapter2

import Data.So
import Data.Vect
import Data.List
import Decidable.Equality
import Syntax.PreorderReasoning
import Data.String

-- Color

record Color where
  constructor MkColor
  red, green, blue : Double

color : (red, green, blue : Double) -> Color
color r g b = MkColor { red = r , green = g , blue = b }

(+) : Color -> Color -> Color
(+) (MkColor r1 g1 b1) (MkColor r2 g2 b2) = color (r1+r2) (g1+g2) (b1+b2)

(-) : Color -> Color -> Color
(-) (MkColor r1 g1 b1) (MkColor r2 g2 b2) = color (r1-r2) (g1-g2) (b1-b2)

(*) : Color -> Double -> Color
(*) (MkColor r g b) s = color (r*s) (g*s) (b*s)

(/) : Color -> Double -> Color
(/) (MkColor r g b) s = color (r/s) (g/s) (b/s)

hadamard : Color -> Color -> Color
hadamard (MkColor r1 g1 b1) (MkColor r2 g2 b2) = color (r1*r2) (g1*g2) (b1*b2)

-- Canvas

|||
||| +--------- x/w ----------->
||| |
||| y/d       (x,y)
||| |
||| V
|||
data Point : Nat -> Nat -> Type where
  MkPoint : {w,d : Nat} -> (x : Fin w) -> (y : Fin d) -> Point w d

Eq (Point w h) where
  (MkPoint x1 y1) == (MkPoint x2 y2) = x1 == x2 && y1 == y2

point : {w,h : Nat} -> (x : Fin w) -> (y : Fin h) -> Point w h
point x y = MkPoint x y

Image : Nat -> Nat -> Type -> Type
Image w h p = Point w h -> p

Canvas : Nat -> Nat -> Type
Canvas w h = Image w h Color

width : {w,h : Nat} -> Canvas w h -> Nat
width {w} _ = w

height : {w,h : Nat} -> Canvas w h -> Nat
height {h} _ = h

canvas : (w,h : Nat) -> Canvas w h
canvas _ _ = const (color 0 0 0)

canvasOfColor : (w,h : Nat) -> Color -> Canvas w h
canvasOfColor _ _ c = const c

pixel : Point w h -> Color -> Canvas w h -> Canvas w h
pixel p c i q = if (p == q) then c else (i q)

writePixel : {w,h : Nat} -> (x : Fin w) -> (y : Fin h) -> Color -> Canvas w h -> Canvas w h
writePixel x y c v = pixel (point x y) c v

getPixel : Point w h -> Canvas w h -> Color
getPixel p i = i p

-- PPM

record PPM where
  constructor MkPPM
  width  : Nat
  height : Nat
  pixels : Vect height (Vect width (Bits8, Bits8, Bits8))

ppmLines : PPM -> List String
ppmLines (MkPPM w h p) =
  [ "P3"
  , "\{show w} \{show h}"
  , "255"
  ] ++ ppmContentLines p
  where
    ppmContentLines : Vect h (Vect w (Bits8, Bits8, Bits8)) -> List String
    ppmContentLines = renderLines . foldl (\state , line => foldl createLines (newLineState state) line) (0,[],[])
      where
        State : Type
        State = (Int, List String, List String)

        renderLine : List String -> String
        renderLine = unwords . reverse

        newLineState : State -> State
        newLineState (_,[],ds) = (0,[],ds)
        newLineState (_,cs,ds) = (0,[],renderLine cs :: ds)

        renderLines : State -> List String
        renderLines (_,cs,ds) = reverse (renderLine cs :: ds)

        -- Parameters in the state:
        -- - Length of the actual line with ' ' interspersed
        -- - The active elements reversed
        -- - The final lines reversed, but content in line is in right order
        addOneBits8 : Bits8 -> State -> State
        addOneBits8 b (l,ccs,ds) =
          let cs = show b in
          let cl = cast (length cs) in
          if (l+cl+1 <= 70)
            then (l+cl+1, cs :: ccs, ds)
            else (cl+1, [cs], renderLine ccs :: ds)

        createLines : State -> (Bits8,Bits8,Bits8) -> State
        createLines s (r,g,b) = addOneBits8 b $ addOneBits8 g $ addOneBits8 r s

range : (l1,l2 : Int) -> List String -> List String
range l1 l2 xs = take (cast (l2-l1+1)) $ drop (cast (l1-1)) xs

-- Conversions

canvasToPPM : {w,h : Nat} -> Canvas w h -> PPM
canvasToPPM {w,h} c =
  MkPPM
    { width    = w
    , height   = h
    , pixels
        = map (map (\p => colorToBits16 (getPixel p c)))
        $ Vect.Fin.tabulate {len=h}
        $ \y => Vect.Fin.tabulate {len=w}  
        $ \x => MkPoint x y
    }
  where
    doubleToBits8 : Double -> Bits8
    doubleToBits8 d =
      if d < 0.0 then 0
      else if d >= 1.0 then 255
      else cast (d * 256) -- Maybe another cast is needed for this.

    colorToBits16 : Color -> (Bits8, Bits8, Bits8)
    colorToBits16 (MkColor r g b) = (doubleToBits8 r,doubleToBits8 g,doubleToBits8 b)

-- * Proofs and examples

-- Addition is pairwise addition of colors.
addTheorem :
  (c1,c2 : Color) ->
  c1 + c2 === color (c1.red + c2.red) (c1.green + c2.green) (c1.blue + c2.blue)
addTheorem (MkColor r1 g1 b1) (MkColor r2 g2 b2) = Refl

-- Substraction is pairwise substraction of colors.
subTheorem :
  (c1,c2 : Color) ->
  c1 - c2 === color (c1.red - c2.red) (c1.green - c2.green) (c1.blue - c2.blue)
subTheorem (MkColor r1 g1 b1) (MkColor r2 g2 b2) = Refl

-- Multiplying by scalar is a pointwise multiplication by the scalar
multScalarTheorem :
  (c : Color) ->
  (s : Double) ->
  c * s === color (c.red * s) (c.green * s) (c.blue * s)
multScalarTheorem (MkColor r g b) s = Refl

-- Dividing by scalar is a pointwise division by the scalar
divScalarTheorem :
  (c : Color) ->
  (s : Double) ->
  c / s === color (c.red / s) (c.green / s) (c.blue / s)
divScalarTheorem (MkColor r g b) s = Refl

hadamardTheorem :
  (c1,c2 : Color) ->
  hadamard c1 c2 === color (c1.red * c2.red) (c1.green * c2.green) (c1.blue * c2.blue)
hadamardTheorem (MkColor r1 g1 b1) (MkColor r2 g2 b2) = Refl

-- Creating canvas
emptyCanvasTheorem :
  (w,h : Nat       ) ->
  (c   : Canvas w h) ->
  (p   : Point  w h) ->
  (c === canvas w h) ->
  ---------------------
  ( width  c === w
  , height c === h
  , getPixel p c === color 0 0 0
  )
emptyCanvasTheorem w h c p cp =
  ( Refl
  , Refl
  , rewrite cp in Refl
  )

-- writing to canvas
pixelTheorem :
  (w,h : Nat)                   ->
  (c   : Canvas w h)            ->
  (p   : Point w h)             ->
  (eq  : (p == p) === True)     -> -- This needs to be valid
  (k   : Color)                 ->
  (c === canvas w h)            ->
  --------------------------------
  (getPixel p (pixel p k c) === k)
pixelTheorem w h c p eq k cp = rewrite cp in rewrite eq in Refl

||| Constructing the PPM header
export
ppmHeaderExample : Bool
ppmHeaderExample =
  range 1 3 (ppmLines (canvasToPPM (canvas 5 3))) ==
  [ "P3"
  , "5 3"
  , "255"
  ]

||| Constructing the PPM pixel data
export
ppmPixelExample : Bool
ppmPixelExample =
  let v0 = canvas 5 3           in
  let c1 = color 1.5 0 0        in
  let c2 = color 0 0.5 0        in
  let c3 = color (-0.5) 0 1     in
  let v1 = writePixel 0 0 c1 v0 in
  let v2 = writePixel 2 1 c2 v1 in
  let v3 = writePixel 4 2 c3 v2 in
  (range 4 6 $ ppmLines $ canvasToPPM v3) ==
    [ "255 0 0 0 0 0 0 0 0 0 0 0 0 0 0"
    , "0 0 0 0 0 0 0 128 0 0 0 0 0 0 0"
    , "0 0 0 0 0 0 0 0 0 0 0 0 0 0 255"
    ]

||| Splitting long lines in the PPM files
export
ppmLongLines : Bool
ppmLongLines =
  let v0 = canvasOfColor 10 2 (color 1 0.8 0.6) in
  (range 4 7 $ ppmLines $ canvasToPPM v0) ==
    [ "255 204 153 255 204 153 255 204 153 255 204 153 255 204 153 255 204"
    , "153 255 204 153 255 204 153 255 204 153 255 204 153"
    , "255 204 153 255 204 153 255 204 153 255 204 153 255 204 153 255 204"
    , "153 255 204 153 255 204 153 255 204 153 255 204 153"
    ]
