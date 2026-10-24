module
public import RawPatchBridge
public section
namespace K230Verification
@[expose] def RawSquare.tileAt {R : Nat} (D : RawSquare R) (left bottom : Int)
    (p : Cell) : Quad FullColor := D.tile (p.1-left,p.2-bottom)

theorem RawSquare.tileAt_member {R : Nat} (D : RawSquare R) (left bottom x y : Int)
    (hx : left≤x) (hxR : x≤left+R) (hy : bottom≤y) (hyR : y≤bottom+R) :
    D.tileAt left bottom (x,y) ∈ exactFullPlaneTiles := by
  apply D.member <;> omega

theorem RawSquare.tileAt_horizontal {R : Nat} (D : RawSquare R) (left bottom x y : Int)
    (hx : left≤x) (hxR : x<left+R) (hy : bottom≤y) (hyR : y≤bottom+R) :
    (D.tileAt left bottom (x,y)).e=(D.tileAt left bottom (x+1,y)).w := by
  have h := D.horizontal (x-left) (y-bottom) (by omega) (by omega) (by omega) (by omega)
  simpa only [RawSquare.tileAt, show x+1-left=x-left+1 by omega] using h

theorem RawSquare.tileAt_vertical {R : Nat} (D : RawSquare R) (left bottom x y : Int)
    (hx : left≤x) (hxR : x≤left+R) (hy : bottom≤y) (hyR : y<bottom+R) :
    (D.tileAt left bottom (x,y)).n=(D.tileAt left bottom (x,y+1)).s := by
  have h := D.vertical (x-left) (y-bottom) (by omega) (by omega) (by omega) (by omega)
  simpa only [RawSquare.tileAt, show y+1-bottom=y-bottom+1 by omega] using h
end K230Verification
