module
public import ChildPatchContract
public import EntryIndices
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace K230Verification
open K230Concrete

@[expose] def RawSquare.resize {R S : Nat} (D : RawSquare R) (h : R=S) : RawSquare S where
  tile := D.tile
  member := by subst S; exact D.member
  horizontal := by subst S; exact D.horizontal
  vertical := by subst S; exact D.vertical

theorem incomingOuterDigit_decode (d : Int → Nat) (t : Int)
    (h : if t%4=1 then d t=2 ∨ d t=3 else d t=0) :
    incomingOuterDigit (fun u => decide (d u=3)) t=d t := by
  by_cases ht : t%4=1
  · simp only [ht, ite_true] at h
    rcases h with h | h <;> simp [incomingOuterDigit,ht,h]
  · simp only [ht,ite_false] at h
    simp [incomingOuterDigit,ht,h]

@[expose] def childWestDigit {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) (b : RedSquare) (t : Int) : Nat :=
  (P.tile (lowerOriginX n b,(lowerOriginY n b:Int)+t+boardHalf b.level)).w.2.1
@[expose] def childSouthDigit {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) (b : RedSquare) (t : Int) : Nat :=
  (P.tile ((lowerOriginX n b:Int)+t+boardHalf b.level,lowerOriginY n b)).s.2.1
@[expose] def childLeftChoice {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) (b : RedSquare) (t : Int) : Bool := decide (childWestDigit P b t=3)
@[expose] def childBottomChoice {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) (b : RedSquare) (t : Int) : Bool := decide (childSouthDigit P b t=3)

theorem childWestDigit_at {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) (b : RedSquare) (j : Nat) :
    childWestDigit P b ((j:Int)-boardHalf b.level)=
      (P.tile (lowerOriginX n b,lowerOriginY n b+j)).w.2.1 := by
  unfold childWestDigit
  have h : (lowerOriginY n b:Int)+((j:Int)-boardHalf b.level)+boardHalf b.level=(lowerOriginY n b:Int)+j := by omega
  rw [h]

theorem childSouthDigit_at {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) (b : RedSquare) (j : Nat) :
    childSouthDigit P b ((j:Int)-boardHalf b.level)=
      (P.tile (lowerOriginX n b+j,lowerOriginY n b)).s.2.1 := by
  unfold childSouthDigit
  have h : (lowerOriginX n b:Int)+((j:Int)-boardHalf b.level)+boardHalf b.level=(lowerOriginX n b:Int)+j := by omega
  rw [h]

theorem lower_cell_bounds {n : Nat} {b : RedSquare} (hb : LowerSquareInside (n+1) b)
    {x y : Nat} (hx : x≤2*boardHalf b.level) (hy : y≤2*boardHalf b.level) :
    lowerOriginX n b+x≤4*squareSize n ∧ lowerOriginY n b+y≤4*squareSize n := by
  have h := lower_origins n b hb
  have hsize := boardHalf_index n
  omega

theorem lower_cell_covered {n : Nat} {b : RedSquare} (hb : LowerSquareInside (n+1) b)
    {x y : Nat} (hx : x≤2*boardHalf b.level) (hy : y≤2*boardHalf b.level) :
    RootCovered (n+1) (((lowerOriginX n b+x:Nat):Int)-2*squareSize n,
      ((lowerOriginY n b+y:Nat):Int)-2*squareSize n) := by
  apply in_lower_rootCovered hb
  have h := lower_origins n b hb
  have hsize := boardHalf_index n
  dsimp [InRedSquare,ClosedInterval]
  constructor <;> constructor <;> omega

theorem lower_cell_blank {n v : Nat} {l d : Int → Bool}
    (P : ExposedBoard n v l d) {b : RedSquare} (hb : LowerSquareInside (n+1) b)
    {x y : Nat} (hx : x≤2*boardHalf b.level) (hy : y≤2*boardHalf b.level) :
    fullTM (P.tile (lowerOriginX n b+x,lowerOriginY n b+y))=tmBlank := by
  have h := lower_cell_bounds hb hx hy
  exact P.covered_blank _ _ h.1 h.2 (lower_cell_covered hb hx hy)

theorem filledChild_of_smaller_boards {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom) (hv : v<4) (b : RedSquare)
    (hb : LowerSquareInside (n+1) b)
    (small : ∀ w : Nat, w<4 → ∀ l d : Int → Bool,
      Nonempty (CanonicalBoard (b.level-1) w l d)) : Nonempty (FilledChild P b) := by
  obtain ⟨w,hw,crop⟩ := geometric_subboard_crop n v b hv hb
  obtain ⟨D⟩ := small w hw (childLeftChoice P b) (childBottomChoice P b)
  have hs := lower_side_length b
  have hh : 2*squareSize (b.level-1)=boardHalf b.level := by omega
  have hhi : 2*(squareSize (b.level-1):Int)=(boardHalf b.level:Int) := by omega
  have hsi : 4*(squareSize (b.level-1):Int)=2*(boardHalf b.level:Int) := by omega
  have hbase : ∀ x y : Nat, x≤2*boardHalf b.level → y≤2*boardHalf b.level →
      fullBase (D.patch.tile (x,y))=
        fullBase (P.tile (lowerOriginX n b+x,lowerOriginY n b+y)) := by
    intro x y hx hy
    have hbounds := lower_cell_bounds hb hx hy
    exact (D.base x y (by omega) (by omega)).trans
      ((congrArg baseTileQuad (crop x y hx hy).symm).trans
        (P.base _ _ hbounds.1 hbounds.2).symm)
  refine ⟨{ patch := D.patch.resize hs, base := ?_, west := ?_, east := ?_, south := ?_, north := ?_ }⟩
  · intro x y hx hy
    exact (D.base x y (by omega) (by omega)).trans
      (congrArg baseTileQuad (crop x y hx hy).symm)
  · intro j hj
    have hd := D.west j (by omega)
    rw [hhi] at hd
    have hc : incomingOuterDigit (childLeftChoice P b) ((j:Int)-boardHalf b.level)=
        (P.tile (lowerOriginX n b,lowerOriginY n b+j)).w.2.1 := by
      change incomingOuterDigit (fun u => decide (childWestDigit P b u=3)) _ = _
      have h := incomingOuterDigit_decode (childWestDigit P b) ((j:Int)-boardHalf b.level)
      have hp := P.lower_west b hb j hj
      rw [← childWestDigit_at P b j] at hp
      simpa only [childLeftChoice,childWestDigit_at] using h hp
    have hbas := congrArg Quad.w (hbase 0 j (by omega) hj)
    have ht := congrArg Quad.w (lower_cell_blank P hb (x:=0) (y:=j) (by omega) hj)
    simp only [Int.natCast_zero,Int.add_zero] at hbas ht
    exact Prod.ext hbas (Prod.ext (hd.1.trans hc) (hd.2.trans ht.symm))
  · intro j hj
    have hd := D.east j (by omega)
    rw [hsi,hhi] at hd
    have hbas := congrArg Quad.e (hbase (2*boardHalf b.level) j (by omega) hj)
    have ht := congrArg Quad.e (lower_cell_blank P hb (x:=2*boardHalf b.level) (y:=j) (by omega) hj)
    exact Prod.ext hbas (Prod.ext (hd.1.trans (P.lower_east b hb j hj).symm) (hd.2.trans ht.symm))
  · intro j hj
    have hd := D.south j (by omega)
    rw [hhi] at hd
    have hc : incomingOuterDigit (childBottomChoice P b) ((j:Int)-boardHalf b.level)=
        (P.tile (lowerOriginX n b+j,lowerOriginY n b)).s.2.1 := by
      change incomingOuterDigit (fun u => decide (childSouthDigit P b u=3)) _ = _
      have h := incomingOuterDigit_decode (childSouthDigit P b) ((j:Int)-boardHalf b.level)
      have hp := P.lower_south b hb j hj
      rw [← childSouthDigit_at P b j] at hp
      simpa only [childBottomChoice,childSouthDigit_at] using h hp
    have hbas := congrArg Quad.s (hbase j 0 hj (by omega))
    have ht := congrArg Quad.s (lower_cell_blank P hb (x:=j) (y:=0) hj (by omega))
    simp only [Int.natCast_zero,Int.add_zero] at hbas ht
    exact Prod.ext hbas (Prod.ext (hd.1.trans hc) (hd.2.trans ht.symm))
  · intro j hj
    have hd := D.north j (by omega)
    rw [hsi,hhi] at hd
    have hbas := congrArg Quad.n (hbase j (2*boardHalf b.level) hj (by omega))
    have ht := congrArg Quad.n (lower_cell_blank P hb (x:=j) (y:=2*boardHalf b.level) hj (by omega))
    exact Prod.ext hbas (Prod.ext (hd.1.trans (P.lower_north b hb j hj).symm) (hd.2.trans ht.symm))
theorem filledChild_of_induction {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom) (hv : v<4) (b : RedSquare)
    (hb : LowerSquareInside (n+1) b)
    (ih : ∀ m : Nat, m<n → ∀ w : Nat, w<4 → ∀ l d : Int → Bool,
      Nonempty (CanonicalBoard m w l d)) : Nonempty (FilledChild P b) := by
  apply filledChild_of_smaller_boards P hv b hb
  exact ih (b.level-1) (by have := hb.1; have := b.level_pos; omega)
end K230Verification
