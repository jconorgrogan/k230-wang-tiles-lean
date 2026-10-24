module
public import FilledChildEdges
public import OwnerPatchGlue
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace K230Verification
open K230Concrete

@[expose] noncomputable def filledPiece {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b)
    (i : Option RedSquare) (p : Cell) : Quad FullColor := by
  classical
  exact match i with
  | none => P.tile p
  | some b => if hb : LowerSquareInside (n+1) b then (children b hb).placed p else P.tile p

theorem filledPiece_none {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b) (p : Cell) :
    filledPiece P children none p=P.tile p := rfl

theorem filledPiece_some {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b)
    (b : RedSquare) (hb : LowerSquareInside (n+1) b) (p : Cell) :
    filledPiece P children (some b) p=(children b hb).placed p := by
  simp only [filledPiece,dif_pos hb]

@[expose] noncomputable def filledPatchData {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b) :
    OwnerPatchData RedSquare (4*squareSize n) := by
  classical
  exact {
    owner := rootOwner n
    piece := filledPiece P children
    member := by
      intro x y hx hxR hy hyR
      cases ho : rootOwner n (x,y) with
      | none =>
        rw [filledPiece_none]
        exact P.member x y hx hxR hy hyR ((childOwner_none_iff _ _).mp ho)
      | some b =>
        have hb := rootOwner_bounds ho
        rw [filledPiece_some P children b hb.1]
        exact (children b hb.1).patch.tileAt_member _ _ x y hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    horizontal_same := by
      intro x y hx hxR hy hyR he
      cases ho : rootOwner n (x,y) with
      | none =>
        simp only [filledPiece_none]
        exact P.horizontal x y hx hxR hy hyR
      | some b =>
        have ho' : rootOwner n (x+1,y)=some b := he.symm.trans ho
        have hb := rootOwner_bounds ho
        have hb' := rootOwner_bounds ho'
        simp only [filledPiece_some P children b hb.1]
        apply (children b hb.1).patch.tileAt_horizontal _ _ x y
        · exact hb.2.1
        · have := hb'.2.2.1; omega
        · exact hb.2.2.2.1
        · exact hb.2.2.2.2
    vertical_same := by
      intro x y hx hxR hy hyR he
      cases ho : rootOwner n (x,y) with
      | none =>
        simp only [filledPiece_none]
        exact P.vertical x y hx hxR hy hyR
      | some b =>
        have ho' : rootOwner n (x,y+1)=some b := he.symm.trans ho
        have hb := rootOwner_bounds ho
        have hb' := rootOwner_bounds ho'
        simp only [filledPiece_some P children b hb.1]
        apply (children b hb.1).patch.tileAt_vertical _ _ x y
        · exact hb.2.1
        · exact hb.2.2.1
        · exact hb.2.2.2.1
        · have := hb'.2.2.2.2; omega
    horizontal_seam := by
      intro x y hx hxR hy hyR he
      cases hp : rootOwner n (x,y) with
      | none =>
        cases hq : rootOwner n (x+1,y) with
        | none => exact False.elim (he (hp.trans hq.symm))
        | some b =>
          have hb := rootOwner_bounds hq
          rw [filledPiece_none,filledPiece_some P children b hb.1]
          have hside := rootOwner_left_seam hp hq
          have hmatch := (children b hb.1).placed_west hb.2 hside
          exact (P.horizontal x y hx hxR hy hyR).trans hmatch.symm
      | some a =>
        cases hq : rootOwner n (x+1,y) with
        | none =>
          have ha := rootOwner_bounds hp
          rw [filledPiece_some P children a ha.1,filledPiece_none]
          have hside := rootOwner_right_seam hp hq
          have hmatch := (children a ha.1).placed_east ha.2 hside
          exact hmatch.trans (P.horizontal x y hx hxR hy hyR)
        | some b =>
          have hab := rootOwner_neighbors hp hq (by simp) (by simp)
          subst b
          exact False.elim (he (hp.trans hq.symm))
    vertical_seam := by
      intro x y hx hxR hy hyR he
      cases hp : rootOwner n (x,y) with
      | none =>
        cases hq : rootOwner n (x,y+1) with
        | none => exact False.elim (he (hp.trans hq.symm))
        | some b =>
          have hb := rootOwner_bounds hq
          rw [filledPiece_none,filledPiece_some P children b hb.1]
          have hside := rootOwner_bottom_seam hp hq
          have hmatch := (children b hb.1).placed_south hb.2 hside
          exact (P.vertical x y hx hxR hy hyR).trans hmatch.symm
      | some a =>
        cases hq : rootOwner n (x,y+1) with
        | none =>
          have ha := rootOwner_bounds hp
          rw [filledPiece_some P children a ha.1,filledPiece_none]
          have hside := rootOwner_top_seam hp hq
          have hmatch := (children a ha.1).placed_north ha.2 hside
          exact hmatch.trans (P.vertical x y hx hxR hy hyR)
        | some b =>
          have hab := rootOwner_neighbors hp hq (by simp) (by simp)
          subst b
          exact False.elim (he (hp.trans hq.symm))
  }

@[expose] noncomputable def filledRawSquare {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b) :
    RawSquare (4*squareSize n) := (filledPatchData P children).toRawSquare

theorem filledRawSquare_tile {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b) (p : Cell) :
    (filledRawSquare P children).tile p=filledPiece P children (rootOwner n p) p := rfl

/-- Fill every maximal child independently. No compatibility is assumed
    between different scales beyond the explicit finite boundary contract. -/
@[expose] noncomputable def pasteCanonicalBoard {n v : Nat} {left bottom : Int → Bool}
    (P : ExposedBoard n v left bottom)
    (children : ∀ b : RedSquare, LowerSquareInside (n+1) b → FilledChild P b) :
    CanonicalBoard n v left bottom where
  patch := filledRawSquare P children
  base := by
    intro x y hx hy
    rw [filledRawSquare_tile]
    cases ho : rootOwner n ((x:Int),(y:Int)) with
    | none =>
      rw [filledPiece_none]
      exact P.base x y hx hy
    | some b =>
      have hb := rootOwner_bounds ho
      rw [filledPiece_some P children b hb.1]
      simpa using (children b hb.1).placed_base hb.2
  west := by
    intro j hj
    rw [filledRawSquare_tile,rootOwner_boundary (Or.inl rfl),filledPiece_none]
    exact P.west j hj
  east := by
    intro j hj
    rw [filledRawSquare_tile,rootOwner_boundary (Or.inr (Or.inl rfl)),filledPiece_none]
    exact P.east j hj
  south := by
    intro j hj
    rw [filledRawSquare_tile,rootOwner_boundary (Or.inr (Or.inr (Or.inl rfl))),filledPiece_none]
    exact P.south j hj
  north := by
    intro j hj
    rw [filledRawSquare_tile,rootOwner_boundary (Or.inr (Or.inr (Or.inr rfl))),filledPiece_none]
    exact P.north j hj

end K230Verification
#print axioms K230Verification.pasteCanonicalBoard
