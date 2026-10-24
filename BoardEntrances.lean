module
public import RedBoardGeometry
public section
set_option maxHeartbeats 0
namespace K230Verification

theorem lower_square_covered {n : Nat} {b : RedSquare} {r s : Int}
    (hb : LowerSquareInside n b) (hp : InRedSquare b (r,s)) : BoardCovered n r s := by
  have hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int) := by
    have h1 := hb.2.1
    have h2 := hb.2.2.1
    have h3 := hp.1.1
    have h4 := hp.1.2
    omega
  exact (boardCovered_iff_lower_square hr).mpr ⟨b,hb,hp⟩

/-- A transition from the parent's exposed region into a lower board is
    exactly a bottom side, not an assumed endpoint convention. -/
theorem covered_vertical_entry {n : Nat} {r s : Int}
    (hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int))
    (hc : BoardCovered n r s) (hn : ¬BoardCovered n r (s-1)) :
    ∃ b : RedSquare, LowerSquareInside n b ∧ InRedSquare b (r,s) ∧ s=b.cy-boardHalf b.level := by
  obtain ⟨b,hb,hp⟩ := (boardCovered_iff_lower_square hr).mp hc
  refine ⟨b,hb,hp,?_⟩
  have he := hp.2.1
  apply Classical.byContradiction
  intro hne
  have hprev : InRedSquare b (r,s-1) := by
    refine ⟨hp.1,?_,?_⟩
    · omega
    · have := hp.2.2; omega
  exact hn (lower_square_covered hb hprev)

theorem covered_vertical_exit {n : Nat} {r s : Int}
    (hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int))
    (hc : BoardCovered n r s) (hn : ¬BoardCovered n r (s+1)) :
    ∃ b : RedSquare, LowerSquareInside n b ∧ InRedSquare b (r,s) ∧ s=b.cy+boardHalf b.level := by
  obtain ⟨b,hb,hp⟩ := (boardCovered_iff_lower_square hr).mp hc
  refine ⟨b,hb,hp,?_⟩
  have he := hp.2.2
  apply Classical.byContradiction
  intro hne
  have hnext : InRedSquare b (r,s+1) := by
    refine ⟨hp.1,?_,?_⟩
    · have := hp.2.1; omega
    · omega
  exact hn (lower_square_covered hb hnext)

theorem covered_horizontal_entry {n : Nat} {r s : Int}
    (hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int))
    (hc : BoardCovered n r s) (hn : ¬BoardCovered n (r-1) s) :
    ∃ b : RedSquare, LowerSquareInside n b ∧ InRedSquare b (r,s) ∧ r=b.cx-boardHalf b.level := by
  obtain ⟨b,hb,hp⟩ := (boardCovered_iff_lower_square hr).mp hc
  refine ⟨b,hb,hp,?_⟩
  have he := hp.1.1
  apply Classical.byContradiction
  intro hne
  have hprev : InRedSquare b (r-1,s) := by
    refine ⟨⟨?_,?_⟩,hp.2⟩
    · omega
    · have := hp.1.2; omega
  exact hn (lower_square_covered hb hprev)

theorem covered_horizontal_exit {n : Nat} {r s : Int}
    (hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int))
    (hc : BoardCovered n r s) (hn : ¬BoardCovered n (r+1) s) :
    ∃ b : RedSquare, LowerSquareInside n b ∧ InRedSquare b (r,s) ∧ r=b.cx+boardHalf b.level := by
  obtain ⟨b,hb,hp⟩ := (boardCovered_iff_lower_square hr).mp hc
  refine ⟨b,hb,hp,?_⟩
  have he := hp.1.2
  apply Classical.byContradiction
  intro hne
  have hnext : InRedSquare b (r+1,s) := by
    refine ⟨⟨?_,?_⟩,hp.2⟩
    · have := hp.1.1; omega
    · omega
  exact hn (lower_square_covered hb hnext)

end K230Verification
