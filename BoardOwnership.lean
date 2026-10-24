module
public import BoardEntrances
public section
set_option maxHeartbeats 0
namespace K230Verification

/-- Exposed cells and ring cells belong to the smallest closed red square
    containing them. No cross-size decoration agreement is built in. -/
@[expose] def Owns (b : RedSquare) (p : Int × Int) : Prop :=
  InRedSquare b p ∧ ∀ a : RedSquare, InRedSquare a p → b.level≤a.level

theorem nat_minimal_witness (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n≤m := by
  classical
  obtain ⟨n,hn⟩ := h
  suffices ∀ n, P n → ∃ k, P k ∧ ∀ m, P m → k≤m from this n hn
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases he : ∃ m, m<n ∧ P m
    · obtain ⟨m,hm,hpm⟩ := he
      exact ih m hm hpm
    · refine ⟨n,hn,?_⟩
      intro m hpm
      by_cases hmn : m<n
      · exact False.elim (he ⟨m,hmn,hpm⟩)
      · omega

/-- Every point covered by a lower board has a smallest actual geometric
    owner strictly inside the enclosing board. -/
theorem covered_has_owner {n : Nat} {r s : Int}
    (hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int))
    (hc : BoardCovered n r s) :
    ∃ b : RedSquare, LowerSquareInside n b ∧ Owns b (r,s) := by
  obtain ⟨b,hb,hp⟩ := (boardCovered_iff_lower_square hr).mp hc
  have hex : ∃ m : Nat, ∃ a : RedSquare, a.level=m ∧ InRedSquare a (r,s) :=
    ⟨b.level,b,rfl,hp⟩
  obtain ⟨m,⟨a,ham,hap⟩,hmin⟩ := nat_minimal_witness _ hex
  have hab : a.level≤b.level := by simpa [ham] using hmin b.level ⟨b,rfl,hp⟩
  have hlo : a.level<n := by have := hb.1; omega
  have hbandx := (red_band_iff_closed_interval
    (show (0:Int)<boardHalf a.level by have := board_half_pos a.level; omega)).mpr
    ⟨a.cx,a.centered_x,hap.1⟩
  have hbandy := (red_band_iff_closed_interval
    (show (0:Int)<boardHalf a.level by have := board_half_pos a.level; omega)).mpr
    ⟨a.cy,a.centered_y,hap.2⟩
  have hcov : BoardCovered n r s := ⟨hc.1,hc.2.1,a.level,a.level_pos,hlo,hbandx,hbandy⟩
  have hd := lower_period_dvd_half a.level_pos hlo
  have hL : (-(boardHalf n:Int))%(4*boardHalf a.level)=0 :=
    Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hd)
  have hR : (boardHalf n:Int)%(4*boardHalf a.level)=0 := Int.emod_eq_zero_of_dvd hd
  have hp0 : (0:Int)<boardHalf a.level := by have := board_half_pos a.level; omega
  have hix := interval_strictly_inside hp0 a.centered_x hL hR hap.1
    ⟨Int.le_of_lt hr.1,Int.le_of_lt hr.2⟩
  have hiy := interval_strictly_inside hp0 a.centered_y hL hR hap.2
    ⟨Int.le_of_lt hc.1,Int.le_of_lt hc.2.1⟩
  refine ⟨a,⟨hlo,hix.1,hix.2,hiy.1,hiy.2⟩,hap,?_⟩
  intro c hcp
  simpa [ham] using hmin c.level ⟨c,rfl,hcp⟩

/-- Owners are unique in their scale and center. Proof fields of RedSquare
    are intentionally irrelevant to this geometric uniqueness statement. -/
theorem owner_unique {a b : RedSquare} {p : Int × Int} (ha : Owns a p) (hb : Owns b p) :
    a.level=b.level ∧ a.cx=b.cx ∧ a.cy=b.cy := by
  have hl : a.level=b.level := Nat.le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  exact ⟨hl,same_level_square_centers hl ha.1 hb.1⟩

/-- No strictly smaller red square can cover a cell assigned to its owner. -/
theorem owner_exposed {b : RedSquare} {p : Int × Int} (hb : Owns b p)
    {a : RedSquare} (ha : a.level<b.level) : ¬InRedSquare a p := by
  intro hp
  have := hb.2 a hp
  omega


theorem centered_add_period {h c a : Int} (hc : CenteredAt h c) (ha : (4*h)∣a) :
    CenteredAt h (c+a) := by
  unfold CenteredAt at *
  rw [Int.add_emod,hc,Int.emod_eq_zero_of_dvd ha]
  simp only [Int.add_zero]
  simpa only [hc] using Int.emod_emod c (4*h)

/-- Ownership gives exactly the exposed-region hypothesis needed in the
    owner's own centered coordinates. -/
theorem owner_exposed_coordinates {b : RedSquare} {r s : Int} (hb : Owns b (r,s)) :
    ¬BoardCovered b.level (r-b.cx) (s-b.cy) := by
  intro hc
  obtain ⟨_,_,m,hm,hmb,hx,hy⟩ := hc
  have hp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
  obtain ⟨cx,hcx,hix⟩ := (red_band_iff_closed_interval hp).mp hx
  obtain ⟨cy,hcy,hiy⟩ := (red_band_iff_closed_interval hp).mp hy
  have hd := lower_period_dvd_half hm hmb
  have hdx : (4*(boardHalf m:Int))∣b.cx := Int.dvd_trans hd (center_multiple_half b.centered_x)
  have hdy : (4*(boardHalf m:Int))∣b.cy := Int.dvd_trans hd (center_multiple_half b.centered_y)
  let a : RedSquare := ⟨m,cx+b.cx,cy+b.cy,hm,centered_add_period hcx hdx,centered_add_period hcy hdy⟩
  have ha : InRedSquare a (r,s) := by
    dsimp [InRedSquare,ClosedInterval,a] at *
    omega
  have hle := hb.2 a ha
  change b.level≤m at hle
  omega


/-- A red ring belongs to that board itself, never to a smaller board. -/
theorem ring_owned {b : RedSquare} {r s : Int} (hb : InRedSquare b (r,s))
    (hring : r=b.cx-boardHalf b.level ∨ r=b.cx+boardHalf b.level ∨
      s=b.cy-boardHalf b.level ∨ s=b.cy+boardHalf b.level) : Owns b (r,s) := by
  refine ⟨hb,?_⟩
  intro a ha
  by_cases hl : b.level≤a.level
  · exact hl
  · have hn := red_squares_strictly_nested (show a.level<b.level by omega) ha hb
    have hx1 := ha.1.1
    have hx2 := ha.1.2
    have hy1 := ha.2.1
    have hy2 := ha.2.2
    unfold StrictlyInside at hn
    rcases hring with h|h|h|h <;> omega

end K230Verification
#print axioms K230Verification.covered_has_owner
#print axioms K230Verification.owner_unique
