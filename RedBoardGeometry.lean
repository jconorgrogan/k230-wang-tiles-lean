module
public import BoardChannels
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

/-- A center of a canonical red interval of half-width h. -/
@[expose] def CenteredAt (h c : Int) : Prop := c % (4*h) = 2*h
@[expose] def ClosedInterval (h c x : Int) : Prop := c-h ≤ x ∧ x ≤ c+h

/-- A small-board center stays two small half-widths away from every
    boundary aligned at its period. This prevents same-color ring crossings. -/
theorem center_boundary_gap {h c b : Int} (hh : 0<h)
    (hc : CenteredAt h c) (hb : b % (4*h)=0) :
    c ≤ b-2*h ∨ b+2*h ≤ c := by
  have hrem : (c-b) % (4*h)=2*h := by
    rw [Int.sub_emod, hc, hb]
    simp only [Int.sub_zero]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have he := Int.mul_ediv_add_emod (c-b) (4*h)
  rw [hrem] at he
  by_cases hq : (c-b)/(4*h) < 0
  · have hb' := Int.mul_le_mul_of_nonneg_left (show (c-b)/(4*h) ≤ -1 by omega) (show 0 ≤ 4*h by omega)
    simp only [Int.mul_neg, Int.mul_one] at hb'
    exact Or.inl (by omega)
  · have hb' := Int.mul_nonneg (show 0 ≤ 4*h by omega) (show 0 ≤ (c-b)/(4*h) by omega)
    exact Or.inr (by omega)

/-- Once a small interval intersects an interval with coarser aligned
    boundaries, it lies strictly inside those boundaries. -/
theorem interval_strictly_inside {h c L R x : Int} (hh : 0<h)
    (hc : CenteredAt h c) (hL : L % (4*h)=0) (hR : R % (4*h)=0)
    (hx : ClosedInterval h c x) (houter : L ≤ x ∧ x ≤ R) :
    L < c-h ∧ c+h < R := by
  have hl := center_boundary_gap hh hc hL
  have hr := center_boundary_gap hh hc hR
  unfold ClosedInterval at hx
  constructor
  · rcases hl with hl|hl <;> omega
  · rcases hr with hr|hr <;> omega

/-- Distinct canonical intervals at the same level cannot even touch. -/
theorem same_level_centers_equal {h a b x : Int} (hh : 0<h)
    (ha : CenteredAt h a) (hb : CenteredAt h b)
    (hxa : ClosedInterval h a x) (hxb : ClosedInterval h b x) : a=b := by
  have hrem : (a-b)%(4*h)=0 := by rw [Int.sub_emod,ha,hb]; simp
  have he := Int.mul_ediv_add_emod (a-b) (4*h)
  rw [hrem] at he
  unfold ClosedInterval at hxa hxb
  by_cases hp : 0 < (a-b)/(4*h)
  · have hmul := Int.mul_le_mul_of_nonneg_left (show 1 ≤ (a-b)/(4*h) by omega) (show 0 ≤ 4*h by omega)
    simp only [Int.mul_one] at hmul
    omega
  by_cases hn : (a-b)/(4*h) < 0
  · have hmul := Int.mul_le_mul_of_nonneg_left (show (a-b)/(4*h) ≤ -1 by omega) (show 0 ≤ 4*h by omega)
    simp only [Int.mul_neg,Int.mul_one] at hmul
    omega
  · have hz : (a-b)/(4*h)=0 := by omega
    simp [hz] at he
    omega

theorem board_half_factor {m n : Nat} (hm : 1≤m) (hmn : m<n) :
    boardHalf n = 4*boardHalf m*4^(n-m-1) := by
  have he : n-1 = (m-1)+1+(n-m-1) := by omega
  unfold boardHalf
  rw [he, Nat.pow_add, Nat.pow_add]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem lower_period_dvd_half {m n : Nat} (hm : 1≤m) (hmn : m<n) :
    (4*(boardHalf m : Int)) ∣ (boardHalf n : Int) := by
  refine ⟨(4^(n-m-1) : Nat), ?_⟩
  have he := board_half_factor hm hmn
  exact_mod_cast he

theorem center_multiple_half {h c : Int} (hc : CenteredAt h c) : h ∣ c := by
  have he := Int.mul_ediv_add_emod c (4*h)
  rw [hc] at he
  refine ⟨4*(c/(4*h))+2, ?_⟩
  calc
    c = 4*h*(c/(4*h))+2*h := he.symm
    _ = h*(4*(c/(4*h))+2) := by
      simp [Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]

theorem coarse_boundaries_aligned {h H c : Int}
    (hdiv : (4*h) ∣ H) (hc : CenteredAt H c) :
    (c-H)%(4*h)=0 ∧ (c+H)%(4*h)=0 := by
  have hcenter : (4*h) ∣ c := Int.dvd_trans hdiv (center_multiple_half hc)
  exact ⟨Int.emod_eq_zero_of_dvd (Int.dvd_sub hcenter hdiv),
    Int.emod_eq_zero_of_dvd (Int.dvd_add hcenter hdiv)⟩

structure RedSquare where
  level : Nat
  cx : Int
  cy : Int
  level_pos : 1≤level
  centered_x : CenteredAt (boardHalf level) cx
  centered_y : CenteredAt (boardHalf level) cy

@[expose] def InRedSquare (b : RedSquare) (p : Int × Int) : Prop :=
  ClosedInterval (boardHalf b.level) b.cx p.1 ∧ ClosedInterval (boardHalf b.level) b.cy p.2
@[expose] def StrictlyInside (a b : RedSquare) : Prop :=
  b.cx-(boardHalf b.level : Int) < a.cx-boardHalf a.level ∧
  a.cx+boardHalf a.level < b.cx+boardHalf b.level ∧
  b.cy-(boardHalf b.level : Int) < a.cy-boardHalf a.level ∧
  a.cy+boardHalf a.level < b.cy+boardHalf b.level

/-- Exact canonical red squares of different scales are disjoint or strictly
    nested. In particular their rings cannot cross or share a cell. -/
theorem red_squares_strictly_nested {a b : RedSquare} {p : Int × Int}
    (hab : a.level < b.level) (ha : InRedSquare a p) (hb : InRedSquare b p) :
    StrictlyInside a b := by
  have hpos : (0 : Int) < boardHalf a.level := by exact_mod_cast board_half_pos a.level
  have hd := lower_period_dvd_half a.level_pos hab
  have hbx := coarse_boundaries_aligned hd b.centered_x
  have hby := coarse_boundaries_aligned hd b.centered_y
  have hx := interval_strictly_inside hpos a.centered_x hbx.1 hbx.2 ha.1 hb.1
  have hy := interval_strictly_inside hpos a.centered_y hby.1 hby.2 ha.2 hb.2
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem same_level_square_centers {a b : RedSquare} {p : Int × Int}
    (hab : a.level=b.level) (ha : InRedSquare a p) (hb : InRedSquare b p) :
    a.cx=b.cx ∧ a.cy=b.cy := by
  have hpos : (0 : Int) < boardHalf a.level := by exact_mod_cast board_half_pos a.level
  have hbx : CenteredAt (boardHalf a.level) b.cx := hab ▸ b.centered_x
  have hby : CenteredAt (boardHalf a.level) b.cy := hab ▸ b.centered_y
  have hix : ClosedInterval (boardHalf a.level) b.cx p.1 := hab ▸ hb.1
  have hiy : ClosedInterval (boardHalf a.level) b.cy p.2 := hab ▸ hb.2
  exact ⟨same_level_centers_equal hpos a.centered_x hbx ha.1 hix,
    same_level_centers_equal hpos a.centered_y hby ha.2 hiy⟩

/-- The modular obstruction band is exactly the union of closed canonical
    intervals, not an approximation to their geometry. -/
theorem red_band_iff_closed_interval {h t : Int} (hh : 0<h) :
    RedBand h t ↔ ∃ c, CenteredAt h c ∧ ClosedInterval h c t := by
  have h2 : (2*h)%(4*h)=2*h := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · intro hb
    let c := 4*h*(t/(4*h))+2*h
    refine ⟨c, ?_, ?_⟩
    · simp [CenteredAt,c,Int.add_emod,h2]
    · have he := Int.mul_ediv_add_emod t (4*h)
      unfold RedBand at hb
      dsimp [ClosedInterval,c]
      omega
  · rintro ⟨c,hc,hct⟩
    have hrange : 0 ≤ 2*h+(t-c) ∧ 2*h+(t-c)<4*h := by
      unfold ClosedInterval at hct
      omega
    have he : t%(4*h)=2*h+(t-c) := by
      calc
        t%(4*h) = (c+(t-c))%(4*h) := by congr 1; omega
        _ = (2*h+(t-c))%(4*h) := by
          exact Int.add_emod_eq_add_emod_right (t-c) (hc.trans h2.symm)
        _ = 2*h+(t-c) := Int.emod_eq_of_lt hrange.1 hrange.2
    unfold RedBand
    rw [he]
    unfold ClosedInterval at hct
    omega

/-- An actual smaller closed square strictly inside a board centered at
    relative coordinate zero. -/
@[expose] def LowerSquareInside (n : Nat) (b : RedSquare) : Prop :=
  b.level < n ∧
  -(boardHalf n : Int) < b.cx-boardHalf b.level ∧
  b.cx+boardHalf b.level < boardHalf n ∧
  -(boardHalf n : Int) < b.cy-boardHalf b.level ∧
  b.cy+boardHalf b.level < boardHalf n

/-- The exact BoardCovered predicate used by the channel proofs equals
    membership in the union of all strictly interior smaller red squares. -/
theorem boardCovered_iff_lower_square {n : Nat} {r s : Int}
    (hr : -(boardHalf n : Int)<r ∧ r<boardHalf n) :
    BoardCovered n r s ↔ ∃ b : RedSquare, LowerSquareInside n b ∧ InRedSquare b (r,s) := by
  constructor
  · rintro ⟨hslo,hshi,m,hm,hmn,hbr,hbs⟩
    have hp : (0 : Int)<boardHalf m := by exact_mod_cast board_half_pos m
    obtain ⟨cx,hcx,hix⟩ := (red_band_iff_closed_interval hp).mp hbr
    obtain ⟨cy,hcy,hiy⟩ := (red_band_iff_closed_interval hp).mp hbs
    let b : RedSquare := ⟨m,cx,cy,hm,hcx,hcy⟩
    have hd := lower_period_dvd_half hm hmn
    have hR : (boardHalf n : Int)%(4*boardHalf m)=0 := Int.emod_eq_zero_of_dvd hd
    have hL : (-(boardHalf n : Int))%(4*boardHalf m)=0 := Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hd)
    have hx := interval_strictly_inside hp hcx hL hR hix ⟨Int.le_of_lt hr.1,Int.le_of_lt hr.2⟩
    have hy := interval_strictly_inside hp hcy hL hR hiy ⟨Int.le_of_lt hslo,Int.le_of_lt hshi⟩
    exact ⟨b,⟨hmn,hx.1,hx.2,hy.1,hy.2⟩,hix,hiy⟩
  · rintro ⟨b,hb,hpoint⟩
    have hp : (0 : Int)<boardHalf b.level := by exact_mod_cast board_half_pos b.level
    have hbr := (red_band_iff_closed_interval hp).mpr ⟨b.cx,b.centered_x,hpoint.1⟩
    have hbs := (red_band_iff_closed_interval hp).mpr ⟨b.cy,b.centered_y,hpoint.2⟩
    refine ⟨?_,?_,b.level,b.level_pos,hb.1,hbr,hbs⟩
    · have hi := hpoint.2.1
      have hb' := hb.2.2.2.1
      omega
    · have hi := hpoint.2.2
      have hb' := hb.2.2.2.2
      omega

#print axioms red_band_iff_closed_interval
#print axioms boardCovered_iff_lower_square
#print axioms red_squares_strictly_nested
#print axioms same_level_square_centers
end K230Verification
