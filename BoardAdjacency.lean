module
public import BoardOwnership
public section
set_option maxHeartbeats 0
namespace K230Verification

/-- The laminar separation remains valid across one lattice edge because
    every red half-width is at least two. -/
theorem interval_neighbor_inside {h c L R x y : Int} (hh : 2≤h)
    (hc : CenteredAt h c) (hL : L%(4*h)=0) (hR : R%(4*h)=0)
    (hx : ClosedInterval h c x) (hy : L≤y ∧ y≤R) (hd : -1≤x-y ∧ x-y≤1) :
    L<c-h ∧ c+h<R := by
  have hl := center_boundary_gap (show 0<h by omega) hc hL
  have hr := center_boundary_gap (show 0<h by omega) hc hR
  unfold ClosedInterval at hx
  constructor
  · rcases hl with hl|hl <;> omega
  · rcases hr with hr|hr <;> omega

theorem board_half_two (n : Nat) : 2≤boardHalf n := by
  have h : 0<4^(n-1) := Nat.pow_pos (by decide)
  unfold boardHalf
  omega

theorem red_squares_neighbor_nested {a b : RedSquare} {p q : Int × Int}
    (hab : a.level<b.level) (ha : InRedSquare a p) (hb : InRedSquare b q)
    (hdx : -1≤p.1-q.1 ∧ p.1-q.1≤1) (hdy : -1≤p.2-q.2 ∧ p.2-q.2≤1) :
    StrictlyInside a b := by
  have hpos : (2:Int)≤boardHalf a.level := by have := board_half_two a.level; omega
  have hd := lower_period_dvd_half a.level_pos hab
  have hbx := coarse_boundaries_aligned hd b.centered_x
  have hby := coarse_boundaries_aligned hd b.centered_y
  have hx := interval_neighbor_inside hpos a.centered_x hbx.1 hbx.2 ha.1 hb.1 hdx
  have hy := interval_neighbor_inside hpos a.centered_y hby.1 hby.2 ha.2 hb.2 hdy
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem same_level_neighbor_centers {h a b x y : Int} (hh : 0<h)
    (ha : CenteredAt h a) (hb : CenteredAt h b)
    (hxa : ClosedInterval h a x) (hyb : ClosedInterval h b y)
    (hd : -1≤x-y ∧ x-y≤1) : a=b := by
  have hrem : (a-b)%(4*h)=0 := by rw [Int.sub_emod,ha,hb]; simp
  have he := Int.mul_ediv_add_emod (a-b) (4*h)
  rw [hrem] at he
  unfold ClosedInterval at hxa hyb
  by_cases hp : 0<(a-b)/(4*h)
  · have hmul := Int.mul_le_mul_of_nonneg_left (show 1≤(a-b)/(4*h) by omega) (show 0≤4*h by omega)
    simp only [Int.mul_one] at hmul
    omega
  by_cases hn : (a-b)/(4*h)<0
  · have hmul := Int.mul_le_mul_of_nonneg_left (show (a-b)/(4*h)≤-1 by omega) (show 0≤4*h by omega)
    simp only [Int.mul_neg,Int.mul_one] at hmul
    omega
  · have hz : (a-b)/(4*h)=0 := by omega
    simp [hz] at he
    omega

theorem same_level_neighbor_square {a b : RedSquare} {p q : Int × Int}
    (hab : a.level=b.level) (ha : InRedSquare a p) (hb : InRedSquare b q)
    (hdx : -1≤p.1-q.1 ∧ p.1-q.1≤1) (hdy : -1≤p.2-q.2 ∧ p.2-q.2≤1) :
    a.cx=b.cx ∧ a.cy=b.cy := by
  have hpos : (0:Int)<boardHalf a.level := by have := board_half_pos a.level; omega
  have hbx : CenteredAt (boardHalf a.level) b.cx := hab ▸ b.centered_x
  have hby : CenteredAt (boardHalf a.level) b.cy := hab ▸ b.centered_y
  have hix : ClosedInterval (boardHalf a.level) b.cx q.1 := hab ▸ hb.1
  have hiy : ClosedInterval (boardHalf a.level) b.cy q.2 := hab ▸ hb.2
  exact ⟨same_level_neighbor_centers hpos a.centered_x hbx ha.1 hix hdx,
    same_level_neighbor_centers hpos a.centered_y hby ha.2 hiy hdy⟩

/-- Adjacent cells cannot have disjoint red-board owners. -/
theorem neighboring_owners_comparable {a b : RedSquare} {p q : Int × Int}
    (ha : Owns a p) (hb : Owns b q)
    (hdx : -1≤p.1-q.1 ∧ p.1-q.1≤1) (hdy : -1≤p.2-q.2 ∧ p.2-q.2≤1) :
    (a.level=b.level ∧ a.cx=b.cx ∧ a.cy=b.cy) ∨ StrictlyInside a b ∨ StrictlyInside b a := by
  by_cases hlt : a.level<b.level
  · exact Or.inr (Or.inl (red_squares_neighbor_nested hlt ha.1 hb.1 hdx hdy))
  by_cases hgt : b.level<a.level
  · exact Or.inr (Or.inr (red_squares_neighbor_nested hgt hb.1 ha.1 (by omega) (by omega)))
  · have he : a.level=b.level := by omega
    exact Or.inl ⟨he,same_level_neighbor_square he ha.1 hb.1 hdx hdy⟩

/-- Crossing from the smaller owner to the larger owner exits the smaller
    board at its right ring, with no hidden intervening cell. -/
theorem owner_horizontal_exit {a b : RedSquare} {r s : Int}
    (ha : Owns a (r,s)) (hb : Owns b (r+1,s)) (hlt : a.level<b.level) :
    r=a.cx+boardHalf a.level := by
  have hn : ¬InRedSquare a (r+1,s) := owner_exposed hb hlt
  have hx := ha.1.1
  have hy := ha.1.2
  unfold ClosedInterval at hx
  by_cases he : r=a.cx+boardHalf a.level
  · exact he
  · exact False.elim (hn ⟨by unfold ClosedInterval; omega,hy⟩)

theorem owner_vertical_exit {a b : RedSquare} {r s : Int}
    (ha : Owns a (r,s)) (hb : Owns b (r,s+1)) (hlt : a.level<b.level) :
    s=a.cy+boardHalf a.level := by
  have hn : ¬InRedSquare a (r,s+1) := owner_exposed hb hlt
  have hx := ha.1.1
  have hy := ha.1.2
  unfold ClosedInterval at hy
  by_cases he : s=a.cy+boardHalf a.level
  · exact he
  · exact False.elim (hn ⟨hx,by unfold ClosedInterval; omega⟩)

end K230Verification
#print axioms K230Verification.neighboring_owners_comparable
#print axioms K230Verification.owner_horizontal_exit
