module
public import StretchedMembership
public section
namespace K230Verification

theorem stretchedTM_outer_north {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r : Int) :
    (stretchedTM F r (boardHalf (k+2))).n=.blank :=
  verticalWire_above F (Int.le_refl _)

theorem stretchedTM_outer_south {k : Nat} (F : FiniteBoard k230Machine (2^k)) (r : Int) :
    (stretchedTM F r (-(boardHalf (k+2) : Int))).s=.blank := by
  apply verticalWire_below
  have hp := board_half_pos (k+2)
  omega

theorem stretchedTM_outer_east {k : Nat} (F : FiniteBoard k230Machine (2^k)) (s : Int) :
    (stretchedTM F (boardHalf (k+2)) s).e=.blank := by
  apply horizontalWire_outside
  omega

theorem stretchedTM_outer_west {k : Nat} (F : FiniteBoard k230Machine (2^k)) (s : Int) :
    (stretchedTM F (-(boardHalf (k+2) : Int)) s).w=.blank := by
  apply horizontalWire_outside
  omega

theorem stretchedTM_comp_family_at {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r s : Int}
    (hr : TapeOffset (k+2) r) (hs : TapeOffset (k+2) s ∧ 0<s) :
    stretchedTM F r s ∈ tmFamily 13 := by
  obtain ⟨i,hi,he⟩ := physicalColumn_surjective hr
  obtain ⟨t,ht,hy⟩ := physicalRow_surjective hs.1 hs.2
  rw [←he,←hy]
  exact stretchedTM_comp_family F hi ht

theorem stretchedTM_seed_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F 0 0 ∈ tmFamily 5 := by rw [stretchedTM_seed]; simp [tmFamily]

theorem stretchedTM_start_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F 1 0 ∈ tmFamily 10 := by
  rw [stretchedTM_start]
  apply List.mem_append_right
  simp

theorem stretchedTM_init_left_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<0) (ht : TapeOffset (k+2) r) :
    stretchedTM F r 0 ∈ tmFamily 8 := by
  rw [stretchedTM_initial_left F hr]
  simp only [if_pos ht]
  apply List.mem_append_right
  simp

theorem stretchedTM_init_right_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : 1<r ∧ r<(boardHalf (k+2) : Int)) (ht : TapeOffset (k+2) r) :
    stretchedTM F r 0 ∈ tmFamily 10 := by
  rw [stretchedTM_initial_right F hr]
  simp only [if_pos ht]
  apply List.mem_append_right
  simp

theorem stretchedTM_init_left_pass {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<0) (ht : ¬TapeOffset (k+2) r) :
    stretchedTM F r 0 ∈ tmFamily 1 := by
  rw [stretchedTM_initial_left F hr]
  simp [ht,tmFamily]

theorem stretchedTM_init_right_pass {k : Nat} (F : FiniteBoard k230Machine (2^k)) {r : Int}
    (hr : 1<r ∧ r<(boardHalf (k+2) : Int)) (ht : ¬TapeOffset (k+2) r) :
    stretchedTM F r 0 ∈ tmFamily 2 := by
  rw [stretchedTM_initial_right F hr]
  simp [ht,tmFamily]

theorem stretchedTM_init_left_wall_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F (-(boardHalf (k+2) : Int)) 0 ∈ tmFamily 4 := by
  rw [stretchedTM_initial_left_wall]
  simp [tmFamily]

theorem stretchedTM_init_right_wall_family {k : Nat} (F : FiniteBoard k230Machine (2^k)) :
    stretchedTM F (boardHalf (k+2)) 0 ∈ tmFamily 3 := by
  rw [stretchedTM_initial_right_wall]
  simp [tmFamily]

#print axioms stretchedTM_outer_north
#print axioms stretchedTM_comp_family_at
#print axioms stretchedTM_init_left_family
end K230Verification
