module
public import ExposedRoleFacts
public import StretchedSupport
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem piece_initial_member {k v : Nat} (F : FiniteBoard k230Machine (2^k)) (hv : v<4)
    (left bottom : Int → Channel) {g : Nat × Nat × Nat} (hg : g ∈ exactGroups.toList) {r : Int}
    (hr : -(boardHalf (k+2) : Int)≤r ∧ r≤boardHalf (k+2))
    (hbase : g.1=(boardAtRelative (k+1) v r 0).val)
    (hchan : groupChannel g=pieceChannels (k+2) left bottom r 0) :
    stretchedTM F r 0 ∈ tmFamily g.2.2 := by
  have hp := board_half_pos (k+2)
  have hN : (groupChannel g).n=pieceV (k+2) bottom r 0 := congrArg Quad.n hchan
  by_cases hleft : r=-(boardHalf (k+2) : Int)
  · subst r
    have hf : g.2.2=4 := (family_four_iff_left_midpoint g hg).mpr (by
      rw [hbase]
      exact relative_left_midpoint (k+1) v hv)
    rw [hf]
    exact stretchedTM_init_left_wall_family F
  by_cases hright : r=(boardHalf (k+2) : Int)
  · subst r
    have hf : g.2.2=3 := (family_three_iff_right_midpoint g hg).mpr (by
      rw [hbase]
      exact relative_right_midpoint (k+1) v hv)
    rw [hf]
    exact stretchedTM_init_right_wall_family F
  have hri : -(boardHalf (k+2) : Int)<r ∧ r<(boardHalf (k+2) : Int) := by omega
  by_cases hzero : r=0
  · subst r
    have hf : g.2.2=5 := (exact_seed_class g hg).mpr (by rw [hbase]; exact relative_center_seed (k+1) v hv)
    rw [hf]
    exact stretchedTM_seed_family F
  have hc : (groupChannel g).n=0 ∨ (groupChannel g).n=1 ∨ (groupChannel g).n=3 := by
    rw [hN]
    exact pieceV_initial_values (by omega) bottom hri
  have hiff : (groupChannel g).n=1 ↔ TapeOffset (k+2) r := by
    rw [hN]
    exact pieceV_one_iff_tape (by omega) bottom hri ⟨by omega,by omega⟩
  by_cases hneg : r<0
  · have hclass : g.1 ∈ leftInitialBases := by rw [hbase]; exact relative_center_left k v hv r ⟨hri.1,hneg⟩
    have hf := left_initial_group g hg hclass hc
    classical
    by_cases ht : TapeOffset (k+2) r
    · rw [hf.2.mpr (hiff.mpr ht)]
      exact stretchedTM_init_left_family F ⟨hri.1,hneg⟩ ht
    · have hne : g.2.2≠8 := fun h => ht (hiff.mp (hf.2.mp h))
      have he : g.2.2=1 := by omega
      rw [he]
      exact stretchedTM_init_left_pass F ⟨hri.1,hneg⟩ ht
  · have hpos : 0<r := by omega
    have hclass : g.1 ∈ rightInitialBases := by rw [hbase]; exact relative_center_right k v hv r ⟨hpos,hri.2⟩
    have hf := right_initial_group g hg hclass hc
    by_cases hstart : r=1
    · subst r
      have ht := (positiveTape_mem.mp (start_is_positive_tape k)).1
      rw [hf.2.mpr (hiff.mpr ht)]
      exact stretchedTM_start_family F
    · have hgt : 1<r := by omega
      classical
      by_cases ht : TapeOffset (k+2) r
      · rw [hf.2.mpr (hiff.mpr ht)]
        exact stretchedTM_init_right_family F ⟨hgt,hri.2⟩ ht
      · have hne : g.2.2≠10 := fun h => ht (hiff.mp (hf.2.mp h))
        have he : g.2.2=2 := by omega
        rw [he]
        exact stretchedTM_init_right_pass F ⟨hgt,hri.2⟩ ht

#print axioms piece_initial_member
end K230Verification
