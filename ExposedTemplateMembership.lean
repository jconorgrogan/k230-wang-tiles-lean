module
public import ExposedInitialMembership
public import ConcreteRoutingMasks
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem piece_family_nine_location {k v : Nat} (hv : v<4) (left bottom : Int → Channel)
    {g : Nat × Nat × Nat} (hg : g ∈ exactGroups.toList) {r s : Int}
    (hr : -(boardHalf (k+2) : Int)≤r ∧ r≤boardHalf (k+2))
    (hs : -(boardHalf (k+2) : Int)≤s ∧ s≤boardHalf (k+2)) (hexp : ¬BoardCovered (k+2) r s)
    (hbase : g.1=(boardAtRelative (k+1) v r s).val)
    (hchan : groupChannel g=pieceChannels (k+2) left bottom r s) (hf : g.2.2=9) :
    s=(boardHalf (k+2) : Int) ∧ TapeOffset (k+2) r := by
  have ha := (concrete_absorber_groups g hg).2.mp hf
  have hB : vBoundary (boardAtRelative (k+1) v r s).val := by
    rw [←hbase]
    unfold vBoundary
    omega
  have hl := relative_vBoundary_location (k+1) v (by omega) hv r s hr hs hexp hB
  have htop : s=(boardHalf (k+2) : Int) := by
    rcases hl with ⟨_,hl⟩|⟨h,_⟩
    · rw [←hbase] at hl; omega
    · exact h
  refine ⟨htop,?_⟩
  have hm := (relative_channel_pattern (k+1) v (by omega) r s hr.1 hs.1).2.mp
    (vBoundary_has_channel _ hB)
  have hhalf := active_half_mod_four (k+1) (by omega)
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  rw [hn] at hhalf
  have hri : -(boardHalf (k+2) : Int)<r ∧ r<(boardHalf (k+2) : Int) := by omega
  have hS : (groupChannel g).s=1 := by simp [groupChannel,ha.2]
  have hcode := congrArg Quad.s hchan
  change (groupChannel g).s=pieceV (k+2) bottom r (s-1) at hcode
  rw [htop] at hcode
  have hp := board_half_pos (k+2)
  exact (pieceV_one_iff_tape (by omega) bottom hri ⟨by omega,by omega⟩).mp (hcode.symm.trans hS)

theorem piece_blank_permitted {k v : Nat} (hv : v<4) (left bottom : Int → Channel)
    {g : Nat × Nat × Nat} (hg : g ∈ exactGroups.toList) {r s : Int}
    (hr : -(boardHalf (k+2) : Int)≤r ∧ r≤boardHalf (k+2))
    (hs : -(boardHalf (k+2) : Int)≤s ∧ s≤boardHalf (k+2)) (hexp : ¬BoardCovered (k+2) r s)
    (hbase : g.1=(boardAtRelative (k+1) v r s).val)
    (hchan : groupChannel g=pieceChannels (k+2) left bottom r s)
    (hs0 : s≠0) (h9 : ¬(s=(boardHalf (k+2) : Int) ∧ TapeOffset (k+2) r)) :
    tmBlank ∈ tmFamily g.2.2 := by
  apply blank_template_member g.2.2 (concrete_group_bounds g hg).2.2
  · intro hf
    have hh := (family_three_iff_right_midpoint g hg).mp hf
    rw [hbase] at hh
    exact hs0 (relative_exposed_right_midpoint (k+1) v hv r s hr hs hexp hh).2
  · intro hf
    have hh := (family_four_iff_left_midpoint g hg).mp hf
    rw [hbase] at hh
    exact hs0 (relative_exposed_left_midpoint (k+1) v hv r s hr hs hexp hh).2
  · intro hf
    have hh := (exact_seed_class g hg).mp hf
    rw [hbase] at hh
    exact hs0 (relative_exposed_seed (k+1) v hv r s hr hs hexp hh).2
  · intro hf
    exact h9 (piece_family_nine_location hv left bottom hg hr hs hexp hbase hchan hf)

/-- Every exposed cell of the stretched finite machine run has a template
    in the exact concrete group selected by its base and channel layers. -/
theorem piece_template_member {k v : Nat} (F : FiniteBoard k230Machine (2^k)) (hv : v<4)
    (left bottom : Int → Channel) {g : Nat × Nat × Nat} (hg : g ∈ exactGroups.toList) {r s : Int}
    (hr : -(boardHalf (k+2) : Int)≤r ∧ r≤boardHalf (k+2))
    (hs : -(boardHalf (k+2) : Int)≤s ∧ s≤boardHalf (k+2)) (hexp : ¬BoardCovered (k+2) r s)
    (hbase : g.1=(boardAtRelative (k+1) v r s).val)
    (hchan : groupChannel g=pieceChannels (k+2) left bottom r s) :
    stretchedTM F r s ∈ tmFamily g.2.2 := by
  have hp := board_half_pos (k+2)
  by_cases hs0 : s=0
  · subst s
    exact piece_initial_member F hv left bottom hg hr hbase hchan
  by_cases hsneg : s<0
  · rw [stretchedTM_below F hsneg]
    apply piece_blank_permitted hv left bottom hg hr hs hexp hbase hchan hs0
    intro h; have := h.1; omega
  have hspos : 0<s := by omega
  have hN : (groupChannel g).n=pieceV (k+2) bottom r s := congrArg Quad.n hchan
  have hE : (groupChannel g).e=pieceH (k+2) left r s := congrArg Quad.e hchan
  have hS : (groupChannel g).s=pieceV (k+2) bottom r (s-1) := congrArg Quad.s hchan
  have hW : (groupChannel g).w=pieceH (k+2) left (r-1) s := congrArg Quad.w hchan
  classical
  by_cases hrow : TapeOffset (k+2) s
  · have hsi : -(boardHalf (k+2) : Int)<s ∧ s<(boardHalf (k+2) : Int) := ⟨hrow.1,hrow.2.1⟩
    by_cases hleft : r=-(boardHalf (k+2) : Int)
    · subst r
      have hb := relative_upper_side k 0 v (by decide) hv s ⟨hspos,hrow.2.1⟩ hrow.2.2.1
      change (boardAtRelative (k+1) v (-(boardHalf (k+2) : Int)) s).val=100 at hb
      have hf := concrete_left_wall_group g hg (hbase.trans hb)
      rw [hf,stretchedTM_left_wall F ⟨hrow,hspos⟩]
      simp [tmFamily]
    by_cases hright : r=(boardHalf (k+2) : Int)
    · subst r
      have hb := relative_upper_side k 1 v (by decide) hv s ⟨hspos,hrow.2.1⟩ hrow.2.2.1
      change (boardAtRelative (k+1) v (boardHalf (k+2)) s).val=95 at hb
      have hw1 : (groupChannel g).w=1 := hW.trans (pieceH_tape_zero (by omega) left hrow ⟨by omega,by omega⟩)
      have hf := reverse_right_absorber_family g hg (hbase.trans hb) hw1
      rw [hf]
      exact stretchedTM_right_wall_family F ⟨hrow,hspos⟩
    have hri : -(boardHalf (k+2) : Int)<r ∧ r<(boardHalf (k+2) : Int) := by omega
    have he1 : (groupChannel g).e=1 := hE.trans (pieceH_tape_zero (by omega) left hrow ⟨by omega,hri.2⟩)
    by_cases hcol : TapeOffset (k+2) r
    · have hn1 : (groupChannel g).n=1 := hN.trans (pieceV_tape_zero (by omega) bottom hcol ⟨by omega,hrow.2.1⟩)
      have hf := concrete_NE_zero_comp g hg hn1 he1
      rw [hf]
      exact stretchedTM_comp_family_at F hcol ⟨hrow,hspos⟩
    · have hn : (groupChannel g).n=0 ∨ (groupChannel g).n=3 := by
        rw [hN]
        exact pieceV_upper_nonfree (by omega) bottom hri hcol ⟨by omega,hrow.2.1⟩
      have hnb := (relative_exposed_not_boundary (k+1) v hv r s hri hsi hexp).1
      have hf := reverse_row_family g hg he1 hn (by rw [hbase]; exact hnb)
      rw [hf]
      exact stretchedTM_row_family F hri hcol ⟨hrow,hspos⟩
  · by_cases hcol : TapeOffset (k+2) r
    · have hri : -(boardHalf (k+2) : Int)<r ∧ r<(boardHalf (k+2) : Int) := ⟨hcol.1,hcol.2.1⟩
      by_cases htop : s=(boardHalf (k+2) : Int)
      · subst s
        have hb := relative_root_options (k+1) 3 v (by omega) (by decide) hv r hri hcol.2.2.1
        have hb' : g.1=134 ∨ g.1=140 := by
          rw [hbase]
          simpa [relativeSide,channelExpected,or_comm] using hb
        have hs1 : (groupChannel g).s=1 := hS.trans (pieceV_tape_zero (by omega) bottom hcol ⟨by omega,by omega⟩)
        have hf := reverse_top_family g hg hb' hs1
        rw [hf]
        exact stretchedTM_top_family F hcol
      · have hsi : -(boardHalf (k+2) : Int)<s ∧ s<(boardHalf (k+2) : Int) := by omega
        have hn1 : (groupChannel g).n=1 := hN.trans (pieceV_tape_zero (by omega) bottom hcol ⟨by omega,hsi.2⟩)
        have he1 : (groupChannel g).e≠1 := by
          rw [hE]
          intro he
          exact hrow ((pieceH_one_iff_tape (by omega) left hsi ⟨by omega,hri.2⟩).mp he)
        have hnb := (relative_exposed_not_boundary (k+1) v hv r s hri hsi hexp).2
        have hf := reverse_column_families g hg hn1 he1 (by rw [hbase]; exact hnb)
        exact column_template_member hf (stretchedTM_column_family F hcol ⟨hspos,hsi.2⟩ hrow)
    · rw [stretchedTM_blank F hcol (fun h => hrow h.1) hs0]
      exact piece_blank_permitted hv left bottom hg hr hs hexp hbase hchan hs0 (fun h => hcol h.2)

#print axioms piece_family_nine_location
#print axioms piece_template_member
end K230Verification
