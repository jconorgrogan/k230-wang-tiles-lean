module
public import ConstructedChannels
public import PieceChannelGeometry
public import ChannelCompleteness
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem pieceChannels_legal (n v : Nat) (hn : 1≤n) (hv : v<4)
    (left bottom : Int → Channel)
    (hl : ∀ s, s%4=1 → EndAllows .outerLeft (left s))
    (hb : ∀ r, r%4=1 → EndAllows .outerLeft (bottom r)) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) :
    ChannelLegal (boardAtRelative n v r s).val (pieceChannels (n+1) left bottom r s) := by
  have hp := relative_channel_pattern n v hn r s hr.1 hs.1
  have hH := active_half_mod_four n hn
  have hloc := relative_hBoundary_location n v hn hv r s hr hs he
  have vloc := relative_vBoundary_location n v hn hv r s hr hs he
  have hpres (h : hBoundary (boardAtRelative n v r s).val) : s%4=1 := hp.1.mp (hBoundary_has_channel _ h)
  have vpres (h : vBoundary (boardAtRelative n v r s).val) : r%4=1 := hp.2.mp (vBoundary_has_channel _ h)
  unfold ChannelLegal
  refine ⟨(boardAtRelative n v r s).isLt, pieceV_bounds _ _ _ _, pieceH_bounds _ _ _ _,
    pieceV_bounds _ _ _ _, pieceH_bounds _ _ _ _,
    (pieceV_presence _ _ _ _).trans hp.2.symm, (pieceV_presence _ _ _ _).trans hp.2.symm,
    (pieceH_presence _ _ _ _).trans hp.1.symm, (pieceH_presence _ _ _ _).trans hp.1.symm,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro h
    change pieceH _ _ _ _=pieceH _ _ _ _
    by_cases hm : s%4=1
    · have hr' := relative_hcopy_location n v hn hv r s hr hs h hm
      apply pieceH_copy _ _ _ _ hr'
      rintro ⟨_,_,m,hm1,hmn,hmr,hms⟩
      exact he ⟨by omega,by omega,m,hm1,hmn,hms,hmr⟩
    · rw [pieceH_absent _ _ _ _ hm,pieceH_absent _ _ _ _ hm]
  · intro h
    change pieceV _ _ _ _=pieceV _ _ _ _
    by_cases hm : r%4=1
    · exact pieceV_copy _ _ _ _ (relative_vcopy_location n v hn hv r s hr hs h hm) he
    · rw [pieceV_absent _ _ _ _ hm,pieceV_absent _ _ _ _ hm]
  · intro h
    have hbd : hBoundary (boardAtRelative n v r s).val := by unfold hBoundary; omega
    have hm := hpres hbd
    have hh : r=-(boardHalf (n+1):Int) := by have := hloc hbd; omega
    subst r
    exact pieceH_left_masks (n+1) left (by omega) hl s hm
  · intro h
    have hbd : hBoundary (boardAtRelative n v r s).val := by unfold hBoundary; omega
    have hm := hpres hbd
    have hh : r=(boardHalf (n+1):Int) := by have := hloc hbd; omega
    subst r
    exact pieceH_right_masks (n+1) left (by omega) s hm
  · intro h
    have hbd : vBoundary (boardAtRelative n v r s).val := by unfold vBoundary; omega
    have hm := vpres hbd
    have hh : s=-(boardHalf (n+1):Int) := by have := vloc hbd; omega
    subst s
    exact pieceV_bottom_masks (n+1) bottom (by omega) hb r hm
  · intro h
    have hbd : vBoundary (boardAtRelative n v r s).val := by unfold vBoundary; omega
    have hm := vpres hbd
    have hh : s=(boardHalf (n+1):Int) := by have := vloc hbd; omega
    subst s
    exact pieceV_top_masks (n+1) bottom (by omega) r hm
  · intro h
    have hbd : hBoundary (boardAtRelative n v r s).val := by unfold hBoundary; omega
    have := hloc hbd
    omega
  · intro h
    have hbd : hBoundary (boardAtRelative n v r s).val := by unfold hBoundary; omega
    have := hloc hbd
    omega
  · intro h
    have hbd : vBoundary (boardAtRelative n v r s).val := by unfold vBoundary; omega
    have := vloc hbd
    omega
  · intro h
    have hbd : vBoundary (boardAtRelative n v r s).val := by unfold vBoundary; omega
    have := vloc hbd
    omega

#print axioms pieceChannels_legal
end K230Verification
