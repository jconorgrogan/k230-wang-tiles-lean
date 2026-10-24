module
public import RootChannelGeometry
public import EntryIndices
public import RingExposure
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem hBoundary_has_channel (b : Nat) (hb : hBoundary b) : HasHChannel b := by
  unfold hBoundary at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem vBoundary_has_channel (b : Nat) (hb : vBoundary b) : HasVChannel b := by
  unfold vBoundary at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem active_half_mod_four (n : Nat) (hn : 1≤n) : (boardHalf (n+1):Int)%4=0 := by
  have hh := fullBoard_half n
  obtain ⟨d,hd⟩ := four_dvd_squareSize n hn
  omega

theorem relative_channel_pattern (n v : Nat) (hn : 1≤n) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r) (hs : -(boardHalf (n+1):Int)≤s) :
    (HasHChannel (boardAtRelative n v r s).val ↔ s%4=1) ∧
    (HasVChannel (boardAtRelative n v r s).val ↔ r%4=1) := by
  have hd := active_half_mod_four n hn
  have hx : ((boardHalf (n+1):Int)+r).toNat%4=1 ↔ r%4=1 := by omega
  have hy : ((boardHalf (n+1):Int)+s).toNat%4=1 ↔ s%4=1 := by omega
  have h := redBoard_modulo_four n hn v ((boardHalf (n+1):Int)+r).toNat
    ((boardHalf (n+1):Int)+s).toNat
  simpa only [boardAtRelative,hx,hy] using h

@[expose] def relativeSide (n v side : Nat) (r : Int) : Fin 156 :=
  boardAtRelative n v
    (if side=0 then -(boardHalf (n+1):Int) else if side=1 then boardHalf (n+1) else r)
    (if side=2 then -(boardHalf (n+1):Int) else if side=3 then boardHalf (n+1) else r)

theorem relativeSide_eq (n v side : Nat) (hside : side<4) (r : Int) :
    relativeSide n v side r = sideCell n v side ((boardHalf (n+1):Int)+r).toNat := by
  have hz : ((boardHalf (n+1):Int)+(-(boardHalf (n+1):Int))).toNat=0 := by omega
  have ht : ((boardHalf (n+1):Int)+(boardHalf (n+1):Int)).toNat=4*squareSize n := by
    have hh := fullBoard_side n
    omega
  have hs : side=0 ∨ side=1 ∨ side=2 ∨ side=3 := by omega
  rcases hs with rfl|rfl|rfl|rfl <;> simp [relativeSide,boardAtRelative,sideCell,hz,ht]

theorem relative_root_options (n side v : Nat) (hn : 1≤n) (hs : side<4) (hv : v<4) (r : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1)) (hm : r%4=1) :
    (relativeSide n v side r).val=channelExpected side 1 ∨
    (relativeSide n v side r).val=channelExpected side 3 := by
  have hh := fullBoard_half n
  have hd := active_half_mod_four n hn
  have hj : 0<((boardHalf (n+1):Int)+r).toNat ∧
      ((boardHalf (n+1):Int)+r).toNat<4*squareSize n := by omega
  have hjm : ((boardHalf (n+1):Int)+r).toNat%4=1 := by omega
  rw [relativeSide_eq n v side hs r]
  exact root_side_options n side v _ hn hs hv hj hjm

theorem relative_exposed_not_boundary (n v : Nat) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1)) (he : ¬BoardCovered (n+1) r s) :
    ¬hBoundary (boardAtRelative n v r s).val ∧ ¬vBoundary (boardAtRelative n v r s).val := by
  have hh := fullBoard_half n
  let x := ((boardHalf (n+1):Int)+r).toNat
  let y := ((boardHalf (n+1):Int)+s).toNat
  have hx : 0<x ∧ x<4*squareSize n := by dsimp [x]; omega
  have hy : 0<y ∧ y<4*squareSize n := by dsimp [y]; omega
  have hxr : (x:Int)-2*squareSize n=r := by dsimp [x]; omega
  have hyr : (y:Int)-2*squareSize n=s := by dsimp [y]; omega
  exact exposed_not_boundary n v x y hv hx hy (by simpa only [hxr,hyr] using he)

theorem relative_hBoundary_location (n v : Nat) (hn : 1≤n) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1)) (he : ¬BoardCovered (n+1) r s)
    (hb : hBoundary (boardAtRelative n v r s).val) :
    (r=-(boardHalf (n+1):Int) ∧ ((boardAtRelative n v r s).val=100 ∨ (boardAtRelative n v r s).val=116)) ∨
    (r=(boardHalf (n+1):Int) ∧ ((boardAtRelative n v r s).val=95 ∨ (boardAtRelative n v r s).val=111)) := by
  have hm := (relative_channel_pattern n v hn r s hr.1 hs.1).1.mp (hBoundary_has_channel _ hb)
  have hH := active_half_mod_four n hn
  have hs' : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1) := by omega
  by_cases hl : r=-(boardHalf (n+1):Int)
  · apply Or.inl
    refine ⟨hl,?_⟩
    have h := relative_root_options n 0 v hn (by decide) hv s hs' hm
    simpa [relativeSide,channelExpected,hl,or_comm] using h
  · have hr' : r=(boardHalf (n+1):Int) := by
      by_contra hh
      exact (relative_exposed_not_boundary n v hv r s ⟨by omega,by omega⟩ hs' he).1 hb
    apply Or.inr
    refine ⟨hr',?_⟩
    have h := relative_root_options n 1 v hn (by decide) hv s hs' hm
    simpa [relativeSide,channelExpected,hr',or_comm] using h

theorem relative_vBoundary_location (n v : Nat) (hn : 1≤n) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1)) (he : ¬BoardCovered (n+1) r s)
    (hb : vBoundary (boardAtRelative n v r s).val) :
    (s=-(boardHalf (n+1):Int) ∧ ((boardAtRelative n v r s).val=136 ∨ (boardAtRelative n v r s).val=142)) ∨
    (s=(boardHalf (n+1):Int) ∧ ((boardAtRelative n v r s).val=134 ∨ (boardAtRelative n v r s).val=140)) := by
  have hm := (relative_channel_pattern n v hn r s hr.1 hs.1).2.mp (vBoundary_has_channel _ hb)
  have hH := active_half_mod_four n hn
  have hr' : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1) := by omega
  by_cases hl : s=-(boardHalf (n+1):Int)
  · apply Or.inl
    refine ⟨hl,?_⟩
    have h := relative_root_options n 2 v hn (by decide) hv r hr' hm
    simpa [relativeSide,channelExpected,hl,or_comm] using h
  · have hs' : s=(boardHalf (n+1):Int) := by
      by_contra hh
      exact (relative_exposed_not_boundary n v hv r s hr' ⟨by omega,by omega⟩ he).2 hb
    apply Or.inr
    refine ⟨hs',?_⟩
    have h := relative_root_options n 3 v hn (by decide) hv r hr' hm
    simpa [relativeSide,channelExpected,hs',or_comm] using h

theorem relative_hcopy_location (n v : Nat) (hn : 1≤n) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1))
    (hb : ¬hBoundary (boardAtRelative n v r s).val) (hm : s%4=1) :
    -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1) := by
  have hh := active_half_mod_four n hn
  have hs' : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1) := by omega
  have hl : r≠-(boardHalf (n+1):Int) := by
    intro he
    have h := relative_root_options n 0 v hn (by decide) hv s hs' hm
    have h' : (boardAtRelative n v r s).val=116 ∨ (boardAtRelative n v r s).val=100 := by
      simpa [relativeSide,channelExpected,he] using h
    unfold hBoundary at hb
    omega
  have hu : r≠(boardHalf (n+1):Int) := by
    intro he
    have h := relative_root_options n 1 v hn (by decide) hv s hs' hm
    have h' : (boardAtRelative n v r s).val=111 ∨ (boardAtRelative n v r s).val=95 := by
      simpa [relativeSide,channelExpected,he] using h
    unfold hBoundary at hb
    omega
  omega

theorem relative_vcopy_location (n v : Nat) (hn : 1≤n) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1))
    (hb : ¬vBoundary (boardAtRelative n v r s).val) (hm : r%4=1) :
    -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1) := by
  have hh := active_half_mod_four n hn
  have hr' : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1) := by omega
  have hl : s≠-(boardHalf (n+1):Int) := by
    intro he
    have h := relative_root_options n 2 v hn (by decide) hv r hr' hm
    have h' : (boardAtRelative n v r s).val=142 ∨ (boardAtRelative n v r s).val=136 := by
      simpa [relativeSide,channelExpected,he] using h
    unfold vBoundary at hb
    omega
  have hu : s≠(boardHalf (n+1):Int) := by
    intro he
    have h := relative_root_options n 3 v hn (by decide) hv r hr' hm
    have h' : (boardAtRelative n v r s).val=140 ∨ (boardAtRelative n v r s).val=134 := by
      simpa [relativeSide,channelExpected,he] using h
    unfold vBoundary at hb
    omega
  omega

#print axioms relative_hBoundary_location
#print axioms relative_vBoundary_location
end K230Verification
