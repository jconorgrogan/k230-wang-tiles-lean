module
public import ActualChannels
public import CenteredFullBoard
public section
namespace K230Verification

@[expose] noncomputable def centerTM (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) : Quad TMColor :=
  fullTM (indexedFullTile (T (centerCell b N r s)))
@[expose] noncomputable def centerGroup (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) : Nat × Nat × Nat :=
  indexedGroup (T (centerCell b N r s))

theorem centerGroup_mem (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) :
    centerGroup T b N r s ∈ exactGroups.toList := (indexedGroup_spec _).1

theorem centerTM_mem (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) :
    centerTM T b N r s ∈ tmFamily (centerGroup T b N r s).2.2 := by
  obtain ⟨t,ht,he⟩ := (indexedGroup_spec (T (centerCell b N r s))).2
  unfold centerTM
  rw [he]
  exact ht

theorem centerTM_horizontal (T : Cell → Fin 11487) (hT : FullValid T) (b : Cell) (N : Nat) (r s : Int) :
    (centerTM T b N r s).e=(centerTM T b N (r+1) s).w := by
  have h := hT (centerCell b N r s,true)
  change (indexedFullTile (T (centerCell b N r s))).e=
    (indexedFullTile (T ((centerCell b N r s).1+1,(centerCell b N r s).2))).w at h
  rw [centerCell_horizontal] at h
  exact congrArg (fun c : FullColor => c.2.2) h

theorem centerTM_vertical (T : Cell → Fin 11487) (hT : FullValid T) (b : Cell) (N : Nat) (r s : Int) :
    (centerTM T b N r s).n=(centerTM T b N r (s+1)).s := by
  have h := hT (centerCell b N r s,false)
  change (indexedFullTile (T (centerCell b N r s))).n=
    (indexedFullTile (T ((centerCell b N r s).1,(centerCell b N r s).2+1))).s at h
  rw [centerCell_vertical] at h
  exact congrArg (fun c : FullColor => c.2.2) h

theorem centerGroup_channels (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) :
    groupChannel (centerGroup T b N r s)=fullChannels (indexedFullTile (T (centerCell b N r s))) :=
  (indexed_channels _).symm

theorem computing_half_four (k : Nat) : boardHalf (k+2)=4*(2*4^k) := by
  have he : k+2-1=k+1 := by omega
  simp only [boardHalf,he,Nat.pow_succ]
  omega

theorem center_coordinate_mod {k : Nat} {r : Int} (hr : -(boardHalf (k+2) : Int)≤r) :
    (((boardHalf (k+2) : Int)+r).toNat)%4=1 ↔ r%4=1 := by
  have he : (((boardHalf (k+2) : Int)+r).toNat : Int)=(boardHalf (k+2) : Int)+r :=
    Int.toNat_of_nonneg (by omega)
  have hf := computing_half_four k
  omega

theorem centerGroup_presence (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hb : FullBoardAt T (k+1) v b) (r s : Int)
    (hr : -(boardHalf (k+2) : Int)≤r ∧ r≤boardHalf (k+2))
    (hs : -(boardHalf (k+2) : Int)≤s ∧ s≤boardHalf (k+2)) :
    ((groupChannel (centerGroup T b (k+2) r s)).e≠0 ↔ s%4=1) ∧
    ((groupChannel (centerGroup T b (k+2) r s)).w≠0 ↔ s%4=1) ∧
    ((groupChannel (centerGroup T b (k+2) r s)).n≠0 ↔ r%4=1) ∧
    ((groupChannel (centerGroup T b (k+2) r s)).s≠0 ↔ r%4=1) := by
  have hp := computing_board_channel_pattern T k v b hb
    ((boardHalf (k+2) : Int)+r).toNat ((boardHalf (k+2) : Int)+s).toNat
    (by omega) (by omega)
  rw [←centerCell_nat b (k+2) r s hr.1 hs.1] at hp
  rw [centerGroup_channels]
  exact ⟨hp.1.trans (center_coordinate_mod hs.1),hp.2.1.trans (center_coordinate_mod hs.1),
    hp.2.2.1.trans (center_coordinate_mod hr.1),hp.2.2.2.trans (center_coordinate_mod hr.1)⟩

theorem centerTM_seed (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) : centerTM T b (k+2) 0 0 ∈ tmFamily 5 := by
  have hs := computing_board_center_seed T k v b hv hb
  have hc : centerCell b (k+2) 0 0=boardCell b (boardHalf (k+2)) (boardHalf (k+2)) := by
    apply Prod.ext <;> simp [centerCell,boardCell]
  have hm := centerTM_mem T b (k+2) 0 0
  change (indexedGroup (T (boardCell b (boardHalf (k+2)) (boardHalf (k+2))))).2.2=5 at hs
  change centerTM T b (k+2) 0 0 ∈ tmFamily (indexedGroup (T (centerCell b (k+2) 0 0))).2.2 at hm
  rw [hc,hs] at hm
  exact hm

#print axioms centerGroup_presence
#print axioms centerTM_seed
end K230Verification
