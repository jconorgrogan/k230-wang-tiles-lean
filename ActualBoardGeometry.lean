module
public import ActualBoardData
public import RootChannelGeometry
public import CenterRowGeometry
public import InitialRow
public import ConcreteRoutingMasks
public section
namespace K230Verification
open K230Concrete

theorem actual_initial_left_class (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) (r : Int)
    (hl : -(boardHalf (k+2) : Int)<r) (hr : r<0) :
    (centerGroup T b (k+2) r 0).1 ∈ leftInitialBases := by
  have hhalf := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hp := board_half_pos (k+2)
  have hy : ((boardHalf (k+2) : Int)+0).toNat=2*squareSize (k+1) := by omega
  have h := fullBoard_centered_group T (k+1) v b hb r 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  simp only [hn] at h
  change (centerGroup T b (k+2) r 0).1 = _ at h
  rw [h,hy]
  exact center_row_left k v _ hv (by constructor <;> omega)

theorem actual_initial_right_class (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) (r : Int)
    (hl : 0<r) (hr : r<(boardHalf (k+2) : Int)) :
    (centerGroup T b (k+2) r 0).1 ∈ rightInitialBases := by
  have hhalf := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hp := board_half_pos (k+2)
  have hy : ((boardHalf (k+2) : Int)+0).toNat=2*squareSize (k+1) := by omega
  have h := fullBoard_centered_group T (k+1) v b hb r 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  simp only [hn] at h
  change (centerGroup T b (k+2) r 0).1 = _ at h
  rw [h,hy]
  exact center_row_right k v _ hv (by constructor <;> omega)

theorem actual_upper_side_group (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) (side : Nat) (hside : side<4) (r : Int)
    (hr : 0<r ∧ r<(boardHalf (k+2) : Int)) (hm : r%4=1) :
    (indexedGroup (T (rootSidePoint b (k+2) side r))).1=channelExpected side 3 := by
  have hh := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hx : 2*squareSize (k+1)<((boardHalf (k+2) : Int)+r).toNat ∧
      ((boardHalf (k+2) : Int)+r).toNat<4*squareSize (k+1) := by constructor <;> omega
  have hxmod := (center_coordinate_mod (show -(boardHalf (k+2) : Int)≤r by omega)).mpr hm
  rw [fullBoard_root_side_group T (k+1) v b hb side hside r ⟨by omega,by omega⟩]
  exact side_upper_channel (k+1) side v _ (by omega) hside hv hx hxmod

theorem actual_left_wall_blank (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) {r : Int}
    (hr : TapeOffset (k+2) r) (hpos : 0<r) :
    (centerTM T b (k+2) (-(boardHalf (k+2) : Int)) r).e=.blank := by
  have hg := actual_upper_side_group T k v b hv hb 0 (by decide) r ⟨hpos,hr.2.1⟩ hr.2.2.1
  change (centerGroup T b (k+2) (-(boardHalf (k+2) : Int)) r).1=100 at hg
  exact concrete_left_wall_blank (centerGroup_mem _ _ _ _ _) hg (centerTM_mem _ _ _ _ _)

theorem actual_right_wall_direction (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) {r : Int}
    (hr : TapeOffset (k+2) r) (hpos : 0<r) :
    (centerTM T b (k+2) (boardHalf (k+2)) r).w=.blank ∨
      ∃ q, (centerTM T b (k+2) (boardHalf (k+2)) r).w=.move .right q := by
  have hg := actual_upper_side_group T k v b hv hb 1 (by decide) r ⟨hpos,hr.2.1⟩ hr.2.2.1
  change (centerGroup T b (k+2) (boardHalf (k+2)) r).1=95 at hg
  exact concrete_right_wall_direction (centerGroup_mem _ _ _ _ _) hg (centerTM_mem _ _ _ _ _)

#print axioms actual_initial_left_class
#print axioms actual_initial_right_class
#print axioms actual_left_wall_blank
#print axioms actual_right_wall_direction
end K230Verification
