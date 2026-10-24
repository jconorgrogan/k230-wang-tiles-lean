module
public import ConstructedSignalValues
public import PieceChannelGeometry
public import ExposedMidpoints
public import SeedGeometry
public import RootExposure
public import InitialRow
public import CenterRowGeometry
public import MandatoryFamilies
public import RoleCompleteness
public section
namespace K230Verification
open K230Concrete

theorem relative_exposed_seed (n v : Nat) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1) : Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1) : Int)≤s ∧ s≤boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) (hb : SeedBase (boardAtRelative n v r s).val) : r=0 ∧ s=0 := by
  have hh := fullBoard_half n
  let x := ((boardHalf (n+1) : Int)+r).toNat
  let y := ((boardHalf (n+1) : Int)+s).toNat
  have hx : x≤4*squareSize n := by dsimp [x]; omega
  have hy : y≤4*squareSize n := by dsimp [y]; omega
  have hxr : (x:Int)-(boardHalf (n+1) : Int)=r := by dsimp [x]; omega
  have hyr : (y:Int)-(boardHalf (n+1) : Int)=s := by dsimp [y]; omega
  have hc := exposed_seed_center n v x y hv hx hy hb (by simpa only [hxr,hyr] using he)
  dsimp [x,y] at hc
  omega

theorem relative_exposed_left_midpoint (n v : Nat) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1) : Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1) : Int)≤s ∧ s≤boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) (hb : (boardAtRelative n v r s).val ∈ [47,49,50,52]) :
    r=-(boardHalf (n+1) : Int) ∧ s=0 := by
  have hh := fullBoard_half n
  let x := ((boardHalf (n+1) : Int)+r).toNat
  let y := ((boardHalf (n+1) : Int)+s).toNat
  have hx : x≤4*squareSize n := by dsimp [x]; omega
  have hy : y≤4*squareSize n := by dsimp [y]; omega
  have hxr : (x:Int)-2*squareSize n=r := by dsimp [x]; omega
  have hyr : (y:Int)-2*squareSize n=s := by dsimp [y]; omega
  have hc := exposed_left_midpoint n v x y hv hx hy (by simpa only [hxr,hyr] using he) hb
  dsimp [x,y] at hc
  omega

theorem relative_exposed_right_midpoint (n v : Nat) (hv : v<4) (r s : Int)
    (hr : -(boardHalf (n+1) : Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1) : Int)≤s ∧ s≤boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) (hb : (boardAtRelative n v r s).val ∈ [35,36,37,38]) :
    r=(boardHalf (n+1) : Int) ∧ s=0 := by
  have hh := fullBoard_half n
  let x := ((boardHalf (n+1) : Int)+r).toNat
  let y := ((boardHalf (n+1) : Int)+s).toNat
  have hx : x≤4*squareSize n := by dsimp [x]; omega
  have hy : y≤4*squareSize n := by dsimp [y]; omega
  have hxr : (x:Int)-2*squareSize n=r := by dsimp [x]; omega
  have hyr : (y:Int)-2*squareSize n=s := by dsimp [y]; omega
  have hc := exposed_right_midpoint n v x y hv hx hy (by simpa only [hxr,hyr] using he) hb
  dsimp [x,y] at hc
  omega

theorem relative_center_seed (n v : Nat) (hv : v<4) : SeedBase (boardAtRelative n v 0 0).val := by
  have hh := fullBoard_half n
  have hx : ((boardHalf (n+1) : Int)+0).toNat=2*squareSize n := by omega
  simp only [boardAtRelative,hx]
  exact redBoard_center_seed n v hv

theorem relative_center_left (k v : Nat) (hv : v<4) (r : Int)
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<0) :
    (boardAtRelative (k+1) v r 0).val ∈ leftInitialBases := by
  have hh := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hx : 0<((boardHalf (k+2) : Int)+r).toNat ∧
      ((boardHalf (k+2) : Int)+r).toNat<2*squareSize (k+1) := by omega
  have hy : ((boardHalf (k+2) : Int)+0).toNat=2*squareSize (k+1) := by omega
  simp only [boardAtRelative,hn,hy]
  exact center_row_left k v _ hv hx

theorem relative_center_right (k v : Nat) (hv : v<4) (r : Int)
    (hr : 0<r ∧ r<(boardHalf (k+2) : Int)) :
    (boardAtRelative (k+1) v r 0).val ∈ rightInitialBases := by
  have hh := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hx : 2*squareSize (k+1)<((boardHalf (k+2) : Int)+r).toNat ∧
      ((boardHalf (k+2) : Int)+r).toNat<4*squareSize (k+1) := by omega
  have hy : ((boardHalf (k+2) : Int)+0).toNat=2*squareSize (k+1) := by omega
  simp only [boardAtRelative,hn,hy]
  exact center_row_right k v _ hv hx

theorem relative_left_midpoint (n v : Nat) (hv : v<4) :
    (boardAtRelative n v (-(boardHalf (n+1) : Int)) 0).val ∈ [47,49,50,52] := by
  have hh := fullBoard_half n
  have hx : ((boardHalf (n+1) : Int)+(-(boardHalf (n+1) : Int))).toNat=0 := by omega
  have hy : ((boardHalf (n+1) : Int)+0).toNat=2*squareSize n := by omega
  simp only [boardAtRelative,hx,hy]
  exact (left_midpoint_iff n v _ hv (by omega)).mpr rfl

theorem relative_right_midpoint (n v : Nat) (hv : v<4) :
    (boardAtRelative n v (boardHalf (n+1)) 0).val ∈ [35,36,37,38] := by
  have hh := fullBoard_half n
  have hx : ((boardHalf (n+1) : Int)+(boardHalf (n+1) : Int)).toNat=4*squareSize n := by omega
  have hy : ((boardHalf (n+1) : Int)+0).toNat=2*squareSize n := by omega
  simp only [boardAtRelative,hx,hy]
  exact (right_midpoint_iff n v _ hv (by omega)).mpr rfl

theorem relative_upper_side (k side v : Nat) (hside : side<4) (hv : v<4) (s : Int)
    (hs : 0<s ∧ s<(boardHalf (k+2) : Int)) (hm : s%4=1) :
    (relativeSide (k+1) v side s).val=channelExpected side 3 := by
  have hh := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hx : 2*squareSize (k+1)<((boardHalf (k+2) : Int)+s).toNat ∧
      ((boardHalf (k+2) : Int)+s).toNat<4*squareSize (k+1) := by omega
  have hmod : ((boardHalf (k+2) : Int)+s).toNat%4=1 := by
    have hH := active_half_mod_four (k+1) (by omega)
    rw [hn] at hH
    omega
  rw [relativeSide_eq (k+1) v side hside s]
  exact side_upper_channel (k+1) side v _ (by omega) hside hv hx hmod

#print axioms relative_exposed_seed
#print axioms relative_exposed_left_midpoint
#print axioms relative_center_left
end K230Verification
