module
public import ActualChannels
public import CenteredFullBoard
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem fullBoard_centered_channel_presence (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1)) :
    ((indexedFullTile (T (centerCell b (n+1) r s))).e.2.1≠0 ↔ s%4=1) ∧
    ((indexedFullTile (T (centerCell b (n+1) r s))).w.2.1≠0 ↔ s%4=1) ∧
    ((indexedFullTile (T (centerCell b (n+1) r s))).n.2.1≠0 ↔ r%4=1) ∧
    ((indexedFullTile (T (centerCell b (n+1) r s))).s.2.1≠0 ↔ r%4=1) := by
  have hH := fullBoard_half n
  obtain ⟨d,hd⟩ := four_dvd_squareSize n hn
  have hx : ((boardHalf (n+1):Int)+r).toNat≤4*squareSize n := by omega
  have hy : ((boardHalf (n+1):Int)+s).toNat≤4*squareSize n := by omega
  have hxmod : ((boardHalf (n+1):Int)+r).toNat%4=1 ↔ r%4=1 := by omega
  have hymod : ((boardHalf (n+1):Int)+s).toNat%4=1 ↔ s%4=1 := by omega
  rw [centerCell_nat b (n+1) r s hr.1 hs.1]
  have h := full_board_channel_pattern T n v b hn hb
    ((boardHalf (n+1):Int)+r).toNat ((boardHalf (n+1):Int)+s).toNat hx hy
  simpa only [hxmod,hymod] using h

theorem centered_vcode_absent (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1)) (hmod : r%4≠1) :
    vCode T (centerCell b (n+1) r s)=0 := by
  have h := (fullBoard_centered_channel_presence T n v b hn hb r s hr hs).2.2.1
  by_contra hne
  exact hmod (h.mp hne)

theorem centered_hcode_absent (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1)) (hmod : s%4≠1) :
    hCode T (centerCell b (n+1) r s)=0 := by
  have h := (fullBoard_centered_channel_presence T n v b hn hb r s hr hs).1
  by_contra hne
  exact hmod (h.mp hne)

#print axioms fullBoard_centered_channel_presence
end K230Verification
