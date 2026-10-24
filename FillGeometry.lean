module
public import ChildPatchContract
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

@[expose] noncomputable def rootOwner (n : Nat) (p : Cell) : Option RedSquare :=
  childOwner (n+1) (p.1-2*squareSize n,p.2-2*squareSize n)

@[expose] def WithinChild (n : Nat) (b : RedSquare) (p : Cell) : Prop :=
  (lowerOriginX n b:Int)≤p.1 ∧ p.1≤lowerOriginX n b+2*boardHalf b.level ∧
  (lowerOriginY n b:Int)≤p.2 ∧ p.2≤lowerOriginY n b+2*boardHalf b.level

theorem rootOwner_bounds {n : Nat} {p : Cell} {b : RedSquare}
    (h : rootOwner n p=some b) : LowerSquareInside (n+1) b ∧ WithinChild n b p := by
  have hb := childOwner_spec h
  have hl := lower_origins n b hb.1
  have hh := boardHalf_index n
  have hx1 := hb.2.1.1.1
  have hx2 := hb.2.1.1.2
  have hy1 := hb.2.1.2.1
  have hy2 := hb.2.1.2.2
  refine ⟨hb.1,?_⟩
  unfold WithinChild
  omega

theorem rootOwner_interior {n : Nat} {p : Cell} {b : RedSquare}
    (h : rootOwner n p=some b) :
    0<p.1 ∧ p.1<4*squareSize n ∧ 0<p.2 ∧ p.2<4*squareSize n := by
  have hb := rootOwner_bounds h
  have hl := lower_origins n b hb.1
  have hh := boardHalf_index n
  unfold WithinChild at hb
  omega

theorem rootOwner_boundary {n : Nat} {p : Cell}
    (h : p.1=0 ∨ p.1=4*squareSize n ∨ p.2=0 ∨ p.2=4*squareSize n) : rootOwner n p=none := by
  cases he : rootOwner n p with
  | none => rfl
  | some b =>
    have hi := rootOwner_interior he
    rcases h with h|h|h|h <;> omega

theorem rootOwner_neighbors {n : Nat} {p q : Cell} {a b : RedSquare}
    (ha : rootOwner n p=some a) (hb : rootOwner n q=some b)
    (hx : -1≤p.1-q.1 ∧ p.1-q.1≤1) (hy : -1≤p.2-q.2 ∧ p.2-q.2≤1) : a=b := by
  exact childOwner_neighbors ha hb (by omega) (by omega)

theorem rootOwner_left_seam {n : Nat} {x y : Int} {b : RedSquare}
    (ha : rootOwner n (x,y)=none) (hb : rootOwner n (x+1,y)=some b) :
    x+1=(lowerOriginX n b:Int) := by
  have hl := lower_origins n b (rootOwner_bounds hb).1
  have hh := boardHalf_index n
  have hc : childOwner (n+1) (x-2*squareSize n+1,y-2*squareSize n)=some b := by
    have he : x-2*(squareSize n:Int)+1=x+1-2*squareSize n := by omega
    simpa only [rootOwner,he] using hb
  have h := childOwner_horizontal_entry ha hc
  omega

theorem rootOwner_right_seam {n : Nat} {x y : Int} {b : RedSquare}
    (ha : rootOwner n (x,y)=some b) (hb : rootOwner n (x+1,y)=none) :
    x=(lowerOriginX n b:Int)+2*boardHalf b.level := by
  have hl := lower_origins n b (rootOwner_bounds ha).1
  have hh := boardHalf_index n
  have hc : childOwner (n+1) (x-2*squareSize n+1,y-2*squareSize n)=none := by
    have he : x-2*(squareSize n:Int)+1=x+1-2*squareSize n := by omega
    simpa only [rootOwner,he] using hb
  have h := childOwner_horizontal_exit ha hc
  omega

theorem rootOwner_bottom_seam {n : Nat} {x y : Int} {b : RedSquare}
    (ha : rootOwner n (x,y)=none) (hb : rootOwner n (x,y+1)=some b) :
    y+1=(lowerOriginY n b:Int) := by
  have hl := lower_origins n b (rootOwner_bounds hb).1
  have hh := boardHalf_index n
  have hc : childOwner (n+1) (x-2*squareSize n,y-2*squareSize n+1)=some b := by
    have he : y-2*(squareSize n:Int)+1=y+1-2*squareSize n := by omega
    simpa only [rootOwner,he] using hb
  have h := childOwner_vertical_entry ha hc
  omega

theorem rootOwner_top_seam {n : Nat} {x y : Int} {b : RedSquare}
    (ha : rootOwner n (x,y)=some b) (hb : rootOwner n (x,y+1)=none) :
    y=(lowerOriginY n b:Int)+2*boardHalf b.level := by
  have hl := lower_origins n b (rootOwner_bounds ha).1
  have hh := boardHalf_index n
  have hc : childOwner (n+1) (x-2*squareSize n,y-2*squareSize n+1)=none := by
    have he : y-2*(squareSize n:Int)+1=y+1-2*squareSize n := by omega
    simpa only [rootOwner,he] using hb
  have h := childOwner_vertical_exit ha hc
  omega

end K230Verification
