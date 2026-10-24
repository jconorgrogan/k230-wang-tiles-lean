module
public import ChannelRouting
public import ActualBoardGeometry
public section
namespace K230Verification

noncomputable def actualInitialLine (T : Cell → Fin 11487) (hT : FullValid T)
    (k v : Nat) (b : Cell) (hv : v<4) (hb : FullBoardAt T (k+1) v b)
    (R : BoardTraces T b k) : InitialLine k where
  tile := fun r => centerTM T b (k+2) r 0
  group := fun r => centerGroup T b (k+2) r 0
  groupMem := fun r => centerGroup_mem T b (k+2) r 0
  tmMem := fun r => centerTM_mem T b (k+2) r 0
  matchH := fun r => centerTM_horizontal T hT b (k+2) r 0
  seed := centerTM_seed T k v b hv hb
  leftClass := fun r hl hr => actual_initial_left_class T k v b hv hb r hl hr
  rightClass := fun r hl hr => actual_initial_right_class T k v b hv hb r hl hr
  channel := fun _ hl hr => R.initial_channel hb ⟨hl,hr⟩
  tapeChannel := by
    intro r hr
    have hp := board_half_pos (k+2)
    exact R.v_zero hr ⟨by omega,by omega⟩

/-- Actual full-plane tiles on an occurring canonical board instantiate all
    physical routing clauses. Only the two exact channel trace theorems are
    supplied; seed, transmitter, computation and absorbing boundaries are
    derived here from the concrete indexed tile set. -/
noncomputable def actualRoutedBoard (T : Cell → Fin 11487) (hT : FullValid T)
    (k v : Nat) (b : Cell) (hv : v<4) (hb : FullBoardAt T (k+1) v b)
    (R : BoardTraces T b k) : RoutedBoard k where
  tile := centerTM T b (k+2)
  matchH := centerTM_horizontal T hT b (k+2)
  matchV := centerTM_vertical T hT b (k+2)
  initial := fun _ hi => (actualInitialLine T hT k v b hv hb R).logical_initial hi
  columnCopy := by
    intro t ht i hi y hyl hyr hdata
    have hrow := physicalRow_mem ht
    have hp := board_half_pos (k+2)
    have hnonneg := timeY_nonneg (show t≤2^k by omega)
    have hy : -(boardHalf (k+2) : Int)<y ∧ y<boardHalf (k+2) := by
      constructor <;> have := hrow.1.2.1 <;> omega
    exact R.column_copy hv hb (physicalColumn_mem hi) hy (physical_row_gap_not_free ht hyl hyr) hdata
  rowCopy := by
    intro t ht i hi hj x hxl hxr
    have hl := physicalColumn_mem hi
    have hr := physicalColumn_mem hj
    have hx : -(boardHalf (k+2) : Int)<x ∧ x<boardHalf (k+2) := by
      constructor
      · have := hl.1; omega
      · have := hr.2.1; omega
    have hs := physicalRow_mem ht
    exact R.row_copy hv hb hx hs.1 (by have := hs.2; omega)
      (physical_column_gap_not_free hi hj hxl hxr)
  computation := by
    intro t ht i hi hdata
    exact R.computation (physicalColumn_mem hi) (physicalRow_mem ht).1 hdata
  left := by
    intro t ht i hi he
    subst i
    have hc := physicalColumn_mem hi
    have hs := physicalRow_mem ht
    have hw := horizontal_wire (tile:=fun x => centerTM T b (k+2) x (physicalRow k t ht))
      (a:= -(boardHalf (k+2) : Int)) (b:=physicalColumn k (-(2^k : Nat)) hi) hc.1
      (fun x _ _ => centerTM_horizontal T hT b (k+2) x (physicalRow k t ht))
      (by
        intro x hxl hxr
        have hx : -(boardHalf (k+2) : Int)<x ∧ x<boardHalf (k+2) := by
          constructor
          · exact hxl
          · have := hc.2.1; omega
        exact R.row_copy hv hb hx hs.1 (by have := hs.2; omega)
          (physical_column_left_not_free hi hxr))
    exact hw.trans (actual_left_wall_blank T k v b hv hb hs.1 hs.2)
  right := by
    intro t ht i hi he
    subst i
    have hc := physicalColumn_mem hi
    have hs := physicalRow_mem ht
    have hw := horizontal_wire (tile:=fun x => centerTM T b (k+2) x (physicalRow k t ht))
      (a:=physicalColumn k ((2^k : Nat)-1) hi) (b:=(boardHalf (k+2) : Int)) hc.2.1
      (fun x _ _ => centerTM_horizontal T hT b (k+2) x (physicalRow k t ht))
      (by
        intro x hxl hxr
        have hx : -(boardHalf (k+2) : Int)<x ∧ x<boardHalf (k+2) := by
          constructor
          · have := hc.1; omega
          · exact hxr
        exact R.row_copy hv hb hx hs.1 (by have := hs.2; omega)
          (physical_column_right_not_free hi hxl))
    rw [←hw]
    exact actual_right_wall_direction T k v b hv hb hs.1 hs.2

noncomputable def actualFiniteBoard (T : Cell → Fin 11487) (hT : FullValid T)
    (k v : Nat) (b : Cell) (hv : v<4) (hb : FullBoardAt T (k+1) v b)
    (R : BoardTraces T b k) : FiniteBoard k230Machine (2^k) :=
  (actualRoutedBoard T hT k v b hv hb R).toFiniteBoard

#print axioms actualInitialLine
#print axioms actualRoutedBoard
#print axioms actualFiniteBoard
end K230Verification
