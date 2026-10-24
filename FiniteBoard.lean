module
public import MachineRun
public import FiniteWindow
public section
namespace K230Verification

@[expose] def InTape (H : Nat) (i : Int) : Prop := -(H : Int) ≤ i ∧ i < (H : Int)
instance (H : Nat) (i : Int) : Decidable (InTape H i) := by unfold InTape; infer_instance

@[expose] def extendEdge (H : Nat) (edge : Int → HLabel) (i : Int) : HLabel :=
  if InTape H i then edge i else none
@[expose] def extendNorth (H : Nat) (north : Int → VLabel) (tape : Int → Bool)
    (edge : Int → HLabel) (i : Int) : VLabel :=
  if InTape H i then north i else
  if i=(H : Int) then
    match edge ((H : Int)-1) with
    | some (.right,q) => .head q (tape i)
    | _ => .symbol (tape i)
  else .symbol (tape i)

/-- A finite compressed board row can be extended to a genuine unbounded row.
    A possible outgoing right move gets its missing merge immediately outside
    the board. No artificial left move or entered state is introduced. -/
theorem finite_row_extend {M : Machine} {H : Nat} {c : Configuration}
    {north : Int → VLabel} {edge : Int → HLabel}
    (hH : 0<H) (hp : InTape H c.position)
    (hr : ∀ i, InTape H i → Allowed M (north i) (edge i) (c.row i) (edge (i-1)))
    (hl : edge (-(H : Int)-1)=none)
    (hrr : edge ((H : Int)-1)=none ∨ ∃ q, edge ((H : Int)-1)=some (.right,q)) :
    RowAllowed M (extendNorth H north c.tape edge) c.row (extendEdge H edge) := by
  intro i
  by_cases hi : InTape H i
  · have ht := hr i hi
    by_cases him : InTape H (i-1)
    · simpa [extendNorth,extendEdge,hi,him] using ht
    · have he : i-1=-(H : Int)-1 := by unfold InTape at *; omega
      simpa [extendNorth,extendEdge,hi,him,he,hl] using ht
  · have hne : i≠c.position := by intro h; subst i; exact hi hp
    have hsym : c.row i = .symbol (c.tape i) := by
      simp [Configuration.row,configRow,hne]
    by_cases he : i=(H : Int)
    · subst i
      have him : InTape H ((H : Int)-1) := by unfold InTape; omega
      rcases hrr with hnone | ⟨q,hq⟩
      · simpa [extendNorth,extendEdge,hi,him,hnone,hsym] using Allowed.symbol (M:=M) (c.tape (H : Int))
      · have hlast : InTape H ((H : Int)-1) := by unfold InTape; omega
        have ht := hr ((H : Int)-1) hlast
        rw [hq] at ht
        obtain ⟨p,a,b,_,_,step,_⟩ := right_emitter ht
        have entered : ∃ p a b, M p a=some (q,b,.right) := ⟨p,a,b,step⟩
        simpa [extendNorth,extendEdge,hi,him,hq,hsym] using Allowed.mergeRight q (c.tape (H : Int)) entered
    · have him : ¬ InTape H (i-1) := by unfold InTape at *; omega
      simpa [extendNorth,extendEdge,hi,him,he,hsym] using Allowed.symbol (M:=M) (c.tape i)

@[expose] def blankConfiguration : Configuration := ⟨0,0,fun _ => false⟩

/-- The precise interface exported by a complete decorated canonical board:
    H computation rows, 2H tape columns, and an outgoing-only right edge. -/
structure FiniteBoard (M : Machine) (H : Nat) where
  vertical : Nat → Int → VLabel
  edge : Nat → Int → HLabel
  initial : ∀ i, InTape H i → vertical 0 i=blankConfiguration.row i
  allowed : ∀ t, t<H → ∀ i, InTape H i →
    Allowed M (vertical (t+1) i) (edge t i) (vertical t i) (edge t (i-1))
  left : ∀ t, t<H → edge t (-(H : Int)-1)=none
  right : ∀ t, t<H → edge t ((H : Int)-1)=none ∨
    ∃ q, edge t ((H : Int)-1)=some (.right,q)

theorem machineStep_position_unit {M : Machine} {c d : Configuration}
    (hs : machineStep M c=some d) :
    d.position=c.position+1 ∨ d.position=c.position-1 := by
  cases he : M c.state (c.tape c.position) with
  | none => simp [machineStep,he] at hs
  | some z =>
    rcases z with ⟨q,b,dir⟩
    have hd : c.after q b dir=d := by simpa [machineStep,he] using hs
    subst d
    cases dir <;> simp [Configuration.after]

/-- All finite board rows are genuine consecutive configurations. The final
    right exit is completed outside the board in the SAME row, so H board
    rows prove exactly H surviving transitions, not H-1. -/
theorem finiteBoard_prefix {M : Machine} {H : Nat} (B : FiniteBoard M H) (hH : 0<H) :
    ∀ t, t≤H → ∃ c, machineRun M blankConfiguration t=some c ∧
      (∀ i, InTape H i → B.vertical t i=c.row i) ∧
      -(t : Int)≤c.position ∧ c.position≤(t : Int) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨blankConfiguration,rfl,B.initial,by simp [blankConfiguration],by simp [blankConfiguration]⟩
  | succ t ih =>
    intro ht
    obtain ⟨c,hc,hrow,hlo,hhi⟩ := ih (by omega)
    have htH : t<H := by omega
    have hp : InTape H c.position := by unfold InTape; omega
    have hlocal : ∀ i, InTape H i →
        Allowed M (B.vertical (t+1) i) (B.edge t i) (c.row i) (B.edge t (i-1)) := by
      intro i hi
      have ha := B.allowed t htH i hi
      rw [hrow i hi] at ha
      exact ha
    have hext := finite_row_extend hH hp hlocal (B.left t htH) (B.right t htH)
    obtain ⟨d,hd,hn⟩ := row_step_sound hext
    refine ⟨d,?_,?_,?_,?_⟩
    · simp [machineRun,hc,hd]
    · intro i hi
      have he := congrArg (fun f : Int → VLabel => f i) hn
      simpa [extendNorth,hi] using he
    · have hu := machineStep_position_unit hd
      rcases hu with hu|hu <;> omega
    · have hu := machineStep_position_unit hd
      rcases hu with hu|hu <;> omega

theorem finiteBoard_survives {M : Machine} {H : Nat} (B : FiniteBoard M H) (hH : 0<H) :
    ∃ c, machineRun M blankConfiguration H=some c := by
  obtain ⟨c,hc,_⟩ := finiteBoard_prefix B hH H (Nat.le_refl H)
  exact ⟨c,hc⟩

/-- Restricting a true row whose head has not reached the left edge produces
    exactly the permitted finite-board boundary conditions. -/
theorem row_outgoing_boundaries {M : Machine} {H : Nat} {c : Configuration}
    {north : Int → VLabel} {edge : Int → HLabel}
    (hr : RowAllowed M north c.row edge)
    (hpL : -(H : Int)<c.position) (hpR : c.position<(H : Int)) :
    edge (-(H : Int)-1)=none ∧
    (edge ((H : Int)-1)=none ∨ ∃ q, edge ((H : Int)-1)=some (.right,q)) := by
  have nohead : ∀ i, i≠c.position → ∀ q a, c.row i≠.head q a := by
    intro i hi q a
    simp [Configuration.row,configRow,hi]
  constructor
  · cases he : edge (-(H : Int)-1) with
    | none => rfl
    | some z =>
      rcases z with ⟨dir,q⟩
      cases dir with
      | right =>
        have ht := hr (-(H : Int)-1)
        rw [he] at ht
        obtain ⟨p,a,b,hhead,_,_,_⟩ := right_emitter ht
        exact False.elim (nohead _ (by omega) p a hhead)
      | left =>
        have ht := hr (-(H : Int))
        rw [he] at ht
        obtain ⟨p,a,b,hhead,_,_,_⟩ := left_emitter ht
        exact False.elim (nohead _ (by omega) p a hhead)
  · cases he : edge ((H : Int)-1) with
    | none => exact Or.inl rfl
    | some z =>
      rcases z with ⟨dir,q⟩
      cases dir with
      | right => exact Or.inr ⟨q,rfl⟩
      | left =>
        have ht := hr (H : Int)
        rw [he] at ht
        obtain ⟨p,a,b,hhead,_,_,_⟩ := left_emitter ht
        exact False.elim (nohead _ (by omega) p a hhead)

theorem neverHalts_finiteBoard {M : Machine} (h : NeverHalts M blankConfiguration) (H : Nat) :
    Nonempty (FiniteBoard M H) := by
  classical
  let config : Nat → Configuration := fun t => Classical.choose (h t)
  have hconfig : ∀ t, machineRun M blankConfiguration t=some (config t) :=
    fun t => Classical.choose_spec (h t)
  have hzero : config 0=blankConfiguration := by
    exact (Option.some.inj (hconfig 0)).symm
  have hstep : ∀ t, machineStep M (config t)=some (config (t+1)) := by
    intro t
    have hn := hconfig (t+1)
    simpa [machineRun,hconfig t] using hn
  have hbounds : ∀ t : Nat, -(t : Int)≤(config t).position ∧ (config t).position≤(t : Int) := by
    intro t
    induction t with
    | zero => simp [hzero,blankConfiguration]
    | succ t ih =>
      have hu := machineStep_position_unit (hstep t)
      rcases hu with hu|hu <;> constructor <;> omega
  have hedge : ∀ t, ∃ e, RowAllowed M (config (t+1)).row (config t).row e :=
    fun t => row_step_complete (hstep t)
  let edge : Nat → Int → HLabel := fun t => Classical.choose (hedge t)
  have hrow : ∀ t, RowAllowed M (config (t+1)).row (config t).row (edge t) :=
    fun t => Classical.choose_spec (hedge t)
  refine ⟨{ vertical := (fun t => (config t).row)
            edge := edge
            initial := ?_
            allowed := ?_
            left := ?_
            right := ?_ }⟩
  · intro i _; rw [hzero]
  · intro t _ i _; exact hrow t i
  · intro t ht
    have hb := hbounds t
    exact (row_outgoing_boundaries (hrow t) (by omega) (by omega)).1
  · intro t ht
    have hb := hbounds t
    exact (row_outgoing_boundaries (hrow t) (by omega) (by omega)).2

theorem nat_le_two_pow (t : Nat) : t≤2^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hp : 0<2^t := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

/-- The geometric construction supplies exactly the cofinal powers-of-two
    capacities. That suffices for ordinary nonhalting, with no infinite-board
    or coherent decoration assumption. -/
theorem cofinal_finiteBoards_iff_neverHalts {M : Machine} :
    (∀ k : Nat, Nonempty (FiniteBoard M (2^k))) ↔ NeverHalts M blankConfiguration := by
  constructor
  · intro h t
    obtain ⟨B⟩ := h t
    obtain ⟨c,hc,_⟩ := finiteBoard_prefix B (Nat.pow_pos (by decide)) t (nat_le_two_pow t)
    exact ⟨c,hc⟩
  · intro h k
    exact neverHalts_finiteBoard h (2^k)

#print axioms finite_row_extend
#print axioms finiteBoard_survives
#print axioms neverHalts_finiteBoard
#print axioms cofinal_finiteBoards_iff_neverHalts
end K230Verification
