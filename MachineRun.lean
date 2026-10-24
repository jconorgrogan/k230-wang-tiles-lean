module
public import RowSimulation

public section
namespace K230Verification
structure Configuration where
  state : Nat
  position : Int
  tape : Int → Bool

def Configuration.after (c : Configuration) (q : Nat) (b : Bool) (d : Dir) : Configuration where
  state := q
  position := if d = .right then c.position+1 else c.position-1
  tape := fun i => if i = c.position then b else c.tape i

def Configuration.row (c : Configuration) : Int → VLabel := configRow c.tape c.position c.state

def machineStep (M : Machine) (c : Configuration) : Option Configuration :=
  (M c.state (c.tape c.position)).map fun (q,b,d) => c.after q b d

def machineRun (M : Machine) (c : Configuration) : Nat → Option Configuration
  | 0 => some c
  | n+1 => (machineRun M c n).bind (machineStep M)

/-- Standard nonhalting: every finite iterate from the initial configuration
    remains defined. Missing transitions are halting. -/
def NeverHalts (M : Machine) (c : Configuration) : Prop :=
  ∀ n, ∃ d, machineRun M c n = some d

theorem after_right_row (c : Configuration) (q : Nat) (b : Bool) :
    (c.after q b .right).row = fun i => if i = c.position then .symbol b else
      if i = c.position+1 then .head q (c.tape i) else .symbol (c.tape i) := by
  funext i
  simp only [Configuration.row, Configuration.after, configRow]
  by_cases hi : i = c.position
  · simp [hi]
    omega
  · simp [hi]

theorem after_left_row (c : Configuration) (q : Nat) (b : Bool) :
    (c.after q b .left).row = fun i => if i = c.position then .symbol b else
      if i = c.position-1 then .head q (c.tape i) else .symbol (c.tape i) := by
  funext i
  simp only [Configuration.row, Configuration.after, configRow]
  by_cases hi : i = c.position
  · simp [hi]
    omega
  · simp [hi]

/-- One-step row soundness returns the genuine deterministic configuration. -/
theorem row_step_sound {M : Machine} {c : Configuration} {north : Int → VLabel} {edge}
    (hr : RowAllowed M north c.row edge) :
    ∃ d, machineStep M c = some d ∧ north = d.row := by
  have atHead := hr c.position
  change Allowed M _ _ (configRow c.tape c.position c.state c.position) _ at atHead
  simp only [configRow, ite_true] at atHead
  obtain ⟨⟨q,b,dir⟩,step⟩ := head_requires_transition atHead
  refine ⟨c.after q b dir, by simp [machineStep,step], ?_⟩
  have hs : ∀ i, c.row i = if i = c.position then .head c.state (c.tape i) else .symbol (c.tape i) := fun _ => rfl
  cases dir with
  | right =>
    rw [after_right_row]
    funext i
    exact row_right c.tape c.position c.state q b hr hs step i
  | left =>
    rw [after_left_row]
    funext i
    exact row_left c.tape c.position c.state q b hr hs step i

theorem row_step_complete {M : Machine} {c d : Configuration}
    (hstep : machineStep M c = some d) :
    ∃ edge, RowAllowed M d.row c.row edge := by
  cases hm : M c.state (c.tape c.position) with
  | none => simp [machineStep,hm] at hstep
  | some z =>
    rcases z with ⟨q,b,dir⟩
    have hex : ∃ north edge, RowAllowed M north c.row edge := by
      cases dir with
      | right => exact row_exists_right c.tape c.position c.state q b hm
      | left => exact row_exists_left c.tape c.position c.state q b hm
    obtain ⟨north,edge,hr⟩ := hex
    obtain ⟨d',hd',hn⟩ := row_step_sound hr
    have eq : d' = d := Option.some.inj (hd'.symm.trans hstep)
    subst d'
    rw [hn] at hr
    exact ⟨edge,hr⟩

/-- Full unbounded space-time diagram with the prescribed initial row. -/
def SpaceTime (M : Machine) (c : Configuration) : Prop :=
  ∃ vertical : Nat → Int → VLabel, ∃ edge : Nat → Int → HLabel,
    vertical 0 = c.row ∧ ∀ n, RowAllowed M (vertical (n+1)) (vertical n) (edge n)

/-- The complete row compiler simulation theorem, with ordinary finite-iterate
    nonhalting as the target, not a custom surrogate for nonhalting. -/
theorem spaceTime_iff_neverHalts {M : Machine} {c : Configuration} :
    SpaceTime M c ↔ NeverHalts M c := by
  classical
  constructor
  · rintro ⟨vertical,edge,hzero,hr⟩
    have all : ∀ n, ∃ d, machineRun M c n = some d ∧ vertical n = d.row := by
      intro n
      induction n with
      | zero => exact ⟨c,rfl,hzero⟩
      | succ n ih =>
        obtain ⟨d,hd,hv⟩ := ih
        have hrow := hr n
        rw [hv] at hrow
        obtain ⟨d',hnext,hv'⟩ := row_step_sound hrow
        refine ⟨d',?_,hv'⟩
        simp [machineRun,hd,hnext]
    intro n
    obtain ⟨d,hd,_⟩ := all n
    exact ⟨d,hd⟩
  · intro h
    let config : Nat → Configuration := fun n => Classical.choose (h n)
    have hconfig : ∀ n, machineRun M c n = some (config n) := fun n => Classical.choose_spec (h n)
    have hzero : config 0 = c := by
      have h0 := hconfig 0
      exact (Option.some.inj h0).symm
    have hnext : ∀ n, machineStep M (config n) = some (config (n+1)) := by
      intro n
      have hn := hconfig (n+1)
      simpa [machineRun,hconfig n] using hn
    have hedge : ∀ n, ∃ e, RowAllowed M (config (n+1)).row (config n).row e :=
      fun n => row_step_complete (hnext n)
    refine ⟨(fun n => (config n).row), (fun n => Classical.choose (hedge n)), ?_, ?_⟩
    · exact congrArg Configuration.row hzero
    · intro n
      exact Classical.choose_spec (hedge n)

#print axioms spaceTime_iff_neverHalts
#print axioms row_step_sound
end K230Verification
