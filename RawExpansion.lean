module
public import ConcreteExpansion
public section
namespace K230Concrete

@[expose] def rawExpanded : Nat → Nat → Nat → Nat → Nat
  | 0,k,_,_ => k
  | n+1,k,x,y => Wang156.sigma (rawExpanded n k (x/2) (y/2)) (x%2+2*(y%2))

theorem expanded_value (n : Nat) (k : Fin 156) (x y : Nat) :
    (expanded n k x y).val = rawExpanded n k.val x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [expanded,child,rawExpanded,ih]

end K230Concrete
