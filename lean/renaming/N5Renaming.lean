import Renaming

namespace FiniteCongruenceChecks.N5Renaming
open Renaming

def forward (x : V) : V :=
  match x.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0
def backward (x : V) : V :=
  match x.val with | 0 => 3 | 1 => 0 | 2 => 1 | _ => 2
def labels : Bijection := ⟨forward, backward, by decide, by decide⟩

-- Source rule 0 is target rule 1, and source rule 1 is target rule 0.
def op1 : V → V := operation labels N5.op2
def op2 : V → V := operation labels N5.op1
def theta (a : Fin 5) : V → V → Prop :=
  Renaming.relation labels (fun x y => N5.theta a x y = true)

theorem transferred_congruence (r : V → V → Prop) :
    IsPropCongruence N5.op1 N5.op2 r ↔
      IsPropCongruence op1 op2 (Renaming.relation labels r) :=
  (congruence_iff labels N5.op1 N5.op2 r).trans (swap_rules _ _ _)

/-- Complete classification obtained from the existing source theorem. -/
theorem all_relations (r : V → V → Prop) :
    IsPropCongruence op1 op2 r ↔ ∃ a : Fin 5, ∀ x y, r x y ↔ theta a x y := by
  let q := Renaming.relation (inverse labels) r
  have hround : Renaming.relation labels q = r := round_trip labels r
  have hc : IsPropCongruence op1 op2 r ↔ IsPropCongruence N5.op1 N5.op2 q := by
    rw [← hround]
    exact (transferred_congruence q).symm
  rw [hc, N5.all_relations q]
  constructor
  · rintro ⟨a, h⟩
    refine ⟨a, ?_⟩
    intro x y
    simpa only [q, Renaming.relation, inverse, labels.right_inverse, theta] using
      h (labels.backward x) (labels.backward y)
  · rintro ⟨a, h⟩
    refine ⟨a, ?_⟩
    intro x y
    simpa only [q, Renaming.relation, inverse, labels.left_inverse, theta] using
      h (labels.forward x) (labels.forward y)

theorem order_exact (a b : Fin 5) :
    N5.le a b = true ↔ (∀ x y, theta a x y → theta b x y) :=
  (N5.order_exact a b).trans (inclusion_iff labels _ _)

theorem theta_injective (a b : Fin 5)
    (h : ∀ x y, theta a x y ↔ theta b x y) : a = b := by
  apply N5.theta_injective a b
  intro x y
  have hh : N5.theta a x y = true ↔ N5.theta b x y = true := by
    simpa only [theta, Renaming.relation, labels.left_inverse] using
      h (labels.forward x) (labels.forward y)
  cases ha : N5.theta a x y <;> cases hb : N5.theta b x y <;> simp_all

end FiniteCongruenceChecks.N5Renaming
