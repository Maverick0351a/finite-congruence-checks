import Std

/-!
# Concrete congruence representations on four points

This file uses Lean kernel reduction (`decide`), never `native_decide`.
The exhaustive domain is the 64 symmetric reflexive Boolean relations on four
points. `relation_complete` proves that this covers every equivalence relation,
so the classification is of ALL congruences of the displayed two-operation
algebra. The data below comes from the saved N5/B3 certificates.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FiniteCongruenceChecks

abbrev V := Fin 4
abbrev Rel := V → V → Bool
abbrev Shape := Bool × Bool × Bool × Bool × Bool × Bool

def relation (s : Shape) (x y : V) : Bool :=
  match x.val, y.val with
  | 0, 1 | 1, 0 => s.1
  | 0, 2 | 2, 0 => s.2.1
  | 0, 3 | 3, 0 => s.2.2.1
  | 1, 2 | 2, 1 => s.2.2.2.1
  | 1, 3 | 3, 1 => s.2.2.2.2.1
  | 2, 3 | 3, 2 => s.2.2.2.2.2
  | _, _ => true

def shape (r : Rel) : Shape :=
  (r 0 1, r 0 2, r 0 3, r 1 2, r 1 3, r 2 3)

def IsEquivalence (r : Rel) : Prop :=
  (∀ x, r x x = true) ∧
  (∀ x y, r x y = r y x) ∧
  (∀ x y z, r x y = true → r y z = true → r x z = true)

def Preserves (f : V → V) (r : Rel) : Prop :=
  ∀ x y, r x y = true → r (f x) (f y) = true

def IsCongruence (f g : V → V) (r : Rel) : Prop :=
  IsEquivalence r ∧ Preserves f r ∧ Preserves g r

def Same (r s : Rel) : Prop := ∀ x y, r x y = s x y
def Included (r s : Rel) : Prop := ∀ x y, r x y = true → s x y = true

instance (r : Rel) : Decidable (IsEquivalence r) := inferInstanceAs
  (Decidable ((∀ x, r x x = true) ∧ (∀ x y, r x y = r y x) ∧
    (∀ x y z, r x y = true → r y z = true → r x z = true)))
instance (f : V → V) (r : Rel) : Decidable (Preserves f r) := inferInstanceAs
  (Decidable (∀ x y, r x y = true → r (f x) (f y) = true))
instance (f g : V → V) (r : Rel) : Decidable (IsCongruence f g r) := inferInstanceAs
  (Decidable (IsEquivalence r ∧ Preserves f r ∧ Preserves g r))
instance (r s : Rel) : Decidable (Same r s) := inferInstanceAs
  (Decidable (∀ x y, r x y = s x y))
instance (r s : Rel) : Decidable (Included r s) := inferInstanceAs
  (Decidable (∀ x y, r x y = true → s x y = true))

theorem fin4_cases : ∀ x : V, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide

theorem relation_complete (r : Rel) (h : IsEquivalence r) :
    r = relation (shape r) := by
  funext x y
  rcases fin4_cases x with rfl | rfl | rfl | rfl
  all_goals rcases fin4_cases y with rfl | rfl | rfl | rfl
  all_goals simp only [relation, shape]
  all_goals first | rfl | exact h.1 _ | exact h.2.1 _ _

def IsPropCongruence (f g : V → V) (r : V → V → Prop) : Prop :=
  Equivalence r ∧
  (∀ x y, r x y → r (f x) (f y)) ∧
  (∀ x y, r x y → r (g x) (g y))

def encode (r : V → V → Prop) [DecidableRel r] : Rel := fun x y => decide (r x y)

theorem encode_congruence (f g : V → V) (r : V → V → Prop) [DecidableRel r] :
    IsCongruence f g (encode r) ↔ IsPropCongruence f g r := by
  constructor
  · rintro ⟨⟨hr, hs, ht⟩, hf, hg⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro x
      simpa [encode] using hr x
    · intro x y hxy
      have hb : encode r x y = true := by simpa [encode] using hxy
      rw [hs x y] at hb
      simpa [encode] using hb
    · intro x y z hxy hyz
      have h1 : encode r x y = true := by simpa [encode] using hxy
      have h2 : encode r y z = true := by simpa [encode] using hyz
      simpa [encode] using ht x y z h1 h2
    · intro x y hxy
      have hb : encode r x y = true := by simpa [encode] using hxy
      simpa [encode] using hf x y hb
    · intro x y hxy
      have hb : encode r x y = true := by simpa [encode] using hxy
      simpa [encode] using hg x y hb
  · rintro ⟨⟨hr, hs, ht⟩, hf, hg⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro x
      simpa [encode] using hr x
    · intro x y
      by_cases hxy : r x y
      · have hyx := hs hxy
        simp [encode, hxy, hyx]
      · have hyx : ¬ r y x := fun h => hxy (hs h)
        simp [encode, hxy, hyx]
    · intro x y z hxy hyz
      have h1 : r x y := by simpa [encode] using hxy
      have h2 : r y z := by simpa [encode] using hyz
      simpa [encode] using ht h1 h2
    · intro x y hxy
      have h1 : r x y := by simpa [encode] using hxy
      simpa [encode] using hf x y h1
    · intro x y hxy
      have h1 : r x y := by simpa [encode] using hxy
      simpa [encode] using hg x y h1

theorem same_encode_iff (r : V → V → Prop) [DecidableRel r] (s : Rel) :
    Same (encode r) s ↔ ∀ x y, r x y ↔ s x y = true := by
  constructor
  · intro h x y
    rw [← h x y]
    simp [encode]
  · intro h x y
    have hi : encode r x y = true ↔ s x y = true := by simpa [encode] using h x y
    cases h1 : encode r x y <;> cases h2 : s x y <;> simp_all

/-- Explicit finite order isomorphism, expressed without a Mathlib dependency. -/
structure Representation (k : Nat) (le : Fin k → Fin k → Bool)
    (f g : V → V) where
  theta : Fin k → Rel
  sound : ∀ a, IsCongruence f g (theta a)
  complete : ∀ r, IsCongruence f g r → ∃ a, Same r (theta a)
  order_exact : ∀ a b, le a b = true ↔ Included (theta a) (theta b)
  injective : ∀ a b, Same (theta a) (theta b) → a = b

namespace N5

def le (x y : Fin 5) : Bool :=
  match x.val, y.val with
  | 0, 0 => true
  | 0, 1 => true
  | 0, 2 => true
  | 0, 3 => true
  | 0, 4 => true
  | 1, 0 => false
  | 1, 1 => true
  | 1, 2 => true
  | 1, 3 => false
  | 1, 4 => true
  | 2, 0 => false
  | 2, 1 => false
  | 2, 2 => true
  | 2, 3 => false
  | 2, 4 => true
  | 3, 0 => false
  | 3, 1 => false
  | 3, 2 => false
  | 3, 3 => true
  | 3, 4 => true
  | 4, 0 => false
  | 4, 1 => false
  | 4, 2 => false
  | 4, 3 => false
  | 4, 4 => true
  | _, _ => false

def color (x y : V) : Fin 5 :=
  match x.val, y.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 3
  | 0, 3 => 4
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 4
  | 1, 3 => 3
  | 2, 0 => 3
  | 2, 1 => 4
  | 2, 2 => 0
  | 2, 3 => 2
  | 3, 0 => 4
  | 3, 1 => 3
  | 3, 2 => 2
  | 3, 3 => 0
  | _, _ => 0

def op1 (x : V) : V :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

def op2 (x : V) : V :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => 1

def theta (a : Fin 5) : Rel := fun x y => le (color x y) a

theorem finite_classification : ∀ s : Shape,
    IsCongruence op1 op2 (relation s) ↔ ∃ a : Fin 5, Same (relation s) (theta a) := by
  rintro ⟨b0, b1, b2, b3, b4, b5⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem all_congruences (r : Rel) :
    IsCongruence op1 op2 r ↔ ∃ a : Fin 5, Same r (theta a) := by
  constructor
  · intro h
    have hr := relation_complete r h.1
    rw [hr]
    exact (finite_classification (shape r)).mp (hr ▸ h)
  · rintro ⟨a, ha⟩
    have hr : r = theta a := funext (fun x => funext (ha x))
    rw [hr]
    exact (show ∀ a : Fin 5, IsCongruence op1 op2 (theta a) by decide) a

theorem all_relations (r : V → V → Prop) :
    IsPropCongruence op1 op2 r ↔ ∃ a, ∀ x y, r x y ↔ theta a x y = true := by
  classical
  rw [← encode_congruence op1 op2 r, all_congruences]
  exact exists_congr (fun a => same_encode_iff r (theta a))

theorem le_is_partial_order :
    (∀ a, le a a = true) ∧
    (∀ a b, le a b = true → le b a = true → a = b) ∧
    (∀ a b c, le a b = true → le b c = true → le a c = true) := by decide

theorem order_exact : ∀ a b : Fin 5,
    le a b = true ↔ Included (theta a) (theta b) := by decide

theorem theta_injective : ∀ a b : Fin 5, Same (theta a) (theta b) → a = b := by decide

def representation : Representation 5 le op1 op2 where
  theta := theta
  sound := by decide
  complete := fun r h => (all_congruences r).mp h
  order_exact := order_exact
  injective := theta_injective

#print axioms finite_classification
#print axioms all_congruences
#print axioms representation
#print axioms all_relations

end N5

namespace B3

def le (x y : Fin 8) : Bool :=
  match x.val, y.val with
  | 0, 0 => true
  | 0, 1 => true
  | 0, 2 => true
  | 0, 3 => true
  | 0, 4 => true
  | 0, 5 => true
  | 0, 6 => true
  | 0, 7 => true
  | 1, 0 => false
  | 1, 1 => true
  | 1, 2 => false
  | 1, 3 => true
  | 1, 4 => false
  | 1, 5 => true
  | 1, 6 => false
  | 1, 7 => true
  | 2, 0 => false
  | 2, 1 => false
  | 2, 2 => true
  | 2, 3 => true
  | 2, 4 => false
  | 2, 5 => false
  | 2, 6 => true
  | 2, 7 => true
  | 3, 0 => false
  | 3, 1 => false
  | 3, 2 => false
  | 3, 3 => true
  | 3, 4 => false
  | 3, 5 => false
  | 3, 6 => false
  | 3, 7 => true
  | 4, 0 => false
  | 4, 1 => false
  | 4, 2 => false
  | 4, 3 => false
  | 4, 4 => true
  | 4, 5 => true
  | 4, 6 => true
  | 4, 7 => true
  | 5, 0 => false
  | 5, 1 => false
  | 5, 2 => false
  | 5, 3 => false
  | 5, 4 => false
  | 5, 5 => true
  | 5, 6 => false
  | 5, 7 => true
  | 6, 0 => false
  | 6, 1 => false
  | 6, 2 => false
  | 6, 3 => false
  | 6, 4 => false
  | 6, 5 => false
  | 6, 6 => true
  | 6, 7 => true
  | 7, 0 => false
  | 7, 1 => false
  | 7, 2 => false
  | 7, 3 => false
  | 7, 4 => false
  | 7, 5 => false
  | 7, 6 => false
  | 7, 7 => true
  | _, _ => false

def color (x y : V) : Fin 8 :=
  match x.val, y.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 4
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 3
  | 1, 3 => 5
  | 2, 0 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 6
  | 3, 0 => 4
  | 3, 1 => 5
  | 3, 2 => 6
  | 3, 3 => 0
  | _, _ => 0

def op1 (x : V) : V :=
  match x.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | _ => 3

def op2 (x : V) : V :=
  match x.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | _ => 0

def theta (a : Fin 8) : Rel := fun x y => le (color x y) a

theorem finite_classification : ∀ s : Shape,
    IsCongruence op1 op2 (relation s) ↔ ∃ a : Fin 8, Same (relation s) (theta a) := by
  rintro ⟨b0, b1, b2, b3, b4, b5⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem all_congruences (r : Rel) :
    IsCongruence op1 op2 r ↔ ∃ a : Fin 8, Same r (theta a) := by
  constructor
  · intro h
    have hr := relation_complete r h.1
    rw [hr]
    exact (finite_classification (shape r)).mp (hr ▸ h)
  · rintro ⟨a, ha⟩
    have hr : r = theta a := funext (fun x => funext (ha x))
    rw [hr]
    exact (show ∀ a : Fin 8, IsCongruence op1 op2 (theta a) by decide) a

theorem all_relations (r : V → V → Prop) :
    IsPropCongruence op1 op2 r ↔ ∃ a, ∀ x y, r x y ↔ theta a x y = true := by
  classical
  rw [← encode_congruence op1 op2 r, all_congruences]
  exact exists_congr (fun a => same_encode_iff r (theta a))

theorem le_is_partial_order :
    (∀ a, le a a = true) ∧
    (∀ a b, le a b = true → le b a = true → a = b) ∧
    (∀ a b c, le a b = true → le b c = true → le a c = true) := by decide

theorem order_exact : ∀ a b : Fin 8,
    le a b = true ↔ Included (theta a) (theta b) := by decide

theorem theta_injective : ∀ a b : Fin 8, Same (theta a) (theta b) → a = b := by decide

def representation : Representation 8 le op1 op2 where
  theta := theta
  sound := by decide
  complete := fun r h => (all_congruences r).mp h
  order_exact := order_exact
  injective := theta_injective

#print axioms finite_classification
#print axioms all_congruences
#print axioms representation
#print axioms all_relations

end B3

end FiniteCongruenceChecks
