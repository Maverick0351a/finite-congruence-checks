import FiniteCongruenceChecks

/-! Transport of two unary operations and their congruences on the same Fin 4
carrier. This is a proof for every bijection and relation, not an enumeration. -/
namespace FiniteCongruenceChecks.Renaming

structure Bijection where
  forward : V → V
  backward : V → V
  left_inverse : ∀ x, backward (forward x) = x
  right_inverse : ∀ x, forward (backward x) = x

def operation (e : Bijection) (f : V → V) : V → V :=
  fun x => e.forward (f (e.backward x))

def relation (e : Bijection) (r : V → V → Prop) : V → V → Prop :=
  fun x y => r (e.backward x) (e.backward y)

theorem congruence_iff (e : Bijection) (f g : V → V) (r : V → V → Prop) :
    IsPropCongruence f g r ↔
      IsPropCongruence (operation e f) (operation e g) (relation e r) := by
  constructor
  · rintro ⟨⟨hr, hs, ht⟩, hf, hg⟩
    refine ⟨⟨fun x => hr _, fun h => hs h, fun h k => ht h k⟩, ?_, ?_⟩
    · intro x y h
      simpa only [relation, operation, e.left_inverse] using hf _ _ h
    · intro x y h
      simpa only [relation, operation, e.left_inverse] using hg _ _ h
  · rintro ⟨⟨hr, hs, ht⟩, hf, hg⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro x
      simpa only [relation, e.left_inverse] using hr (e.forward x)
    · intro x y h
      have hh : relation e r (e.forward x) (e.forward y) := by
        simpa only [relation, e.left_inverse] using h
      simpa only [relation, e.left_inverse] using hs hh
    · intro x y z h k
      have hh : relation e r (e.forward x) (e.forward y) := by
        simpa only [relation, e.left_inverse] using h
      have hk : relation e r (e.forward y) (e.forward z) := by
        simpa only [relation, e.left_inverse] using k
      simpa only [relation, e.left_inverse] using ht hh hk
    · intro x y h
      have hh : relation e r (e.forward x) (e.forward y) := by
        simpa only [relation, e.left_inverse] using h
      simpa only [relation, operation, e.left_inverse] using hf _ _ hh
    · intro x y h
      have hh : relation e r (e.forward x) (e.forward y) := by
        simpa only [relation, e.left_inverse] using h
      simpa only [relation, operation, e.left_inverse] using hg _ _ hh

def inverse (e : Bijection) : Bijection :=
  ⟨e.backward, e.forward, e.right_inverse, e.left_inverse⟩

theorem round_trip (e : Bijection) (r : V → V → Prop) :
    relation e (relation (inverse e) r) = r := by
  funext x y
  simp only [relation, inverse, e.right_inverse]

theorem inclusion_iff (e : Bijection) (r s : V → V → Prop) :
    (∀ x y, r x y → s x y) ↔
      (∀ x y, relation e r x y → relation e s x y) := by
  constructor
  · intro h x y hxy
    exact h _ _ hxy
  · intro h x y hxy
    have hh : relation e r (e.forward x) (e.forward y) := by
      simpa only [relation, e.left_inverse] using hxy
    simpa only [relation, e.left_inverse] using h _ _ hh

theorem swap_rules (f g : V → V) (r : V → V → Prop) :
    IsPropCongruence f g r ↔ IsPropCongruence g f r := by
  constructor <;> rintro ⟨he, hf, hg⟩ <;> exact ⟨he, hg, hf⟩

end FiniteCongruenceChecks.Renaming
