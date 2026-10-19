/-!
Finite congruences on five objects, using only Lean's standard library.
The ten Boolean entries encode every reflexive symmetric relation. Completeness
is proved before using the finite classification, including arbitrary Prop
relations through a classical decidability bridge.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace FiniteCongruenceChecks.FiveObject

abbrev V := Fin 5
abbrev Rel := V → V → Bool
abbrev Table := V × V × V × V × V
abbrev Shape := Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool

def table (t : Table) (x : V) : V :=
  match x.val with
  | 0 => t.1 | 1 => t.2.1 | 2 => t.2.2.1 | 3 => t.2.2.2.1 | _ => t.2.2.2.2

def graph (t : Table) : Rel := fun x y => table t x == table t y

def relation (s : Shape) (x y : V) : Bool :=
  match x.val, y.val with
  | 0, 1 | 1, 0 => s.1
  | 0, 2 | 2, 0 => s.2.1
  | 0, 3 | 3, 0 => s.2.2.1
  | 0, 4 | 4, 0 => s.2.2.2.1
  | 1, 2 | 2, 1 => s.2.2.2.2.1
  | 1, 3 | 3, 1 => s.2.2.2.2.2.1
  | 1, 4 | 4, 1 => s.2.2.2.2.2.2.1
  | 2, 3 | 3, 2 => s.2.2.2.2.2.2.2.1
  | 2, 4 | 4, 2 => s.2.2.2.2.2.2.2.2.1
  | 3, 4 | 4, 3 => s.2.2.2.2.2.2.2.2.2
  | _, _ => true

def shape (r : Rel) : Shape :=
  (r 0 1, r 0 2, r 0 3, r 0 4, r 1 2, r 1 3, r 1 4, r 2 3, r 2 4, r 3 4)

def IsEquivalence (r : Rel) : Prop :=
  (∀ x, r x x = true) ∧
  (∀ x y, r x y = r y x) ∧
  (∀ x y z, r x y = true → r y z = true → r x z = true)
def Preserves (f : V → V) (r : Rel) : Prop :=
  ∀ x y, r x y = true → r (f x) (f y) = true
def IsCongruence {k : Nat} (ops : Fin k → V → V) (r : Rel) : Prop :=
  IsEquivalence r ∧ ∀ i, Preserves (ops i) r
def Same (r s : Rel) : Prop := ∀ x y, r x y = s x y
def Included (r s : Rel) : Prop := ∀ x y, r x y = true → s x y = true
def PreservesFamily (theta : Fin 8 → Rel) (f : V → V) : Prop :=
  ∀ a, Preserves f (theta a)

instance (r : Rel) : Decidable (IsEquivalence r) := inferInstanceAs
  (Decidable ((∀ x, r x x = true) ∧ (∀ x y, r x y = r y x) ∧
    (∀ x y z, r x y = true → r y z = true → r x z = true)))
instance (f : V → V) (r : Rel) : Decidable (Preserves f r) := inferInstanceAs
  (Decidable (∀ x y, r x y = true → r (f x) (f y) = true))
instance {k : Nat} (ops : Fin k → V → V) (r : Rel) : Decidable (IsCongruence ops r) :=
  inferInstanceAs (Decidable (IsEquivalence r ∧ ∀ i, Preserves (ops i) r))
instance (r s : Rel) : Decidable (Same r s) :=
  inferInstanceAs (Decidable (∀ x y, r x y = s x y))
instance (r s : Rel) : Decidable (Included r s) :=
  inferInstanceAs (Decidable (∀ x y, r x y = true → s x y = true))
instance (theta : Fin 8 → Rel) (f : V → V) : Decidable (PreservesFamily theta f) :=
  inferInstanceAs (Decidable (∀ a, Preserves f (theta a)))

theorem fin5_cases : ∀ x : V, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide

theorem table_complete (f : V → V) : table (f 0, f 1, f 2, f 3, f 4) = f := by
  funext x
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem relation_complete (r : Rel) (h : IsEquivalence r) :
    r = relation (shape r) := by
  funext x y
  rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl
  all_goals rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [relation, shape]
  all_goals first | rfl | exact h.1 _ | exact h.2.1 _ _

def IsPropCongruence {k : Nat} (ops : Fin k → V → V) (r : V → V → Prop) : Prop :=
  Equivalence r ∧ ∀ i x y, r x y → r (ops i x) (ops i y)
def encode (r : V → V → Prop) [DecidableRel r] : Rel := fun x y => decide (r x y)
def Realizes {k : Nat} (ops : Fin k → V → V) (theta : Fin 8 → Rel) : Prop :=
  ∀ r : V → V → Prop,
    IsPropCongruence ops r ↔ ∃ a, ∀ x y, r x y ↔ theta a x y = true

theorem encode_congruence {k : Nat} (ops : Fin k → V → V)
    (r : V → V → Prop) [DecidableRel r] :
    IsCongruence ops (encode r) ↔ IsPropCongruence ops r := by
  constructor
  · rintro ⟨⟨hr, hs, ht⟩, hf⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
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
    · intro i x y hxy
      have hb : encode r x y = true := by simpa [encode] using hxy
      simpa [encode] using hf i x y hb
  · rintro ⟨⟨hr, hs, ht⟩, hf⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
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
    · intro i x y hxy
      have h1 : r x y := by simpa [encode] using hxy
      simpa [encode] using hf i x y h1

theorem same_encode_iff (r : V → V → Prop) [DecidableRel r] (s : Rel) :
    Same (encode r) s ↔ ∀ x y, r x y ↔ s x y = true := by
  constructor
  · intro h x y
    rw [← h x y]
    simp [encode]
  · intro h x y
    have hi : encode r x y = true ↔ s x y = true := by simpa [encode] using h x y
    cases h1 : encode r x y <;> cases h2 : s x y <;> simp_all

theorem realizes_bool {k : Nat} (ops : Fin k → V → V) (theta : Fin 8 → Rel)
    (h : Realizes ops theta) (r : Rel) :
    IsCongruence ops r ↔ ∃ a, Same r (theta a) := by
  have he : encode (fun x y => r x y = true) = r := by
    funext x y
    simp [encode]
  rw [← he, encode_congruence, h]
  exact exists_congr (fun a => (same_encode_iff _ _).symm)

theorem realizes_preserves {k : Nat} (ops : Fin k → V → V) (theta : Fin 8 → Rel)
    (h : Realizes ops theta) (i : Fin k) : PreservesFamily theta (ops i) := by
  intro a
  have hh := (realizes_bool ops theta h (theta a)).mpr ⟨a, fun _ _ => rfl⟩
  exact hh.2 i

/-- Padding a signature with identity operations does not change congruences. -/
def padOps {k m : Nat} (ops : Fin k → V → V) (i : Fin m) : V → V :=
  if h : i.val < k then ops ⟨i.val, h⟩ else id

theorem padding_congruence {k m : Nat} (ops : Fin k → V → V) (hkm : k ≤ m)
    (r : V → V → Prop) : IsPropCongruence (padOps (m := m) ops) r ↔ IsPropCongruence ops r := by
  constructor
  · rintro ⟨he, hp⟩
    refine ⟨he, ?_⟩
    intro i x y hxy
    have hi : i.val < m := Nat.lt_of_lt_of_le i.isLt hkm
    simpa [padOps, i.isLt] using hp ⟨i.val, hi⟩ x y hxy
  · rintro ⟨he, hp⟩
    refine ⟨he, ?_⟩
    intro i x y hxy
    by_cases hi : i.val < k
    · simpa [padOps, hi] using hp ⟨i.val, hi⟩ x y hxy
    · simpa [padOps, hi] using hxy

theorem padding_realizes {k m : Nat} (ops : Fin k → V → V) (theta : Fin 8 → Rel)
    (hkm : k ≤ m) (h : Realizes ops theta) : Realizes (padOps (m := m) ops) theta := by
  intro r
  exact (padding_congruence ops hkm r).trans (h r)

end FiniteCongruenceChecks.FiveObject
