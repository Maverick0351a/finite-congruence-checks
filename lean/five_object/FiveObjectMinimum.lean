import FiveObjectClassification
import FiveObjectObstructions

/-!
Complete concrete classifications and exact unary-operation lower bounds.
Every finite certificate is evaluated by Lean's kernel through `decide`.
No native compiler result is accepted as a proof.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace FiniteCongruenceChecks.FiveObject

namespace A

theorem all_congruences (r : Rel) :
    IsCongruence ops r ↔ ∃ a : Fin 8, Same r (theta a) := by
  constructor
  · intro h
    have hr := relation_complete r h.1
    rw [hr]
    exact (finite_classification (shape r)).mp (hr ▸ h)
  · rintro ⟨a, ha⟩
    have hr : r = theta a := funext (fun x => funext (ha x))
    rw [hr]
    exact (show ∀ a : Fin 8, IsCongruence ops (theta a) by decide) a

theorem all_relations (r : V → V → Prop) :
    IsPropCongruence ops r ↔ ∃ a : Fin 8, ∀ x y, r x y ↔ theta a x y = true := by
  classical
  rw [← encode_congruence ops r, all_congruences]
  exact exists_congr (fun a => same_encode_iff r (theta a))

theorem order_exact : ∀ a b : Fin 8,
    le a b = true ↔ Included (theta a) (theta b) := by decide

theorem theta_injective : ∀ a b : Fin 8, Same (theta a) (theta b) → a = b := by decide

theorem profile_allowed (f : V → V) (hf : PreservesFamily theta f) : AllowedProfile (profile f) := by
  have h := profile_certificate (f 0) (f 1) (f 2) (f 3) (f 4)
  rw [table_complete] at h
  exact h hf

theorem profiles_intersect : ∀ p q : Profile, AllowedProfile p → AllowedProfile q →
    ∃ i : Fin 4, profileAt p i = true ∧ profileAt q i = true := by
  intro p q hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem profileAt_iff (f : V → V) (i : Fin 4) :
    profileAt (profile f) i = true ↔ Preserves f (obstruction i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl <;> simp [profileAt, profile]

theorem obstruction_equivalence : ∀ i : Fin 4, IsEquivalence (obstruction i) := by decide
theorem obstruction_outside : ∀ (i : Fin 4) (a : Fin 8), ¬ Same (obstruction i) (theta a) := by decide

theorem pair_extra (f g : V → V) (hf : PreservesFamily theta f) (hg : PreservesFamily theta g) :
    ∃ i : Fin 4, Preserves f (obstruction i) ∧ Preserves g (obstruction i) := by
  obtain ⟨i, hi, hj⟩ := profiles_intersect (profile f) (profile g)
    (profile_allowed f hf) (profile_allowed g hg)
  exact ⟨i, (profileAt_iff f i).mp hi, (profileAt_iff g i).mp hj⟩

/-- Arbitrary unary maps, including equal maps, cannot realize the exact A family. -/
theorem no_two_operations (f g : V → V) :
    ¬ Realizes (fun i : Fin 2 => if i.val = 0 then f else g) theta := by
  intro h
  have hf : PreservesFamily theta f := realizes_preserves _ theta h 0
  have hg : PreservesFamily theta g := realizes_preserves _ theta h 1
  obtain ⟨i, hi, hj⟩ := pair_extra f g hf hg
  have hc : IsCongruence (fun j : Fin 2 => if j.val = 0 then f else g) (obstruction i) := by
    refine ⟨obstruction_equivalence i, ?_⟩
    intro j
    by_cases h0 : j.val = 0
    · simpa [h0] using hi
    · simpa [h0] using hj
  obtain ⟨a, ha⟩ := (realizes_bool _ theta h (obstruction i)).mp hc
  exact obstruction_outside i a ha

/-- Includes zero and one rules by identity padding; repeated rules are allowed. -/
theorem no_small_signature {k : Nat} (ops : Fin k → V → V) (hk : k ≤ 2) :
    ¬ Realizes ops theta := by
  intro h
  let padded : Fin 2 → V → V := padOps ops
  have hp : Realizes padded theta := padding_realizes ops theta hk h
  have he : padded = fun i : Fin 2 => if i.val = 0 then padded 0 else padded 1 := by
    funext i
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with rfl | rfl <;> rfl
  rw [he] at hp
  exact no_two_operations (padded 0) (padded 1) hp

end A

namespace B

theorem all_congruences (r : Rel) :
    IsCongruence ops r ↔ ∃ a : Fin 8, Same r (theta a) := by
  constructor
  · intro h
    have hr := relation_complete r h.1
    rw [hr]
    exact (finite_classification (shape r)).mp (hr ▸ h)
  · rintro ⟨a, ha⟩
    have hr : r = theta a := funext (fun x => funext (ha x))
    rw [hr]
    exact (show ∀ a : Fin 8, IsCongruence ops (theta a) by decide) a

theorem all_relations (r : V → V → Prop) :
    IsPropCongruence ops r ↔ ∃ a : Fin 8, ∀ x y, r x y ↔ theta a x y = true := by
  classical
  rw [← encode_congruence ops r, all_congruences]
  exact exists_congr (fun a => same_encode_iff r (theta a))

theorem order_exact : ∀ a b : Fin 8,
    le a b = true ↔ Included (theta (correspondence a)) (theta (correspondence b)) := by decide
theorem theta_injective : ∀ a b : Fin 8, Same (theta a) (theta b) → a = b := by decide

theorem single_extra (f : V → V) (hf : PreservesFamily theta f) :
    ∃ i : Fin 2, Preserves f (obstruction i) := by
  have h := obstruction_certificate (f 0) (f 1) (f 2) (f 3) (f 4)
  rw [table_complete] at h
  rcases h hf with h0 | h1
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩

theorem obstruction_equivalence : ∀ i : Fin 2, IsEquivalence (obstruction i) := by decide
theorem obstruction_outside : ∀ (i : Fin 2) (a : Fin 8), ¬ Same (obstruction i) (theta a) := by decide

theorem no_one_operation (f : V → V) : ¬ Realizes (fun _ : Fin 1 => f) theta := by
  intro h
  have hf := realizes_preserves _ theta h 0
  obtain ⟨i, hi⟩ := single_extra f hf
  obtain ⟨a, ha⟩ := (realizes_bool _ theta h (obstruction i)).mp
    ⟨obstruction_equivalence i, fun _ => hi⟩
  exact obstruction_outside i a ha

theorem no_small_signature {k : Nat} (ops : Fin k → V → V) (hk : k ≤ 1) :
    ¬ Realizes ops theta := by
  intro h
  let padded : Fin 1 → V → V := padOps ops
  have hp : Realizes padded theta := padding_realizes ops theta hk h
  have he : padded = fun _ : Fin 1 => padded 0 := by
    funext i
    have hi : i = 0 := by revert i; decide
    subst i
    rfl
  rw [he] at hp
  exact no_one_operation (padded 0) hp

end B

theorem correspondence_inverse :
    (∀ a, inverseCorrespondence (correspondence a) = a) ∧
    (∀ a, correspondence (inverseCorrespondence a) = a) := by decide

theorem le_is_partial_order :
    (∀ a, le a a = true) ∧
    (∀ a b, le a b = true → le b a = true → a = b) ∧
    (∀ a b c, le a b = true → le b c = true → le a c = true) := by decide

theorem same_order (a b : Fin 8) : Included (A.theta a) (A.theta b) ↔
    Included (B.theta (correspondence a)) (B.theta (correspondence b)) :=
  (A.order_exact a b).symm.trans (B.order_exact a b)

end FiniteCongruenceChecks.FiveObject
