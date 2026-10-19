import FiniteCongruenceChecks
import OAI.Algebra.Universal.GraphCriterion

/-!
# The saved N5 and B3 certificates satisfy the pinned upstream graph criterion

The concrete tables are imported from the certificate data via the core proof.
We turn the two unary operations into an upstream algebra, identify its entire
congruence order, and prove that the upstream principal colors are exactly the
saved colors. The upstream theorem then supplies its full `IsGraphWitness`,
including `Relation.EqvGen` connectivity for every nonempty finite seed set.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FiniteCongruenceChecks.UpstreamBridge

open OAI.FiniteCongruence

/-- The actual saved two-operation algebra, in the upstream finite-signature type. -/
def unaryAlgebra (f g : V → V) : Algebra V where
  numOps := 2
  arity := fun _ => 1
  op := fun index inputs => if index.val = 0 then f (inputs 0) else g (inputs 0)

theorem upstream_congruence_isPropCongruence (f g : V → V)
    (r : Congruence (unaryAlgebra f g)) : IsPropCongruence f g r := by
  refine ⟨r.1.iseqv, ?_, ?_⟩
  · intro x y h
    simpa [unaryAlgebra] using
      r.compatible (0 : Fin 2) (fun _ => x) (fun _ => y) (fun _ => h)
  · intro x y h
    simpa [unaryAlgebra] using
      r.compatible (1 : Fin 2) (fun _ => x) (fun _ => y) (fun _ => h)

/-- Boolean congruences from the core proof become exact upstream congruences. -/
def toCongruence (f g : V → V) (r : Rel) (h : IsCongruence f g r) :
    Congruence (unaryAlgebra f g) := by
  refine ⟨⟨fun x y => r x y = true, ⟨h.1.1, ?_, ?_⟩⟩, ?_⟩
  · intro x y hxy
    rw [← h.1.2.1 x y]
    exact hxy
  · intro x y z hxy hyz
    exact h.1.2.2 x y z hxy hyz
  · intro index left right related
    by_cases hi : index.val = 0
    · simpa [unaryAlgebra, hi] using h.2.1 (left (0 : Fin 1)) (right (0 : Fin 1)) (related (0 : Fin 1))
    · simpa [unaryAlgebra, hi] using h.2.2 (left (0 : Fin 1)) (right (0 : Fin 1)) (related (0 : Fin 1))

/-- Convert a complete concrete classification into the upstream order isomorphism. -/
noncomputable def classificationOrderIso {Label : Type} [PartialOrder Label]
    (f g : V → V) (theta : Label → Rel)
    (sound : ∀ a, IsCongruence f g (theta a))
    (complete : ∀ r : V → V → Prop, IsPropCongruence f g r →
      ∃ a, ∀ x y, r x y ↔ theta a x y = true)
    (order : ∀ a b, a ≤ b ↔ Included (theta a) (theta b)) :
    Label ≃o Congruence (unaryAlgebra f g) := by
  let forward := fun a => toCongruence f g (theta a) (sound a)
  have horder : ∀ a b, forward a ≤ forward b ↔ a ≤ b := by
    intro a b
    exact (order a b).symm
  refine { Equiv.ofBijective forward ⟨?_, ?_⟩ with map_rel_iff' := horder _ _ }
  · intro a b hab
    exact le_antisymm ((horder a b).mp hab.le) ((horder b a).mp hab.ge)
  · intro r
    obtain ⟨a, ha⟩ := complete r (upstream_congruence_isPropCongruence f g r)
    refine ⟨a, Congruence.ext ?_⟩
    intro x y
    exact (ha x y).symm

/-- A congruence order isomorphism identifies each saved color as its principal color. -/
theorem principalColor_eq_saved {Label : Type} [Lattice Label] [OrderBot Label]
    {alg : Algebra V} (equiv : Label ≃o Congruence alg) (color : V → V → Label)
    (related : ∀ a x y, equiv a x y ↔ color x y ≤ a) :
    principalColor equiv = color := by
  funext x y
  apply le_antisymm
  · exact (principalColor_le equiv).mpr ((related _ x y).mpr le_rfl)
  · exact (related _ x y).mp ((principalColor_le equiv).mp le_rfl)

namespace N5

/-- A distinct type for the saved order, avoiding the numeric order on `Fin 5`. -/
def Label := Fin 5

instance : Fintype Label := inferInstanceAs (Fintype (Fin 5))
instance : DecidableEq Label := inferInstanceAs (DecidableEq (Fin 5))

instance : PartialOrder Label where
  le a b := FiniteCongruenceChecks.N5.le a b = true
  le_refl := FiniteCongruenceChecks.N5.le_is_partial_order.1
  le_trans := fun a b c => FiniteCongruenceChecks.N5.le_is_partial_order.2.2 a b c
  le_antisymm := FiniteCongruenceChecks.N5.le_is_partial_order.2.1

instance : DecidableLE Label := fun a b =>
  inferInstanceAs (Decidable (FiniteCongruenceChecks.N5.le a b = true))

instance : Lattice Label where
  sup := FiniteCongruenceChecks.N5.join
  le_sup_left := by
    change ∀ a b : Fin 5, FiniteCongruenceChecks.N5.le a (FiniteCongruenceChecks.N5.join a b) = true
    decide
  le_sup_right := by
    change ∀ a b : Fin 5, FiniteCongruenceChecks.N5.le b (FiniteCongruenceChecks.N5.join a b) = true
    decide
  sup_le := by
    change ∀ a b c : Fin 5, FiniteCongruenceChecks.N5.le a c = true → FiniteCongruenceChecks.N5.le b c = true → FiniteCongruenceChecks.N5.le (FiniteCongruenceChecks.N5.join a b) c = true
    decide
  inf := FiniteCongruenceChecks.N5.meet
  inf_le_left := by
    change ∀ a b : Fin 5, FiniteCongruenceChecks.N5.le (FiniteCongruenceChecks.N5.meet a b) a = true
    decide
  inf_le_right := by
    change ∀ a b : Fin 5, FiniteCongruenceChecks.N5.le (FiniteCongruenceChecks.N5.meet a b) b = true
    decide
  le_inf := by
    change ∀ a b c : Fin 5, FiniteCongruenceChecks.N5.le a b = true → FiniteCongruenceChecks.N5.le a c = true → FiniteCongruenceChecks.N5.le a (FiniteCongruenceChecks.N5.meet b c) = true
    decide

instance : OrderBot Label where
  bot := FiniteCongruenceChecks.N5.bottom
  bot_le := by
    change ∀ a : Fin 5, FiniteCongruenceChecks.N5.le FiniteCongruenceChecks.N5.bottom a = true
    decide

def color : V → V → Label := FiniteCongruenceChecks.N5.color
def algebra : Algebra V := unaryAlgebra FiniteCongruenceChecks.N5.op1 FiniteCongruenceChecks.N5.op2

noncomputable def congruenceOrderIso : Label ≃o Congruence algebra :=
  classificationOrderIso _ _ FiniteCongruenceChecks.N5.theta
    FiniteCongruenceChecks.N5.representation.sound
    (fun r h => (FiniteCongruenceChecks.N5.all_relations r).mp h)
    FiniteCongruenceChecks.N5.order_exact

theorem principalColor_eq : principalColor congruenceOrderIso = color :=
  principalColor_eq_saved congruenceOrderIso color (fun _ _ _ => Iff.rfl)

/-- The exact saved N5 coloring satisfies the complete pinned upstream predicate. -/
theorem isGraphWitness : IsGraphWitness color := by
  rw [← principalColor_eq]
  exact principalColor_isGraphWitness congruenceOrderIso

theorem hasGraphWitness : HasGraphWitness Label := ⟨4, by decide, color, isGraphWitness⟩

theorem representable : Representable Label :=
  ⟨4, by decide, algebra, ⟨congruenceOrderIso⟩⟩

#check isGraphWitness
#print axioms congruenceOrderIso
#print axioms principalColor_eq
#print axioms isGraphWitness
#print axioms hasGraphWitness
#print axioms representable

end N5

namespace B3

/-- A distinct type for the saved order, avoiding the numeric order on `Fin 8`. -/
def Label := Fin 8

instance : Fintype Label := inferInstanceAs (Fintype (Fin 8))
instance : DecidableEq Label := inferInstanceAs (DecidableEq (Fin 8))

instance : PartialOrder Label where
  le a b := FiniteCongruenceChecks.B3.le a b = true
  le_refl := FiniteCongruenceChecks.B3.le_is_partial_order.1
  le_trans := fun a b c => FiniteCongruenceChecks.B3.le_is_partial_order.2.2 a b c
  le_antisymm := FiniteCongruenceChecks.B3.le_is_partial_order.2.1

instance : DecidableLE Label := fun a b =>
  inferInstanceAs (Decidable (FiniteCongruenceChecks.B3.le a b = true))

instance : Lattice Label where
  sup := FiniteCongruenceChecks.B3.join
  le_sup_left := by
    change ∀ a b : Fin 8, FiniteCongruenceChecks.B3.le a (FiniteCongruenceChecks.B3.join a b) = true
    decide
  le_sup_right := by
    change ∀ a b : Fin 8, FiniteCongruenceChecks.B3.le b (FiniteCongruenceChecks.B3.join a b) = true
    decide
  sup_le := by
    change ∀ a b c : Fin 8, FiniteCongruenceChecks.B3.le a c = true → FiniteCongruenceChecks.B3.le b c = true → FiniteCongruenceChecks.B3.le (FiniteCongruenceChecks.B3.join a b) c = true
    decide
  inf := FiniteCongruenceChecks.B3.meet
  inf_le_left := by
    change ∀ a b : Fin 8, FiniteCongruenceChecks.B3.le (FiniteCongruenceChecks.B3.meet a b) a = true
    decide
  inf_le_right := by
    change ∀ a b : Fin 8, FiniteCongruenceChecks.B3.le (FiniteCongruenceChecks.B3.meet a b) b = true
    decide
  le_inf := by
    change ∀ a b c : Fin 8, FiniteCongruenceChecks.B3.le a b = true → FiniteCongruenceChecks.B3.le a c = true → FiniteCongruenceChecks.B3.le a (FiniteCongruenceChecks.B3.meet b c) = true
    decide

instance : OrderBot Label where
  bot := FiniteCongruenceChecks.B3.bottom
  bot_le := by
    change ∀ a : Fin 8, FiniteCongruenceChecks.B3.le FiniteCongruenceChecks.B3.bottom a = true
    decide

def color : V → V → Label := FiniteCongruenceChecks.B3.color
def algebra : Algebra V := unaryAlgebra FiniteCongruenceChecks.B3.op1 FiniteCongruenceChecks.B3.op2

noncomputable def congruenceOrderIso : Label ≃o Congruence algebra :=
  classificationOrderIso _ _ FiniteCongruenceChecks.B3.theta
    FiniteCongruenceChecks.B3.representation.sound
    (fun r h => (FiniteCongruenceChecks.B3.all_relations r).mp h)
    FiniteCongruenceChecks.B3.order_exact

theorem principalColor_eq : principalColor congruenceOrderIso = color :=
  principalColor_eq_saved congruenceOrderIso color (fun _ _ _ => Iff.rfl)

/-- The exact saved B3 coloring satisfies the complete pinned upstream predicate. -/
theorem isGraphWitness : IsGraphWitness color := by
  rw [← principalColor_eq]
  exact principalColor_isGraphWitness congruenceOrderIso

theorem hasGraphWitness : HasGraphWitness Label := ⟨4, by decide, color, isGraphWitness⟩

theorem representable : Representable Label :=
  ⟨4, by decide, algebra, ⟨congruenceOrderIso⟩⟩

#check isGraphWitness
#print axioms congruenceOrderIso
#print axioms principalColor_eq
#print axioms isGraphWitness
#print axioms hasGraphWitness
#print axioms representable

end B3

end FiniteCongruenceChecks.UpstreamBridge
