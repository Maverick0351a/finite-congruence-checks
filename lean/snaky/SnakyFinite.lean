import FiniteCards.Height21Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

/-- The exact coordinate board 0 ≤ x,y ≤ 16, including all 289 cells. -/
def square17 : Finset Cell := (Finset.Icc (0 : ℤ) 16).product (Finset.Icc (0 : ℤ) 16)

theorem envelope_card : envelope_727.card = 251 := by decide +kernel

theorem square_card : square17.card = 289 := by decide +kernel

theorem envelope_subset_square : envelope_727 ⊆ square17 := by decide +kernel

theorem square_membership (p : Cell) :
    p ∈ square17 ↔ 0 ≤ p.1 ∧ p.1 ≤ 16 ∧ 0 ≤ p.2 ∧ p.2 ≤ 16 := by
  simp [square17, and_assoc]

/-- Every containing finite board with at least 42 cells supports this strategy.
All Maker choices and legal Breaker replies are quantified within U. -/
theorem board_wins (U : Finset Cell) (hU : envelope_727 ⊆ U) (hsize : 42 ≤ U.card) :
    FiniteWins U HasSnaky 21 ∅ ∅ := by
  apply finite_row_works_727 U ∅ ∅ hU
  · simp
  · simp
  · simp
  · simp [required_727]
  · simp
  · simpa using hsize

theorem envelope_wins : FiniteWins envelope_727 HasSnaky 21 ∅ ∅ :=
  board_wins envelope_727 (Finset.Subset.refl _) (by rw [envelope_card]; decide)

theorem square_wins : FiniteWins square17 HasSnaky 21 ∅ ∅ :=
  board_wins square17 envelope_subset_square (by rw [square_card]; decide)

/-- The public result refers to the upstream six-cell Snaky target exactly. -/
theorem target_exact : snaky = {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)} := rfl

end FiniteCongruenceChecks.SnakyFinite
