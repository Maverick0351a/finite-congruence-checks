/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height01Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_row_works_0 : FiniteTemplate HasSnaky 1 required_0 envelope_0 := by
  have hA : required_0 = snaky.erase (0, 0) := by decide +kernel
  have hT : envelope_0 = snaky := by decide +kernel
  rw [hA, hT]
  exact finite_immediate HasSnaky snaky (0, 0) (by decide +kernel) identity_target

theorem finite_row_works_1 : FiniteTemplate HasSnaky 1 required_1 envelope_1 := by
  have hA : required_1 = snaky.erase (1, 0) := by decide +kernel
  have hT : envelope_1 = snaky := by decide +kernel
  rw [hA, hT]
  exact finite_immediate HasSnaky snaky (1, 0) (by decide +kernel) identity_target

theorem finite_row_works_2 : FiniteTemplate HasSnaky 1 required_2 envelope_2 := by
  have hA : required_2 = snaky.erase (2, 0) := by decide +kernel
  have hT : envelope_2 = snaky := by decide +kernel
  rw [hA, hT]
  exact finite_immediate HasSnaky snaky (2, 0) (by decide +kernel) identity_target

theorem finite_row_works_3 : FiniteTemplate HasSnaky 1 required_3 envelope_3 := by
  have hA : required_3 = snaky.erase (3, 0) := by decide +kernel
  have hT : envelope_3 = snaky := by decide +kernel
  rw [hA, hT]
  exact finite_immediate HasSnaky snaky (3, 0) (by decide +kernel) identity_target

theorem finite_row_works_4 : FiniteTemplate HasSnaky 1 required_4 envelope_4 := by
  have hA : required_4 = snaky.erase (3, 1) := by decide +kernel
  have hT : envelope_4 = snaky := by decide +kernel
  rw [hA, hT]
  exact finite_immediate HasSnaky snaky (3, 1) (by decide +kernel) identity_target

theorem finite_row_works_5 : FiniteTemplate HasSnaky 1 required_5 envelope_5 := by
  have hA : required_5 = snaky.erase (4, 1) := by decide +kernel
  have hT : envelope_5 = snaky := by decide +kernel
  rw [hA, hT]
  exact finite_immediate HasSnaky snaky (4, 1) (by decide +kernel) identity_target

end FiniteCongruenceChecks.SnakyFinite
