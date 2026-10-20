/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part06
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_681_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_681_i1 j) (childrenD_681_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_32 7 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_90 3 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_681_i1 : FiniteTemplate HasSnaky 5 required_681_i1 envelope_681_i1 := by
  refine finite_compose HasSnaky 4 childrenC_681_i1 childrenD_681_i1 finite_children_work_681_i1 (4, 3)
    required_681_i1 envelope_681_i1 pivot_mem_681_i1 child_required_sub_681_i1 child_envelope_sub_681_i1 ?_
  intro b hb
  exact common_sub_681_i1 (mem_commonEnvelope childrenD_681_i1 b hb)

theorem finite_children_work_681_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_681_i2 j) (childrenD_681_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_681_i2 : FiniteTemplate HasSnaky 5 required_681_i2 envelope_681_i2 := by
  refine finite_compose HasSnaky 4 childrenC_681_i2 childrenD_681_i2 finite_children_work_681_i2 (4, 3)
    required_681_i2 envelope_681_i2 pivot_mem_681_i2 child_required_sub_681_i2 child_envelope_sub_681_i2 ?_
  intro b hb
  exact common_sub_681_i2 (mem_commonEnvelope childrenD_681_i2 b hb)

theorem finite_children_work_681_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_681_i0 j) (childrenD_681_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_681_i1.mono (by decide +kernel)
  · exact finite_row_works_681_i2.mono (by decide +kernel)

theorem finite_row_works_681_i0 : FiniteTemplate HasSnaky 6 required_681_i0 envelope_681_i0 := by
  refine finite_compose HasSnaky 5 childrenC_681_i0 childrenD_681_i0 finite_children_work_681_i0 (4, 6)
    required_681_i0 envelope_681_i0 pivot_mem_681_i0 child_required_sub_681_i0 child_envelope_sub_681_i0 ?_
  intro b hb
  exact common_sub_681_i0 (mem_commonEnvelope childrenD_681_i0 b hb)

theorem finite_children_work_681 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_681 j) (childrenD_681 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 1 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_681_i0.mono (by decide +kernel)

theorem finite_row_works_681 : FiniteTemplate HasSnaky 7 required_681 envelope_681 := by
  refine finite_compose HasSnaky 6 childrenC_681 childrenD_681 finite_children_work_681 (3, 4)
    required_681 envelope_681 pivot_mem_681 child_required_sub_681 child_envelope_sub_681 ?_
  intro b hb
  exact common_sub_681 (mem_commonEnvelope childrenD_681 b hb)

end FiniteCongruenceChecks.SnakyFinite
