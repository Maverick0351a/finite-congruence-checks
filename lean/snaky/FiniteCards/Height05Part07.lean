/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part07
import FiniteCards.Height01Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_679_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_679_i0 j) (childrenD_679_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_222 5 (5, 1)).mono (by decide +kernel)

theorem finite_row_works_679_i0 : FiniteTemplate HasSnaky 4 required_679_i0 envelope_679_i0 := by
  refine finite_compose HasSnaky 3 childrenC_679_i0 childrenD_679_i0 finite_children_work_679_i0 (3, 3)
    required_679_i0 envelope_679_i0 pivot_mem_679_i0 child_required_sub_679_i0 child_envelope_sub_679_i0 ?_
  intro b hb
  exact common_sub_679_i0 (mem_commonEnvelope childrenD_679_i0 b hb)

theorem finite_children_work_679 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_679 j) (childrenD_679 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_679_i0.mono (by decide +kernel)

theorem finite_row_works_679 : FiniteTemplate HasSnaky 5 required_679 envelope_679 := by
  refine finite_compose HasSnaky 4 childrenC_679 childrenD_679 finite_children_work_679 (2, 3)
    required_679 envelope_679 pivot_mem_679 child_required_sub_679 child_envelope_sub_679 ?_
  intro b hb
  exact common_sub_679 (mem_commonEnvelope childrenD_679 b hb)

end FiniteCongruenceChecks.SnakyFinite
