/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height19Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height05Part01
import FiniteCards.Height06Part01
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height09Part01
import FiniteCards.Height09Part04
import FiniteCards.Height10Part02
import FiniteCards.Height10Part03
import FiniteCards.Height14Part03
import FiniteCards.Height18Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_694_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_694_i0 j) (childrenD_694_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_390 4 (4, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_544 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 1 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_546 5 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_549 1 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_694_i0 : FiniteTemplate HasSnaky 11 required_694_i0 envelope_694_i0 := by
  refine finite_compose HasSnaky 10 childrenC_694_i0 childrenD_694_i0 finite_children_work_694_i0 (4, 6)
    required_694_i0 envelope_694_i0 pivot_mem_694_i0 child_required_sub_694_i0 child_envelope_sub_694_i0 ?_
  intro b hb
  exact common_sub_694_i0 (mem_commonEnvelope childrenD_694_i0 b hb)

theorem finite_children_work_694_i1 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_694_i1 j) (childrenD_694_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 3 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_142 7 (8, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_693 3 (0, 11)).mono (by decide +kernel)

theorem finite_row_works_694_i1 : FiniteTemplate HasSnaky 15 required_694_i1 envelope_694_i1 := by
  refine finite_compose HasSnaky 14 childrenC_694_i1 childrenD_694_i1 finite_children_work_694_i1 (5, 4)
    required_694_i1 envelope_694_i1 pivot_mem_694_i1 child_required_sub_694_i1 child_envelope_sub_694_i1 ?_
  intro b hb
  exact common_sub_694_i1 (mem_commonEnvelope childrenD_694_i1 b hb)

theorem finite_children_work_694 : ∀ j, FiniteTemplate HasSnaky 18 (childrenC_694 j) (childrenD_694 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_397 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_691 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_694_i0.mono (by decide +kernel)
  · exact finite_row_works_694_i1.mono (by decide +kernel)

theorem finite_row_works_694 : FiniteTemplate HasSnaky 19 required_694 envelope_694 := by
  refine finite_compose HasSnaky 18 childrenC_694 childrenD_694 finite_children_work_694 (5, 7)
    required_694 envelope_694 pivot_mem_694 child_required_sub_694 child_envelope_sub_694 ?_
  intro b hb
  exact common_sub_694 (mem_commonEnvelope childrenD_694 b hb)

end FiniteCongruenceChecks.SnakyFinite
