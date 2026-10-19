/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part07
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height06Part02
import FiniteCards.Height08Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_722_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_722_i1 j) (childrenD_722_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_722_i1 : FiniteTemplate HasSnaky 5 required_722_i1 envelope_722_i1 := by
  refine finite_compose HasSnaky 4 childrenC_722_i1 childrenD_722_i1 finite_children_work_722_i1 (3, 4)
    required_722_i1 envelope_722_i1 pivot_mem_722_i1 child_required_sub_722_i1 child_envelope_sub_722_i1 ?_
  intro b hb
  exact common_sub_722_i1 (mem_commonEnvelope childrenD_722_i1 b hb)

theorem finite_children_work_722_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_722_i0 j) (childrenD_722_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_366 6 (5, 8)).mono (by decide +kernel)
  · exact finite_row_works_722_i1.mono (by decide +kernel)

theorem finite_row_works_722_i0 : FiniteTemplate HasSnaky 6 required_722_i0 envelope_722_i0 := by
  refine finite_compose HasSnaky 5 childrenC_722_i0 childrenD_722_i0 finite_children_work_722_i0 (4, 6)
    required_722_i0 envelope_722_i0 pivot_mem_722_i0 child_required_sub_722_i0 child_envelope_sub_722_i0 ?_
  intro b hb
  exact common_sub_722_i0 (mem_commonEnvelope childrenD_722_i0 b hb)

theorem finite_children_work_722_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_722_i2 j) (childrenD_722_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_345 1 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_722_i2 : FiniteTemplate HasSnaky 9 required_722_i2 envelope_722_i2 := by
  refine finite_compose HasSnaky 8 childrenC_722_i2 childrenD_722_i2 finite_children_work_722_i2 (5, 4)
    required_722_i2 envelope_722_i2 pivot_mem_722_i2 child_required_sub_722_i2 child_envelope_sub_722_i2 ?_
  intro b hb
  exact common_sub_722_i2 (mem_commonEnvelope childrenD_722_i2 b hb)

theorem finite_children_work_722_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_722_i3 j) (childrenD_722_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_307 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_722_i3 : FiniteTemplate HasSnaky 5 required_722_i3 envelope_722_i3 := by
  refine finite_compose HasSnaky 4 childrenC_722_i3 childrenD_722_i3 finite_children_work_722_i3 (3, 4)
    required_722_i3 envelope_722_i3 pivot_mem_722_i3 child_required_sub_722_i3 child_envelope_sub_722_i3 ?_
  intro b hb
  exact common_sub_722_i3 (mem_commonEnvelope childrenD_722_i3 b hb)

theorem finite_children_work_722_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_722_i4 j) (childrenD_722_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_267 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_722_i4 : FiniteTemplate HasSnaky 7 required_722_i4 envelope_722_i4 := by
  refine finite_compose HasSnaky 6 childrenC_722_i4 childrenD_722_i4 finite_children_work_722_i4 (3, 4)
    required_722_i4 envelope_722_i4 pivot_mem_722_i4 child_required_sub_722_i4 child_envelope_sub_722_i4 ?_
  intro b hb
  exact common_sub_722_i4 (mem_commonEnvelope childrenD_722_i4 b hb)

theorem finite_children_work_722 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_722 j) (childrenD_722 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_176 4 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_722_i0.mono (by decide +kernel)
  · exact finite_row_works_722_i2.mono (by decide +kernel)
  · exact finite_row_works_722_i3.mono (by decide +kernel)
  · exact finite_row_works_722_i4.mono (by decide +kernel)

theorem finite_row_works_722 : FiniteTemplate HasSnaky 10 required_722 envelope_722 := by
  refine finite_compose HasSnaky 9 childrenC_722 childrenD_722 finite_children_work_722 (4, 4)
    required_722 envelope_722 pivot_mem_722 child_required_sub_722 child_envelope_sub_722 ?_
  intro b hb
  exact common_sub_722 (mem_commonEnvelope childrenD_722 b hb)

end FiniteCongruenceChecks.SnakyFinite
