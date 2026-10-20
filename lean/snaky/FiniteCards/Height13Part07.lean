/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part07
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height05Part02
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height09Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_720_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_720_i0 j) (childrenD_720_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_200 1 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_720_i0 : FiniteTemplate HasSnaky 7 required_720_i0 envelope_720_i0 := by
  refine finite_compose HasSnaky 6 childrenC_720_i0 childrenD_720_i0 finite_children_work_720_i0 (3, 5)
    required_720_i0 envelope_720_i0 pivot_mem_720_i0 child_required_sub_720_i0 child_envelope_sub_720_i0 ?_
  intro b hb
  exact common_sub_720_i0 (mem_commonEnvelope childrenD_720_i0 b hb)

theorem finite_children_work_720_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_720_i4 j) (childrenD_720_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 2 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_315 1 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_720_i4 : FiniteTemplate HasSnaky 7 required_720_i4 envelope_720_i4 := by
  refine finite_compose HasSnaky 6 childrenC_720_i4 childrenD_720_i4 finite_children_work_720_i4 (6, 7)
    required_720_i4 envelope_720_i4 pivot_mem_720_i4 child_required_sub_720_i4 child_envelope_sub_720_i4 ?_
  intro b hb
  exact common_sub_720_i4 (mem_commonEnvelope childrenD_720_i4 b hb)

theorem finite_children_work_720_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_720_i5 j) (childrenD_720_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_197 7 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_201 5 (8, 4)).mono (by decide +kernel)

theorem finite_row_works_720_i5 : FiniteTemplate HasSnaky 6 required_720_i5 envelope_720_i5 := by
  refine finite_compose HasSnaky 5 childrenC_720_i5 childrenD_720_i5 finite_children_work_720_i5 (7, 4)
    required_720_i5 envelope_720_i5 pivot_mem_720_i5 child_required_sub_720_i5 child_envelope_sub_720_i5 ?_
  intro b hb
  exact common_sub_720_i5 (mem_commonEnvelope childrenD_720_i5 b hb)

theorem finite_children_work_720_i3 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_720_i3 j) (childrenD_720_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_13 2 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 6 (8, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 1 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_720_i4.mono (by decide +kernel)
  · exact finite_row_works_720_i5.mono (by decide +kernel)

theorem finite_row_works_720_i3 : FiniteTemplate HasSnaky 10 required_720_i3 envelope_720_i3 := by
  refine finite_compose HasSnaky 9 childrenC_720_i3 childrenD_720_i3 finite_children_work_720_i3 (7, 7)
    required_720_i3 envelope_720_i3 pivot_mem_720_i3 child_required_sub_720_i3 child_envelope_sub_720_i3 ?_
  intro b hb
  exact common_sub_720_i3 (mem_commonEnvelope childrenD_720_i3 b hb)

theorem finite_children_work_720_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_720_i2 j) (childrenD_720_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (5, 8)).mono (by decide +kernel)
  · exact finite_row_works_720_i3.mono (by decide +kernel)

theorem finite_row_works_720_i2 : FiniteTemplate HasSnaky 11 required_720_i2 envelope_720_i2 := by
  refine finite_compose HasSnaky 10 childrenC_720_i2 childrenD_720_i2 finite_children_work_720_i2 (5, 7)
    required_720_i2 envelope_720_i2 pivot_mem_720_i2 child_required_sub_720_i2 child_envelope_sub_720_i2 ?_
  intro b hb
  exact common_sub_720_i2 (mem_commonEnvelope childrenD_720_i2 b hb)

theorem finite_children_work_720_i1 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_720_i1 j) (childrenD_720_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_310 1 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_720_i2.mono (by decide +kernel)

theorem finite_row_works_720_i1 : FiniteTemplate HasSnaky 12 required_720_i1 envelope_720_i1 := by
  refine finite_compose HasSnaky 11 childrenC_720_i1 childrenD_720_i1 finite_children_work_720_i1 (7, 5)
    required_720_i1 envelope_720_i1 pivot_mem_720_i1 child_required_sub_720_i1 child_envelope_sub_720_i1 ?_
  intro b hb
  exact common_sub_720_i1 (mem_commonEnvelope childrenD_720_i1 b hb)

theorem finite_children_work_720 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_720 j) (childrenD_720 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_64 7 (8, 6)).mono (by decide +kernel)
  · exact finite_row_works_720_i0.mono (by decide +kernel)
  · exact finite_row_works_720_i1.mono (by decide +kernel)

theorem finite_row_works_720 : FiniteTemplate HasSnaky 13 required_720 envelope_720 := by
  refine finite_compose HasSnaky 12 childrenC_720 childrenD_720 finite_children_work_720 (7, 6)
    required_720 envelope_720 pivot_mem_720 child_required_sub_720 child_envelope_sub_720 ?_
  intro b hb
  exact common_sub_720 (mem_commonEnvelope childrenD_720 b hb)

end FiniteCongruenceChecks.SnakyFinite
