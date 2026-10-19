/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height18Part02
import FiniteCards.Height01Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part02
import FiniteCards.Height09Part01
import FiniteCards.Height11Part01
import FiniteCards.Height11Part06
import FiniteCards.Height14Part04
import FiniteCards.Height15Part03
import FiniteCards.Height16Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_701_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_701_i1 j) (childrenD_701_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 3 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_39 2 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_701_i1 : FiniteTemplate HasSnaky 5 required_701_i1 envelope_701_i1 := by
  refine finite_compose HasSnaky 4 childrenC_701_i1 childrenD_701_i1 finite_children_work_701_i1 (5, 8)
    required_701_i1 envelope_701_i1 pivot_mem_701_i1 child_required_sub_701_i1 child_envelope_sub_701_i1 ?_
  intro b hb
  exact common_sub_701_i1 (mem_commonEnvelope childrenD_701_i1 b hb)

theorem finite_children_work_701_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_701_i2 j) (childrenD_701_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 5 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_325 1 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_701_i2 : FiniteTemplate HasSnaky 10 required_701_i2 envelope_701_i2 := by
  refine finite_compose HasSnaky 9 childrenC_701_i2 childrenD_701_i2 finite_children_work_701_i2 (5, 8)
    required_701_i2 envelope_701_i2 pivot_mem_701_i2 child_required_sub_701_i2 child_envelope_sub_701_i2 ?_
  intro b hb
  exact common_sub_701_i2 (mem_commonEnvelope childrenD_701_i2 b hb)

theorem finite_children_work_701_i3 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_701_i3 j) (childrenD_701_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 2 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_463 1 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_701_i3 : FiniteTemplate HasSnaky 12 required_701_i3 envelope_701_i3 := by
  refine finite_compose HasSnaky 11 childrenC_701_i3 childrenD_701_i3 finite_children_work_701_i3 (4, 7)
    required_701_i3 envelope_701_i3 pivot_mem_701_i3 child_required_sub_701_i3 child_envelope_sub_701_i3 ?_
  intro b hb
  exact common_sub_701_i3 (mem_commonEnvelope childrenD_701_i3 b hb)

theorem finite_children_work_701_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_701_i4 j) (childrenD_701_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 3 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_348 2 (7, 6)).mono (by decide +kernel)

theorem finite_row_works_701_i4 : FiniteTemplate HasSnaky 7 required_701_i4 envelope_701_i4 := by
  refine finite_compose HasSnaky 6 childrenC_701_i4 childrenD_701_i4 finite_children_work_701_i4 (4, 8)
    required_701_i4 envelope_701_i4 pivot_mem_701_i4 child_required_sub_701_i4 child_envelope_sub_701_i4 ?_
  intro b hb
  exact common_sub_701_i4 (mem_commonEnvelope childrenD_701_i4 b hb)

theorem finite_children_work_701_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_701_i6 j) (childrenD_701_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (5, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_701_i6 : FiniteTemplate HasSnaky 4 required_701_i6 envelope_701_i6 := by
  refine finite_compose HasSnaky 3 childrenC_701_i6 childrenD_701_i6 finite_children_work_701_i6 (5, 9)
    required_701_i6 envelope_701_i6 pivot_mem_701_i6 child_required_sub_701_i6 child_envelope_sub_701_i6 ?_
  intro b hb
  exact common_sub_701_i6 (mem_commonEnvelope childrenD_701_i6 b hb)

theorem finite_children_work_701_i7 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_701_i7 j) (childrenD_701_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (5, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_372 0 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_701_i7 : FiniteTemplate HasSnaky 8 required_701_i7 envelope_701_i7 := by
  refine finite_compose HasSnaky 7 childrenC_701_i7 childrenD_701_i7 finite_children_work_701_i7 (5, 9)
    required_701_i7 envelope_701_i7 pivot_mem_701_i7 child_required_sub_701_i7 child_envelope_sub_701_i7 ?_
  intro b hb
  exact common_sub_701_i7 (mem_commonEnvelope childrenD_701_i7 b hb)

theorem finite_children_work_701_i5 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_701_i5 j) (childrenD_701_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 3 (4, 8)).mono (by decide +kernel)
  · exact finite_row_works_701_i6.mono (by decide +kernel)
  · exact finite_row_works_701_i7.mono (by decide +kernel)

theorem finite_row_works_701_i5 : FiniteTemplate HasSnaky 9 required_701_i5 envelope_701_i5 := by
  refine finite_compose HasSnaky 8 childrenC_701_i5 childrenD_701_i5 finite_children_work_701_i5 (5, 8)
    required_701_i5 envelope_701_i5 pivot_mem_701_i5 child_required_sub_701_i5 child_envelope_sub_701_i5 ?_
  intro b hb
  exact common_sub_701_i5 (mem_commonEnvelope childrenD_701_i5 b hb)

theorem finite_children_work_701_i0 : ∀ j, FiniteTemplate HasSnaky 16 (childrenC_701_i0 j) (childrenD_701_i0 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_701_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_683 5 (10, 6)).mono (by decide +kernel)
  · exact finite_row_works_701_i2.mono (by decide +kernel)
  · exact finite_row_works_701_i3.mono (by decide +kernel)
  · exact finite_row_works_701_i4.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_700 1 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_701_i5.mono (by decide +kernel)

theorem finite_row_works_701_i0 : FiniteTemplate HasSnaky 17 required_701_i0 envelope_701_i0 := by
  refine finite_compose HasSnaky 16 childrenC_701_i0 childrenD_701_i0 finite_children_work_701_i0 (5, 10)
    required_701_i0 envelope_701_i0 pivot_mem_701_i0 child_required_sub_701_i0 child_envelope_sub_701_i0 ?_
  intro b hb
  exact common_sub_701_i0 (mem_commonEnvelope childrenD_701_i0 b hb)

theorem finite_children_work_701 : ∀ j, FiniteTemplate HasSnaky 17 (childrenC_701 j) (childrenD_701 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 3 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 2 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_697 6 (9, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_699 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_701_i0.mono (by decide +kernel)

theorem finite_row_works_701 : FiniteTemplate HasSnaky 18 required_701 envelope_701 := by
  refine finite_compose HasSnaky 17 childrenC_701 childrenD_701 finite_children_work_701 (7, 7)
    required_701 envelope_701 pivot_mem_701 child_required_sub_701 child_envelope_sub_701 ?_
  intro b hb
  exact common_sub_701 (mem_commonEnvelope childrenD_701 b hb)

end FiniteCongruenceChecks.SnakyFinite
