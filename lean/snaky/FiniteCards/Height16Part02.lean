/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height08Part04
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height11Part02
import FiniteCards.Height13Part03
import FiniteCards.Height15Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_683_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_683_i0 j) (childrenD_683_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_683_i0 : FiniteTemplate HasSnaky 4 required_683_i0 envelope_683_i0 := by
  refine finite_compose HasSnaky 3 childrenC_683_i0 childrenD_683_i0 finite_children_work_683_i0 (2, 5)
    required_683_i0 envelope_683_i0 pivot_mem_683_i0 child_required_sub_683_i0 child_envelope_sub_683_i0 ?_
  intro b hb
  exact common_sub_683_i0 (mem_commonEnvelope childrenD_683_i0 b hb)

theorem finite_children_work_683_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_683_i1 j) (childrenD_683_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_604 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_683_i1 : FiniteTemplate HasSnaky 9 required_683_i1 envelope_683_i1 := by
  refine finite_compose HasSnaky 8 childrenC_683_i1 childrenD_683_i1 finite_children_work_683_i1 (2, 5)
    required_683_i1 envelope_683_i1 pivot_mem_683_i1 child_required_sub_683_i1 child_envelope_sub_683_i1 ?_
  intro b hb
  exact common_sub_683_i1 (mem_commonEnvelope childrenD_683_i1 b hb)

theorem finite_children_work_683 : ∀ j, FiniteTemplate HasSnaky 15 (childrenC_683 j) (childrenD_683 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_150 1 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_683_i0.mono (by decide +kernel)
  · exact finite_row_works_683_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_682 4 (0, 10)).mono (by decide +kernel)

theorem finite_row_works_683 : FiniteTemplate HasSnaky 16 required_683 envelope_683 := by
  refine finite_compose HasSnaky 15 childrenC_683 childrenD_683 finite_children_work_683 (3, 5)
    required_683 envelope_683 pivot_mem_683 child_required_sub_683 child_envelope_sub_683 ?_
  intro b hb
  exact common_sub_683 (mem_commonEnvelope childrenD_683 b hb)

theorem finite_children_work_706_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_706_i2 j) (childrenD_706_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (2, 3)).mono (by decide +kernel)

theorem finite_row_works_706_i2 : FiniteTemplate HasSnaky 4 required_706_i2 envelope_706_i2 := by
  refine finite_compose HasSnaky 3 childrenC_706_i2 childrenD_706_i2 finite_children_work_706_i2 (6, 4)
    required_706_i2 envelope_706_i2 pivot_mem_706_i2 child_required_sub_706_i2 child_envelope_sub_706_i2 ?_
  intro b hb
  exact common_sub_706_i2 (mem_commonEnvelope childrenD_706_i2 b hb)

theorem finite_children_work_706_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_706_i3 j) (childrenD_706_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_154 3 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_159 4 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_706_i3 : FiniteTemplate HasSnaky 4 required_706_i3 envelope_706_i3 := by
  refine finite_compose HasSnaky 3 childrenC_706_i3 childrenD_706_i3 finite_children_work_706_i3 (5, 3)
    required_706_i3 envelope_706_i3 pivot_mem_706_i3 child_required_sub_706_i3 child_envelope_sub_706_i3 ?_
  intro b hb
  exact common_sub_706_i3 (mem_commonEnvelope childrenD_706_i3 b hb)

theorem finite_children_work_706_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_706_i4 j) (childrenD_706_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 3 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_152 2 (8, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_166 0 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_706_i4 : FiniteTemplate HasSnaky 7 required_706_i4 envelope_706_i4 := by
  refine finite_compose HasSnaky 6 childrenC_706_i4 childrenD_706_i4 finite_children_work_706_i4 (7, 5)
    required_706_i4 envelope_706_i4 pivot_mem_706_i4 child_required_sub_706_i4 child_envelope_sub_706_i4 ?_
  intro b hb
  exact common_sub_706_i4 (mem_commonEnvelope childrenD_706_i4 b hb)

theorem finite_children_work_706_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_706_i1 j) (childrenD_706_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_261 3 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_706_i2.mono (by decide +kernel)
  · exact finite_row_works_706_i3.mono (by decide +kernel)
  · exact finite_row_works_706_i4.mono (by decide +kernel)

theorem finite_row_works_706_i1 : FiniteTemplate HasSnaky 8 required_706_i1 envelope_706_i1 := by
  refine finite_compose HasSnaky 7 childrenC_706_i1 childrenD_706_i1 finite_children_work_706_i1 (7, 3)
    required_706_i1 envelope_706_i1 pivot_mem_706_i1 child_required_sub_706_i1 child_envelope_sub_706_i1 ?_
  intro b hb
  exact common_sub_706_i1 (mem_commonEnvelope childrenD_706_i1 b hb)

theorem finite_children_work_706_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_706_i0 j) (childrenD_706_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_65 3 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_706_i1.mono (by decide +kernel)

theorem finite_row_works_706_i0 : FiniteTemplate HasSnaky 9 required_706_i0 envelope_706_i0 := by
  refine finite_compose HasSnaky 8 childrenC_706_i0 childrenD_706_i0 finite_children_work_706_i0 (3, 4)
    required_706_i0 envelope_706_i0 pivot_mem_706_i0 child_required_sub_706_i0 child_envelope_sub_706_i0 ?_
  intro b hb
  exact common_sub_706_i0 (mem_commonEnvelope childrenD_706_i0 b hb)

theorem finite_children_work_706_i6 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_706_i6 j) (childrenD_706_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_318 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_334 7 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_379 3 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_706_i6 : FiniteTemplate HasSnaky 8 required_706_i6 envelope_706_i6 := by
  refine finite_compose HasSnaky 7 childrenC_706_i6 childrenD_706_i6 finite_children_work_706_i6 (3, 3)
    required_706_i6 envelope_706_i6 pivot_mem_706_i6 child_required_sub_706_i6 child_envelope_sub_706_i6 ?_
  intro b hb
  exact common_sub_706_i6 (mem_commonEnvelope childrenD_706_i6 b hb)

theorem finite_children_work_706_i7 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_706_i7 j) (childrenD_706_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_66 7 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_238 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_394 3 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_706_i7 : FiniteTemplate HasSnaky 8 required_706_i7 envelope_706_i7 := by
  refine finite_compose HasSnaky 7 childrenC_706_i7 childrenD_706_i7 finite_children_work_706_i7 (3, 4)
    required_706_i7 envelope_706_i7 pivot_mem_706_i7 child_required_sub_706_i7 child_envelope_sub_706_i7 ?_
  intro b hb
  exact common_sub_706_i7 (mem_commonEnvelope childrenD_706_i7 b hb)

theorem finite_children_work_706_i5 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_706_i5 j) (childrenD_706_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_417 7 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_420 7 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_526 7 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_532 3 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_706_i6.mono (by decide +kernel)
  · exact finite_row_works_706_i7.mono (by decide +kernel)

theorem finite_row_works_706_i5 : FiniteTemplate HasSnaky 9 required_706_i5 envelope_706_i5 := by
  refine finite_compose HasSnaky 8 childrenC_706_i5 childrenD_706_i5 finite_children_work_706_i5 (5, 3)
    required_706_i5 envelope_706_i5 pivot_mem_706_i5 child_required_sub_706_i5 child_envelope_sub_706_i5 ?_
  intro b hb
  exact common_sub_706_i5 (mem_commonEnvelope childrenD_706_i5 b hb)

theorem finite_children_work_706_i9 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_706_i9 j) (childrenD_706_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_59 0 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_296 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_603 0 (6, 1)).mono (by decide +kernel)

theorem finite_row_works_706_i9 : FiniteTemplate HasSnaky 14 required_706_i9 envelope_706_i9 := by
  refine finite_compose HasSnaky 13 childrenC_706_i9 childrenD_706_i9 finite_children_work_706_i9 (7, 4)
    required_706_i9 envelope_706_i9 pivot_mem_706_i9 child_required_sub_706_i9 child_envelope_sub_706_i9 ?_
  intro b hb
  exact common_sub_706_i9 (mem_commonEnvelope childrenD_706_i9 b hb)

theorem finite_children_work_706_i8 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_706_i8 j) (childrenD_706_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 3 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_74 3 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_325 4 (3, 9)).mono (by decide +kernel)
  · exact finite_row_works_706_i9.mono (by decide +kernel)

theorem finite_row_works_706_i8 : FiniteTemplate HasSnaky 15 required_706_i8 envelope_706_i8 := by
  refine finite_compose HasSnaky 14 childrenC_706_i8 childrenD_706_i8 finite_children_work_706_i8 (7, 5)
    required_706_i8 envelope_706_i8 pivot_mem_706_i8 child_required_sub_706_i8 child_envelope_sub_706_i8 ?_
  intro b hb
  exact common_sub_706_i8 (mem_commonEnvelope childrenD_706_i8 b hb)

theorem finite_children_work_706 : ∀ j, FiniteTemplate HasSnaky 15 (childrenC_706 j) (childrenD_706 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_512 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_517 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_527 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_537 7 (8, 6)).mono (by decide +kernel)
  · exact finite_row_works_706_i0.mono (by decide +kernel)
  · exact finite_row_works_706_i5.mono (by decide +kernel)
  · exact finite_row_works_706_i8.mono (by decide +kernel)

theorem finite_row_works_706 : FiniteTemplate HasSnaky 16 required_706 envelope_706 := by
  refine finite_compose HasSnaky 15 childrenC_706 childrenD_706 finite_children_work_706 (4, 4)
    required_706 envelope_706 pivot_mem_706 child_required_sub_706 child_envelope_sub_706 ?_
  intro b hb
  exact common_sub_706 (mem_commonEnvelope childrenD_706 b hb)

end FiniteCongruenceChecks.SnakyFinite
