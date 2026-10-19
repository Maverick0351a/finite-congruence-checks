/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height09Part01
import FiniteCards.Height10Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_427_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_427_i6 j) (childrenD_427_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_70 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_226 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_427_i6 : FiniteTemplate HasSnaky 4 required_427_i6 envelope_427_i6 := by
  refine finite_compose HasSnaky 3 childrenC_427_i6 childrenD_427_i6 finite_children_work_427_i6 (4, 3)
    required_427_i6 envelope_427_i6 pivot_mem_427_i6 child_required_sub_427_i6 child_envelope_sub_427_i6 ?_
  intro b hb
  exact common_sub_427_i6 (mem_commonEnvelope childrenD_427_i6 b hb)

theorem finite_children_work_427_i5 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_427_i5 j) (childrenD_427_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_427_i6.mono (by decide +kernel)

theorem finite_row_works_427_i5 : FiniteTemplate HasSnaky 5 required_427_i5 envelope_427_i5 := by
  refine finite_compose HasSnaky 4 childrenC_427_i5 childrenD_427_i5 finite_children_work_427_i5 (4, 1)
    required_427_i5 envelope_427_i5 pivot_mem_427_i5 child_required_sub_427_i5 child_envelope_sub_427_i5 ?_
  intro b hb
  exact common_sub_427_i5 (mem_commonEnvelope childrenD_427_i5 b hb)

theorem finite_children_work_427_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_427_i4 j) (childrenD_427_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_427_i5.mono (by decide +kernel)

theorem finite_row_works_427_i4 : FiniteTemplate HasSnaky 6 required_427_i4 envelope_427_i4 := by
  refine finite_compose HasSnaky 5 childrenC_427_i4 childrenD_427_i4 finite_children_work_427_i4 (4, 2)
    required_427_i4 envelope_427_i4 pivot_mem_427_i4 child_required_sub_427_i4 child_envelope_sub_427_i4 ?_
  intro b hb
  exact common_sub_427_i4 (mem_commonEnvelope childrenD_427_i4 b hb)

theorem finite_children_work_427_i9 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_427_i9 j) (childrenD_427_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_2 5 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_427_i9 : FiniteTemplate HasSnaky 2 required_427_i9 envelope_427_i9 := by
  refine finite_compose HasSnaky 1 childrenC_427_i9 childrenD_427_i9 finite_children_work_427_i9 (3, 3)
    required_427_i9 envelope_427_i9 pivot_mem_427_i9 child_required_sub_427_i9 child_envelope_sub_427_i9 ?_
  intro b hb
  exact common_sub_427_i9 (mem_commonEnvelope childrenD_427_i9 b hb)

theorem finite_children_work_427_i8 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_427_i8 j) (childrenD_427_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_427_i9.mono (by decide +kernel)

theorem finite_row_works_427_i8 : FiniteTemplate HasSnaky 3 required_427_i8 envelope_427_i8 := by
  refine finite_compose HasSnaky 2 childrenC_427_i8 childrenD_427_i8 finite_children_work_427_i8 (2, 3)
    required_427_i8 envelope_427_i8 pivot_mem_427_i8 child_required_sub_427_i8 child_envelope_sub_427_i8 ?_
  intro b hb
  exact common_sub_427_i8 (mem_commonEnvelope childrenD_427_i8 b hb)

theorem finite_children_work_427_i7 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_427_i7 j) (childrenD_427_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_427_i8.mono (by decide +kernel)

theorem finite_row_works_427_i7 : FiniteTemplate HasSnaky 4 required_427_i7 envelope_427_i7 := by
  refine finite_compose HasSnaky 3 childrenC_427_i7 childrenD_427_i7 finite_children_work_427_i7 (3, 0)
    required_427_i7 envelope_427_i7 pivot_mem_427_i7 child_required_sub_427_i7 child_envelope_sub_427_i7 ?_
  intro b hb
  exact common_sub_427_i7 (mem_commonEnvelope childrenD_427_i7 b hb)

theorem finite_children_work_427_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_427_i3 j) (childrenD_427_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 3 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_357 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_427_i4.mono (by decide +kernel)
  · exact finite_row_works_427_i7.mono (by decide +kernel)

theorem finite_row_works_427_i3 : FiniteTemplate HasSnaky 7 required_427_i3 envelope_427_i3 := by
  refine finite_compose HasSnaky 6 childrenC_427_i3 childrenD_427_i3 finite_children_work_427_i3 (3, 1)
    required_427_i3 envelope_427_i3 pivot_mem_427_i3 child_required_sub_427_i3 child_envelope_sub_427_i3 ?_
  intro b hb
  exact common_sub_427_i3 (mem_commonEnvelope childrenD_427_i3 b hb)

theorem finite_children_work_427_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_427_i2 j) (childrenD_427_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_427_i3.mono (by decide +kernel)

theorem finite_row_works_427_i2 : FiniteTemplate HasSnaky 8 required_427_i2 envelope_427_i2 := by
  refine finite_compose HasSnaky 7 childrenC_427_i2 childrenD_427_i2 finite_children_work_427_i2 (0, 1)
    required_427_i2 envelope_427_i2 pivot_mem_427_i2 child_required_sub_427_i2 child_envelope_sub_427_i2 ?_
  intro b hb
  exact common_sub_427_i2 (mem_commonEnvelope childrenD_427_i2 b hb)

theorem finite_children_work_427_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_427_i1 j) (childrenD_427_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_427_i2.mono (by decide +kernel)

theorem finite_row_works_427_i1 : FiniteTemplate HasSnaky 9 required_427_i1 envelope_427_i1 := by
  refine finite_compose HasSnaky 8 childrenC_427_i1 childrenD_427_i1 finite_children_work_427_i1 (0, 4)
    required_427_i1 envelope_427_i1 pivot_mem_427_i1 child_required_sub_427_i1 child_envelope_sub_427_i1 ?_
  intro b hb
  exact common_sub_427_i1 (mem_commonEnvelope childrenD_427_i1 b hb)

theorem finite_children_work_427_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_427_i0 j) (childrenD_427_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_427_i1.mono (by decide +kernel)

theorem finite_row_works_427_i0 : FiniteTemplate HasSnaky 10 required_427_i0 envelope_427_i0 := by
  refine finite_compose HasSnaky 9 childrenC_427_i0 childrenD_427_i0 finite_children_work_427_i0 (2, 4)
    required_427_i0 envelope_427_i0 pivot_mem_427_i0 child_required_sub_427_i0 child_envelope_sub_427_i0 ?_
  intro b hb
  exact common_sub_427_i0 (mem_commonEnvelope childrenD_427_i0 b hb)

theorem finite_children_work_427 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_427 j) (childrenD_427 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_427_i0.mono (by decide +kernel)

theorem finite_row_works_427 : FiniteTemplate HasSnaky 11 required_427 envelope_427 := by
  refine finite_compose HasSnaky 10 childrenC_427 childrenD_427 finite_children_work_427 (2, 1)
    required_427 envelope_427 pivot_mem_427 child_required_sub_427 child_envelope_sub_427 ?_
  intro b hb
  exact common_sub_427 (mem_commonEnvelope childrenD_427 b hb)

theorem finite_children_work_463_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_463_i0 j) (childrenD_463_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_348 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_463_i0 : FiniteTemplate HasSnaky 7 required_463_i0 envelope_463_i0 := by
  refine finite_compose HasSnaky 6 childrenC_463_i0 childrenD_463_i0 finite_children_work_463_i0 (2, 6)
    required_463_i0 envelope_463_i0 pivot_mem_463_i0 child_required_sub_463_i0 child_envelope_sub_463_i0 ?_
  intro b hb
  exact common_sub_463_i0 (mem_commonEnvelope childrenD_463_i0 b hb)

theorem finite_children_work_463 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_463 j) (childrenD_463 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_147 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_167 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_463_i0.mono (by decide +kernel)
  · exact finite_row_works_353.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_460 4 (3, 8)).mono (by decide +kernel)

theorem finite_row_works_463 : FiniteTemplate HasSnaky 11 required_463 envelope_463 := by
  refine finite_compose HasSnaky 10 childrenC_463 childrenD_463 finite_children_work_463 (4, 5)
    required_463 envelope_463 pivot_mem_463 child_required_sub_463 child_envelope_sub_463 ?_
  intro b hb
  exact common_sub_463 (mem_commonEnvelope childrenD_463 b hb)

theorem finite_children_work_467 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_467 j) (childrenD_467 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_31 6 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_398 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_444 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_466 6 (5, 7)).mono (by decide +kernel)

theorem finite_row_works_467 : FiniteTemplate HasSnaky 11 required_467 envelope_467 := by
  refine finite_compose HasSnaky 10 childrenC_467 childrenD_467 finite_children_work_467 (4, 6)
    required_467 envelope_467 pivot_mem_467 child_required_sub_467 child_envelope_sub_467 ?_
  intro b hb
  exact common_sub_467 (mem_commonEnvelope childrenD_467 b hb)

theorem finite_children_work_468_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_468_i1 j) (childrenD_468_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_71 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_73 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_468_i1 : FiniteTemplate HasSnaky 6 required_468_i1 envelope_468_i1 := by
  refine finite_compose HasSnaky 5 childrenC_468_i1 childrenD_468_i1 finite_children_work_468_i1 (3, 3)
    required_468_i1 envelope_468_i1 pivot_mem_468_i1 child_required_sub_468_i1 child_envelope_sub_468_i1 ?_
  intro b hb
  exact common_sub_468_i1 (mem_commonEnvelope childrenD_468_i1 b hb)

theorem finite_children_work_468_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_468_i3 j) (childrenD_468_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_75 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_266 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_447 0 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_468_i3 : FiniteTemplate HasSnaky 8 required_468_i3 envelope_468_i3 := by
  refine finite_compose HasSnaky 7 childrenC_468_i3 childrenD_468_i3 finite_children_work_468_i3 (3, 6)
    required_468_i3 envelope_468_i3 pivot_mem_468_i3 child_required_sub_468_i3 child_envelope_sub_468_i3 ?_
  intro b hb
  exact common_sub_468_i3 (mem_commonEnvelope childrenD_468_i3 b hb)

theorem finite_children_work_468_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_468_i2 j) (childrenD_468_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_426 6 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_468_i3.mono (by decide +kernel)

theorem finite_row_works_468_i2 : FiniteTemplate HasSnaky 9 required_468_i2 envelope_468_i2 := by
  refine finite_compose HasSnaky 8 childrenC_468_i2 childrenD_468_i2 finite_children_work_468_i2 (3, 3)
    required_468_i2 envelope_468_i2 pivot_mem_468_i2 child_required_sub_468_i2 child_envelope_sub_468_i2 ?_
  intro b hb
  exact common_sub_468_i2 (mem_commonEnvelope childrenD_468_i2 b hb)

theorem finite_children_work_468_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_468_i0 j) (childrenD_468_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_468_i1.mono (by decide +kernel)
  · exact finite_row_works_468_i2.mono (by decide +kernel)

theorem finite_row_works_468_i0 : FiniteTemplate HasSnaky 10 required_468_i0 envelope_468_i0 := by
  refine finite_compose HasSnaky 9 childrenC_468_i0 childrenD_468_i0 finite_children_work_468_i0 (3, 5)
    required_468_i0 envelope_468_i0 pivot_mem_468_i0 child_required_sub_468_i0 child_envelope_sub_468_i0 ?_
  intro b hb
  exact common_sub_468_i0 (mem_commonEnvelope childrenD_468_i0 b hb)

theorem finite_children_work_468 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_468 j) (childrenD_468 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_126 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_126 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_468_i0.mono (by decide +kernel)

theorem finite_row_works_468 : FiniteTemplate HasSnaky 11 required_468 envelope_468 := by
  refine finite_compose HasSnaky 10 childrenC_468 childrenD_468 finite_children_work_468 (3, 4)
    required_468 envelope_468 pivot_mem_468 child_required_sub_468 child_envelope_sub_468 ?_
  intro b hb
  exact common_sub_468 (mem_commonEnvelope childrenD_468 b hb)

end FiniteCongruenceChecks.SnakyFinite
