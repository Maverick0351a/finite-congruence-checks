/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part02
import FiniteCards.Height01Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height05Part03
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_443_i6 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_443_i6 j) (childrenD_443_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_443_i6 : FiniteTemplate HasSnaky 2 required_443_i6 envelope_443_i6 := by
  refine finite_compose HasSnaky 1 childrenC_443_i6 childrenD_443_i6 finite_children_work_443_i6 (5, 3)
    required_443_i6 envelope_443_i6 pivot_mem_443_i6 child_required_sub_443_i6 child_envelope_sub_443_i6 ?_
  intro b hb
  exact common_sub_443_i6 (mem_commonEnvelope childrenD_443_i6 b hb)

theorem finite_children_work_443_i5 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_443_i5 j) (childrenD_443_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 0)).mono (by decide +kernel)
  · exact finite_row_works_443_i6.mono (by decide +kernel)

theorem finite_row_works_443_i5 : FiniteTemplate HasSnaky 3 required_443_i5 envelope_443_i5 := by
  refine finite_compose HasSnaky 2 childrenC_443_i5 childrenD_443_i5 finite_children_work_443_i5 (3, 3)
    required_443_i5 envelope_443_i5 pivot_mem_443_i5 child_required_sub_443_i5 child_envelope_sub_443_i5 ?_
  intro b hb
  exact common_sub_443_i5 (mem_commonEnvelope childrenD_443_i5 b hb)

theorem finite_children_work_443_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_443_i4 j) (childrenD_443_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_443_i5.mono (by decide +kernel)

theorem finite_row_works_443_i4 : FiniteTemplate HasSnaky 4 required_443_i4 envelope_443_i4 := by
  refine finite_compose HasSnaky 3 childrenC_443_i4 childrenD_443_i4 finite_children_work_443_i4 (4, 1)
    required_443_i4 envelope_443_i4 pivot_mem_443_i4 child_required_sub_443_i4 child_envelope_sub_443_i4 ?_
  intro b hb
  exact common_sub_443_i4 (mem_commonEnvelope childrenD_443_i4 b hb)

theorem finite_children_work_443_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_443_i3 j) (childrenD_443_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_443_i4.mono (by decide +kernel)

theorem finite_row_works_443_i3 : FiniteTemplate HasSnaky 5 required_443_i3 envelope_443_i3 := by
  refine finite_compose HasSnaky 4 childrenC_443_i3 childrenD_443_i3 finite_children_work_443_i3 (2, 4)
    required_443_i3 envelope_443_i3 pivot_mem_443_i3 child_required_sub_443_i3 child_envelope_sub_443_i3 ?_
  intro b hb
  exact common_sub_443_i3 (mem_commonEnvelope childrenD_443_i3 b hb)

theorem finite_children_work_443_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_443_i2 j) (childrenD_443_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_443_i3.mono (by decide +kernel)

theorem finite_row_works_443_i2 : FiniteTemplate HasSnaky 6 required_443_i2 envelope_443_i2 := by
  refine finite_compose HasSnaky 5 childrenC_443_i2 childrenD_443_i2 finite_children_work_443_i2 (4, 0)
    required_443_i2 envelope_443_i2 pivot_mem_443_i2 child_required_sub_443_i2 child_envelope_sub_443_i2 ?_
  intro b hb
  exact common_sub_443_i2 (mem_commonEnvelope childrenD_443_i2 b hb)

theorem finite_children_work_443_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_443_i1 j) (childrenD_443_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_443_i2.mono (by decide +kernel)

theorem finite_row_works_443_i1 : FiniteTemplate HasSnaky 7 required_443_i1 envelope_443_i1 := by
  refine finite_compose HasSnaky 6 childrenC_443_i1 childrenD_443_i1 finite_children_work_443_i1 (3, 1)
    required_443_i1 envelope_443_i1 pivot_mem_443_i1 child_required_sub_443_i1 child_envelope_sub_443_i1 ?_
  intro b hb
  exact common_sub_443_i1 (mem_commonEnvelope childrenD_443_i1 b hb)

theorem finite_children_work_443_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_443_i0 j) (childrenD_443_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_443_i1.mono (by decide +kernel)

theorem finite_row_works_443_i0 : FiniteTemplate HasSnaky 8 required_443_i0 envelope_443_i0 := by
  refine finite_compose HasSnaky 7 childrenC_443_i0 childrenD_443_i0 finite_children_work_443_i0 (0, 1)
    required_443_i0 envelope_443_i0 pivot_mem_443_i0 child_required_sub_443_i0 child_envelope_sub_443_i0 ?_
  intro b hb
  exact common_sub_443_i0 (mem_commonEnvelope childrenD_443_i0 b hb)

theorem finite_children_work_443 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_443 j) (childrenD_443 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_443_i0.mono (by decide +kernel)

theorem finite_row_works_443 : FiniteTemplate HasSnaky 9 required_443 envelope_443 := by
  refine finite_compose HasSnaky 8 childrenC_443 childrenD_443 finite_children_work_443 (2, 1)
    required_443 envelope_443 pivot_mem_443 child_required_sub_443 child_envelope_sub_443 ?_
  intro b hb
  exact common_sub_443 (mem_commonEnvelope childrenD_443 b hb)

theorem finite_children_work_449 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_449 j) (childrenD_449 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_48 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_448.mono (by decide +kernel)

theorem finite_row_works_449 : FiniteTemplate HasSnaky 9 required_449 envelope_449 := by
  refine finite_compose HasSnaky 8 childrenC_449 childrenD_449 finite_children_work_449 (4, 3)
    required_449 envelope_449 pivot_mem_449 child_required_sub_449 child_envelope_sub_449 ?_
  intro b hb
  exact common_sub_449 (mem_commonEnvelope childrenD_449 b hb)

theorem finite_children_work_450 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_450 j) (childrenD_450 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_448 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_450 : FiniteTemplate HasSnaky 9 required_450 envelope_450 := by
  refine finite_compose HasSnaky 8 childrenC_450 childrenD_450 finite_children_work_450 (3, 4)
    required_450 envelope_450 pivot_mem_450 child_required_sub_450 child_envelope_sub_450 ?_
  intro b hb
  exact common_sub_450 (mem_commonEnvelope childrenD_450 b hb)

theorem finite_children_work_457 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_457 j) (childrenD_457 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_456 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_457 : FiniteTemplate HasSnaky 9 required_457 envelope_457 := by
  refine finite_compose HasSnaky 8 childrenC_457 childrenD_457 finite_children_work_457 (1, 4)
    required_457 envelope_457 pivot_mem_457 child_required_sub_457 child_envelope_sub_457 ?_
  intro b hb
  exact common_sub_457 (mem_commonEnvelope childrenD_457 b hb)

theorem finite_children_work_458 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_458 j) (childrenD_458 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_9.mono (by decide +kernel)
  · exact finite_row_works_62.mono (by decide +kernel)
  · exact finite_row_works_456.mono (by decide +kernel)

theorem finite_row_works_458 : FiniteTemplate HasSnaky 9 required_458 envelope_458 := by
  refine finite_compose HasSnaky 8 childrenC_458 childrenD_458 finite_children_work_458 (1, 4)
    required_458 envelope_458 pivot_mem_458 child_required_sub_458 child_envelope_sub_458 ?_
  intro b hb
  exact common_sub_458 (mem_commonEnvelope childrenD_458 b hb)

theorem finite_children_work_470_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_470_i0 j) (childrenD_470_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_470_i0 : FiniteTemplate HasSnaky 4 required_470_i0 envelope_470_i0 := by
  refine finite_compose HasSnaky 3 childrenC_470_i0 childrenD_470_i0 finite_children_work_470_i0 (2, 3)
    required_470_i0 envelope_470_i0 pivot_mem_470_i0 child_required_sub_470_i0 child_envelope_sub_470_i0 ?_
  intro b hb
  exact common_sub_470_i0 (mem_commonEnvelope childrenD_470_i0 b hb)

theorem finite_children_work_470_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_470_i2 j) (childrenD_470_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 7 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_470_i2 : FiniteTemplate HasSnaky 4 required_470_i2 envelope_470_i2 := by
  refine finite_compose HasSnaky 3 childrenC_470_i2 childrenD_470_i2 finite_children_work_470_i2 (2, 3)
    required_470_i2 envelope_470_i2 pivot_mem_470_i2 child_required_sub_470_i2 child_envelope_sub_470_i2 ?_
  intro b hb
  exact common_sub_470_i2 (mem_commonEnvelope childrenD_470_i2 b hb)

theorem finite_children_work_470_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_470_i1 j) (childrenD_470_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_56 4 (1, 8)).mono (by decide +kernel)
  · exact finite_row_works_470_i2.mono (by decide +kernel)

theorem finite_row_works_470_i1 : FiniteTemplate HasSnaky 5 required_470_i1 envelope_470_i1 := by
  refine finite_compose HasSnaky 4 childrenC_470_i1 childrenD_470_i1 finite_children_work_470_i1 (3, 6)
    required_470_i1 envelope_470_i1 pivot_mem_470_i1 child_required_sub_470_i1 child_envelope_sub_470_i1 ?_
  intro b hb
  exact common_sub_470_i1 (mem_commonEnvelope childrenD_470_i1 b hb)

theorem finite_children_work_470 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_470 j) (childrenD_470 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_319 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_335 4 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_470_i0.mono (by decide +kernel)
  · exact finite_row_works_470_i1.mono (by decide +kernel)

theorem finite_row_works_470 : FiniteTemplate HasSnaky 9 required_470 envelope_470 := by
  refine finite_compose HasSnaky 8 childrenC_470 childrenD_470 finite_children_work_470 (3, 3)
    required_470 envelope_470 pivot_mem_470 child_required_sub_470 child_envelope_sub_470 ?_
  intro b hb
  exact common_sub_470 (mem_commonEnvelope childrenD_470 b hb)

theorem finite_children_work_474 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_474 j) (childrenD_474 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_473 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_474 : FiniteTemplate HasSnaky 9 required_474 envelope_474 := by
  refine finite_compose HasSnaky 8 childrenC_474 childrenD_474 finite_children_work_474 (4, 2)
    required_474 envelope_474 pivot_mem_474 child_required_sub_474 child_envelope_sub_474 ?_
  intro b hb
  exact common_sub_474 (mem_commonEnvelope childrenD_474 b hb)

theorem finite_children_work_477 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_477 j) (childrenD_477 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_62 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_473.mono (by decide +kernel)

theorem finite_row_works_477 : FiniteTemplate HasSnaky 9 required_477 envelope_477 := by
  refine finite_compose HasSnaky 8 childrenC_477 childrenD_477 finite_children_work_477 (4, 2)
    required_477 envelope_477 pivot_mem_477 child_required_sub_477 child_envelope_sub_477 ?_
  intro b hb
  exact common_sub_477 (mem_commonEnvelope childrenD_477 b hb)

end FiniteCongruenceChecks.SnakyFinite
