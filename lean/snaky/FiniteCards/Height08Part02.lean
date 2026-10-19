/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part05
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_452_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_452_i0 j) (childrenD_452_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 0 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_452_i0 : FiniteTemplate HasSnaky 5 required_452_i0 envelope_452_i0 := by
  refine finite_compose HasSnaky 4 childrenC_452_i0 childrenD_452_i0 finite_children_work_452_i0 (6, 4)
    required_452_i0 envelope_452_i0 pivot_mem_452_i0 child_required_sub_452_i0 child_envelope_sub_452_i0 ?_
  intro b hb
  exact common_sub_452_i0 (mem_commonEnvelope childrenD_452_i0 b hb)

theorem finite_children_work_452 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_452 j) (childrenD_452 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 7 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_317 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_452_i0.mono (by decide +kernel)

theorem finite_row_works_452 : FiniteTemplate HasSnaky 8 required_452 envelope_452 := by
  refine finite_compose HasSnaky 7 childrenC_452 childrenD_452 finite_children_work_452 (4, 4)
    required_452 envelope_452 pivot_mem_452 child_required_sub_452 child_envelope_sub_452 ?_
  intro b hb
  exact common_sub_452 (mem_commonEnvelope childrenD_452 b hb)

theorem finite_children_work_454 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_454 j) (childrenD_454 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_453 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_454 : FiniteTemplate HasSnaky 8 required_454 envelope_454 := by
  refine finite_compose HasSnaky 7 childrenC_454 childrenD_454 finite_children_work_454 (1, 3)
    required_454 envelope_454 pivot_mem_454 child_required_sub_454 child_envelope_sub_454 ?_
  intro b hb
  exact common_sub_454 (mem_commonEnvelope childrenD_454 b hb)

theorem finite_children_work_455 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_455 j) (childrenD_455 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_453.mono (by decide +kernel)

theorem finite_row_works_455 : FiniteTemplate HasSnaky 8 required_455 envelope_455 := by
  refine finite_compose HasSnaky 7 childrenC_455 childrenD_455 finite_children_work_455 (1, 1)
    required_455 envelope_455 pivot_mem_455 child_required_sub_455 child_envelope_sub_455 ?_
  intro b hb
  exact common_sub_455 (mem_commonEnvelope childrenD_455 b hb)

theorem finite_children_work_456 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_456 j) (childrenD_456 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_453 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_456 : FiniteTemplate HasSnaky 8 required_456 envelope_456 := by
  refine finite_compose HasSnaky 7 childrenC_456 childrenD_456 finite_children_work_456 (2, 4)
    required_456 envelope_456 pivot_mem_456 child_required_sub_456 child_envelope_sub_456 ?_
  intro b hb
  exact common_sub_456 (mem_commonEnvelope childrenD_456 b hb)

theorem finite_children_work_473 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_473 j) (childrenD_473 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_472.mono (by decide +kernel)

theorem finite_row_works_473 : FiniteTemplate HasSnaky 8 required_473 envelope_473 := by
  refine finite_compose HasSnaky 7 childrenC_473 childrenD_473 finite_children_work_473 (1, 1)
    required_473 envelope_473 pivot_mem_473 child_required_sub_473 child_envelope_sub_473 ?_
  intro b hb
  exact common_sub_473 (mem_commonEnvelope childrenD_473 b hb)

theorem finite_children_work_478 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_478 j) (childrenD_478 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_472.mono (by decide +kernel)

theorem finite_row_works_478 : FiniteTemplate HasSnaky 8 required_478 envelope_478 := by
  refine finite_compose HasSnaky 7 childrenC_478 childrenD_478 finite_children_work_478 (2, 2)
    required_478 envelope_478 pivot_mem_478 child_required_sub_478 child_envelope_sub_478 ?_
  intro b hb
  exact common_sub_478 (mem_commonEnvelope childrenD_478 b hb)

theorem finite_children_work_482 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_482 j) (childrenD_482 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_124 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_472.mono (by decide +kernel)

theorem finite_row_works_482 : FiniteTemplate HasSnaky 8 required_482 envelope_482 := by
  refine finite_compose HasSnaky 7 childrenC_482 childrenD_482 finite_children_work_482 (2, 2)
    required_482 envelope_482 pivot_mem_482 child_required_sub_482 child_envelope_sub_482 ?_
  intro b hb
  exact common_sub_482 (mem_commonEnvelope childrenD_482 b hb)

theorem finite_children_work_484_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_484_i1 j) (childrenD_484_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_96 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_484_i1 : FiniteTemplate HasSnaky 3 required_484_i1 envelope_484_i1 := by
  refine finite_compose HasSnaky 2 childrenC_484_i1 childrenD_484_i1 finite_children_work_484_i1 (2, 2)
    required_484_i1 envelope_484_i1 pivot_mem_484_i1 child_required_sub_484_i1 child_envelope_sub_484_i1 ?_
  intro b hb
  exact common_sub_484_i1 (mem_commonEnvelope childrenD_484_i1 b hb)

theorem finite_children_work_484_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_484_i2 j) (childrenD_484_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_130 6 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_484_i2 : FiniteTemplate HasSnaky 5 required_484_i2 envelope_484_i2 := by
  refine finite_compose HasSnaky 4 childrenC_484_i2 childrenD_484_i2 finite_children_work_484_i2 (4, 4)
    required_484_i2 envelope_484_i2 pivot_mem_484_i2 child_required_sub_484_i2 child_envelope_sub_484_i2 ?_
  intro b hb
  exact common_sub_484_i2 (mem_commonEnvelope childrenD_484_i2 b hb)

theorem finite_children_work_484_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_484_i4 j) (childrenD_484_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_223 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_484_i4 : FiniteTemplate HasSnaky 4 required_484_i4 envelope_484_i4 := by
  refine finite_compose HasSnaky 3 childrenC_484_i4 childrenD_484_i4 finite_children_work_484_i4 (2, 2)
    required_484_i4 envelope_484_i4 pivot_mem_484_i4 child_required_sub_484_i4 child_envelope_sub_484_i4 ?_
  intro b hb
  exact common_sub_484_i4 (mem_commonEnvelope childrenD_484_i4 b hb)

theorem finite_children_work_484_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_484_i3 j) (childrenD_484_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_268 2 (5, 0)).mono (by decide +kernel)
  · exact finite_row_works_484_i4.mono (by decide +kernel)

theorem finite_row_works_484_i3 : FiniteTemplate HasSnaky 5 required_484_i3 envelope_484_i3 := by
  refine finite_compose HasSnaky 4 childrenC_484_i3 childrenD_484_i3 finite_children_work_484_i3 (4, 2)
    required_484_i3 envelope_484_i3 pivot_mem_484_i3 child_required_sub_484_i3 child_envelope_sub_484_i3 ?_
  intro b hb
  exact common_sub_484_i3 (mem_commonEnvelope childrenD_484_i3 b hb)

theorem finite_children_work_484_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_484_i0 j) (childrenD_484_i0 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_484_i1.mono (by decide +kernel)
  · exact finite_row_works_484_i2.mono (by decide +kernel)
  · exact finite_row_works_484_i3.mono (by decide +kernel)

theorem finite_row_works_484_i0 : FiniteTemplate HasSnaky 6 required_484_i0 envelope_484_i0 := by
  refine finite_compose HasSnaky 5 childrenC_484_i0 childrenD_484_i0 finite_children_work_484_i0 (3, 2)
    required_484_i0 envelope_484_i0 pivot_mem_484_i0 child_required_sub_484_i0 child_envelope_sub_484_i0 ?_
  intro b hb
  exact common_sub_484_i0 (mem_commonEnvelope childrenD_484_i0 b hb)

theorem finite_children_work_484_i6 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_484_i6 j) (childrenD_484_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_58 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_168 6 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_357 6 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_484_i6 : FiniteTemplate HasSnaky 6 required_484_i6 envelope_484_i6 := by
  refine finite_compose HasSnaky 5 childrenC_484_i6 childrenD_484_i6 finite_children_work_484_i6 (4, 4)
    required_484_i6 envelope_484_i6 pivot_mem_484_i6 child_required_sub_484_i6 child_envelope_sub_484_i6 ?_
  intro b hb
  exact common_sub_484_i6 (mem_commonEnvelope childrenD_484_i6 b hb)

theorem finite_children_work_484_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_484_i5 j) (childrenD_484_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_314 5 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_484_i6.mono (by decide +kernel)

theorem finite_row_works_484_i5 : FiniteTemplate HasSnaky 7 required_484_i5 envelope_484_i5 := by
  refine finite_compose HasSnaky 6 childrenC_484_i5 childrenD_484_i5 finite_children_work_484_i5 (2, 4)
    required_484_i5 envelope_484_i5 pivot_mem_484_i5 child_required_sub_484_i5 child_envelope_sub_484_i5 ?_
  intro b hb
  exact common_sub_484_i5 (mem_commonEnvelope childrenD_484_i5 b hb)

theorem finite_children_work_484 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_484 j) (childrenD_484 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_81 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_204 4 (0, 8)).mono (by decide +kernel)
  · exact finite_row_works_484_i0.mono (by decide +kernel)
  · exact finite_row_works_484_i5.mono (by decide +kernel)

theorem finite_row_works_484 : FiniteTemplate HasSnaky 8 required_484 envelope_484 := by
  refine finite_compose HasSnaky 7 childrenC_484 childrenD_484 finite_children_work_484 (4, 5)
    required_484 envelope_484 pivot_mem_484 child_required_sub_484 child_envelope_sub_484 ?_
  intro b hb
  exact common_sub_484 (mem_commonEnvelope childrenD_484 b hb)

theorem finite_children_work_494 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_494 j) (childrenD_494 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_87.mono (by decide +kernel)
  · exact finite_row_works_286.mono (by decide +kernel)
  · exact finite_row_works_492.mono (by decide +kernel)

theorem finite_row_works_494 : FiniteTemplate HasSnaky 8 required_494 envelope_494 := by
  refine finite_compose HasSnaky 7 childrenC_494 childrenD_494 finite_children_work_494 (3, 3)
    required_494 envelope_494 pivot_mem_494 child_required_sub_494 child_envelope_sub_494 ?_
  intro b hb
  exact common_sub_494 (mem_commonEnvelope childrenD_494 b hb)

theorem finite_children_work_510_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_510_i0 j) (childrenD_510_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_138 5 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_510_i0 : FiniteTemplate HasSnaky 3 required_510_i0 envelope_510_i0 := by
  refine finite_compose HasSnaky 2 childrenC_510_i0 childrenD_510_i0 finite_children_work_510_i0 (1, 4)
    required_510_i0 envelope_510_i0 pivot_mem_510_i0 child_required_sub_510_i0 child_envelope_sub_510_i0 ?_
  intro b hb
  exact common_sub_510_i0 (mem_commonEnvelope childrenD_510_i0 b hb)

theorem finite_children_work_510 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_510 j) (childrenD_510 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_510_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_510 : FiniteTemplate HasSnaky 8 required_510 envelope_510 := by
  refine finite_compose HasSnaky 7 childrenC_510 childrenD_510 finite_children_work_510 (4, 3)
    required_510 envelope_510 pivot_mem_510 child_required_sub_510 child_envelope_sub_510 ?_
  intro b hb
  exact common_sub_510 (mem_commonEnvelope childrenD_510 b hb)

theorem finite_children_work_513_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_513_i0 j) (childrenD_513_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_439 5 (5, 1)).mono (by decide +kernel)

theorem finite_row_works_513_i0 : FiniteTemplate HasSnaky 7 required_513_i0 envelope_513_i0 := by
  refine finite_compose HasSnaky 6 childrenC_513_i0 childrenD_513_i0 finite_children_work_513_i0 (0, 4)
    required_513_i0 envelope_513_i0 pivot_mem_513_i0 child_required_sub_513_i0 child_envelope_sub_513_i0 ?_
  intro b hb
  exact common_sub_513_i0 (mem_commonEnvelope childrenD_513_i0 b hb)

theorem finite_children_work_513 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_513 j) (childrenD_513 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_9.mono (by decide +kernel)
  · exact finite_row_works_513_i0.mono (by decide +kernel)

theorem finite_row_works_513 : FiniteTemplate HasSnaky 8 required_513 envelope_513 := by
  refine finite_compose HasSnaky 7 childrenC_513 childrenD_513 finite_children_work_513 (1, 4)
    required_513 envelope_513 pivot_mem_513 child_required_sub_513 child_envelope_sub_513 ?_
  intro b hb
  exact common_sub_513 (mem_commonEnvelope childrenD_513 b hb)

end FiniteCongruenceChecks.SnakyFinite
