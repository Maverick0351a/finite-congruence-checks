/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height09Part02
import FiniteCards.Height10Part01
import FiniteCards.Height10Part03
import FiniteCards.Height11Part01
import FiniteCards.Height11Part02
import FiniteCards.Height11Part03
import FiniteCards.Height11Part05
import FiniteCards.Height12Part02
import FiniteCards.Height12Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_591_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_591_i0 j) (childrenD_591_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_265 1 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_591_i0 : FiniteTemplate HasSnaky 6 required_591_i0 envelope_591_i0 := by
  refine finite_compose HasSnaky 5 childrenC_591_i0 childrenD_591_i0 finite_children_work_591_i0 (3, 6)
    required_591_i0 envelope_591_i0 pivot_mem_591_i0 child_required_sub_591_i0 child_envelope_sub_591_i0 ?_
  intro b hb
  exact common_sub_591_i0 (mem_commonEnvelope childrenD_591_i0 b hb)

theorem finite_children_work_591_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_591_i1 j) (childrenD_591_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_13 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_289 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 3 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_591_i1 : FiniteTemplate HasSnaky 7 required_591_i1 envelope_591_i1 := by
  refine finite_compose HasSnaky 6 childrenC_591_i1 childrenD_591_i1 finite_children_work_591_i1 (4, 4)
    required_591_i1 envelope_591_i1 pivot_mem_591_i1 child_required_sub_591_i1 child_envelope_sub_591_i1 ?_
  intro b hb
  exact common_sub_591_i1 (mem_commonEnvelope childrenD_591_i1 b hb)

theorem finite_children_work_591_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_591_i4 j) (childrenD_591_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_80 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_591_i4 : FiniteTemplate HasSnaky 5 required_591_i4 envelope_591_i4 := by
  refine finite_compose HasSnaky 4 childrenC_591_i4 childrenD_591_i4 finite_children_work_591_i4 (3, 5)
    required_591_i4 envelope_591_i4 pivot_mem_591_i4 child_required_sub_591_i4 child_envelope_sub_591_i4 ?_
  intro b hb
  exact common_sub_591_i4 (mem_commonEnvelope childrenD_591_i4 b hb)

theorem finite_children_work_591_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_591_i3 j) (childrenD_591_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_109 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_157 7 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_591_i4.mono (by decide +kernel)

theorem finite_row_works_591_i3 : FiniteTemplate HasSnaky 6 required_591_i3 envelope_591_i3 := by
  refine finite_compose HasSnaky 5 childrenC_591_i3 childrenD_591_i3 finite_children_work_591_i3 (4, 3)
    required_591_i3 envelope_591_i3 pivot_mem_591_i3 child_required_sub_591_i3 child_envelope_sub_591_i3 ?_
  intro b hb
  exact common_sub_591_i3 (mem_commonEnvelope childrenD_591_i3 b hb)

theorem finite_children_work_591_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_591_i5 j) (childrenD_591_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_271 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_591_i5 : FiniteTemplate HasSnaky 6 required_591_i5 envelope_591_i5 := by
  refine finite_compose HasSnaky 5 childrenC_591_i5 childrenD_591_i5 finite_children_work_591_i5 (4, 3)
    required_591_i5 envelope_591_i5 pivot_mem_591_i5 child_required_sub_591_i5 child_envelope_sub_591_i5 ?_
  intro b hb
  exact common_sub_591_i5 (mem_commonEnvelope childrenD_591_i5 b hb)

theorem finite_children_work_591_i2 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_591_i2 j) (childrenD_591_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_356 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_591_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_586 1 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_591_i5.mono (by decide +kernel)

theorem finite_row_works_591_i2 : FiniteTemplate HasSnaky 12 required_591_i2 envelope_591_i2 := by
  refine finite_compose HasSnaky 11 childrenC_591_i2 childrenD_591_i2 finite_children_work_591_i2 (4, 4)
    required_591_i2 envelope_591_i2 pivot_mem_591_i2 child_required_sub_591_i2 child_envelope_sub_591_i2 ?_
  intro b hb
  exact common_sub_591_i2 (mem_commonEnvelope childrenD_591_i2 b hb)

theorem finite_children_work_591 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_591 j) (childrenD_591 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_42 1 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_430 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_591_i0.mono (by decide +kernel)
  · exact finite_row_works_591_i1.mono (by decide +kernel)
  · exact finite_row_works_591_i2.mono (by decide +kernel)

theorem finite_row_works_591 : FiniteTemplate HasSnaky 13 required_591 envelope_591 := by
  refine finite_compose HasSnaky 12 childrenC_591 childrenD_591 finite_children_work_591 (4, 6)
    required_591 envelope_591 pivot_mem_591 child_required_sub_591 child_envelope_sub_591 ?_
  intro b hb
  exact common_sub_591 (mem_commonEnvelope childrenD_591 b hb)

theorem finite_children_work_597_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_597_i0 j) (childrenD_597_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (6, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_109 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_291 0 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_597_i0 : FiniteTemplate HasSnaky 5 required_597_i0 envelope_597_i0 := by
  refine finite_compose HasSnaky 4 childrenC_597_i0 childrenD_597_i0 finite_children_work_597_i0 (5, 4)
    required_597_i0 envelope_597_i0 pivot_mem_597_i0 child_required_sub_597_i0 child_envelope_sub_597_i0 ?_
  intro b hb
  exact common_sub_597_i0 (mem_commonEnvelope childrenD_597_i0 b hb)

theorem finite_children_work_597_i3 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_597_i3 j) (childrenD_597_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_597_i3 : FiniteTemplate HasSnaky 2 required_597_i3 envelope_597_i3 := by
  refine finite_compose HasSnaky 1 childrenC_597_i3 childrenD_597_i3 finite_children_work_597_i3 (4, 2)
    required_597_i3 envelope_597_i3 pivot_mem_597_i3 child_required_sub_597_i3 child_envelope_sub_597_i3 ?_
  intro b hb
  exact common_sub_597_i3 (mem_commonEnvelope childrenD_597_i3 b hb)

theorem finite_children_work_597_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_597_i2 j) (childrenD_597_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_597_i3.mono (by decide +kernel)

theorem finite_row_works_597_i2 : FiniteTemplate HasSnaky 4 required_597_i2 envelope_597_i2 := by
  refine finite_compose HasSnaky 3 childrenC_597_i2 childrenD_597_i2 finite_children_work_597_i2 (5, 2)
    required_597_i2 envelope_597_i2 pivot_mem_597_i2 child_required_sub_597_i2 child_envelope_sub_597_i2 ?_
  intro b hb
  exact common_sub_597_i2 (mem_commonEnvelope childrenD_597_i2 b hb)

theorem finite_children_work_597_i6 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_597_i6 j) (childrenD_597_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_4 3 (5, 5)).mono (by decide +kernel)

theorem finite_row_works_597_i6 : FiniteTemplate HasSnaky 2 required_597_i6 envelope_597_i6 := by
  refine finite_compose HasSnaky 1 childrenC_597_i6 childrenD_597_i6 finite_children_work_597_i6 (6, 1)
    required_597_i6 envelope_597_i6 pivot_mem_597_i6 child_required_sub_597_i6 child_envelope_sub_597_i6 ?_
  intro b hb
  exact common_sub_597_i6 (mem_commonEnvelope childrenD_597_i6 b hb)

theorem finite_children_work_597_i5 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_597_i5 j) (childrenD_597_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (5, 2)).mono (by decide +kernel)
  · exact finite_row_works_597_i6.mono (by decide +kernel)

theorem finite_row_works_597_i5 : FiniteTemplate HasSnaky 3 required_597_i5 envelope_597_i5 := by
  refine finite_compose HasSnaky 2 childrenC_597_i5 childrenD_597_i5 finite_children_work_597_i5 (5, 2)
    required_597_i5 envelope_597_i5 pivot_mem_597_i5 child_required_sub_597_i5 child_envelope_sub_597_i5 ?_
  intro b hb
  exact common_sub_597_i5 (mem_commonEnvelope childrenD_597_i5 b hb)

theorem finite_children_work_597_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_597_i4 j) (childrenD_597_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_140 6 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_597_i5.mono (by decide +kernel)

theorem finite_row_works_597_i4 : FiniteTemplate HasSnaky 4 required_597_i4 envelope_597_i4 := by
  refine finite_compose HasSnaky 3 childrenC_597_i4 childrenD_597_i4 finite_children_work_597_i4 (4, 2)
    required_597_i4 envelope_597_i4 pivot_mem_597_i4 child_required_sub_597_i4 child_envelope_sub_597_i4 ?_
  intro b hb
  exact common_sub_597_i4 (mem_commonEnvelope childrenD_597_i4 b hb)

theorem finite_children_work_597_i1 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_597_i1 j) (childrenD_597_i1 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_597_i2.mono (by decide +kernel)
  · exact finite_row_works_597_i4.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_596 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_597_i1 : FiniteTemplate HasSnaky 12 required_597_i1 envelope_597_i1 := by
  refine finite_compose HasSnaky 11 childrenC_597_i1 childrenD_597_i1 finite_children_work_597_i1 (5, 4)
    required_597_i1 envelope_597_i1 pivot_mem_597_i1 child_required_sub_597_i1 child_envelope_sub_597_i1 ?_
  intro b hb
  exact common_sub_597_i1 (mem_commonEnvelope childrenD_597_i1 b hb)

theorem finite_children_work_597 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_597 j) (childrenD_597 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_272 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_290 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_593 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_597_i0.mono (by decide +kernel)
  · exact finite_row_works_597_i1.mono (by decide +kernel)

theorem finite_row_works_597 : FiniteTemplate HasSnaky 13 required_597 envelope_597 := by
  refine finite_compose HasSnaky 12 childrenC_597 childrenD_597 finite_children_work_597 (5, 5)
    required_597 envelope_597 pivot_mem_597 child_required_sub_597 child_envelope_sub_597 ?_
  intro b hb
  exact common_sub_597 (mem_commonEnvelope childrenD_597 b hb)

theorem finite_children_work_603_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_603_i0 j) (childrenD_603_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_427 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_603_i0 : FiniteTemplate HasSnaky 12 required_603_i0 envelope_603_i0 := by
  refine finite_compose HasSnaky 11 childrenC_603_i0 childrenD_603_i0 finite_children_work_603_i0 (1, 2)
    required_603_i0 envelope_603_i0 pivot_mem_603_i0 child_required_sub_603_i0 child_envelope_sub_603_i0 ?_
  intro b hb
  exact common_sub_603_i0 (mem_commonEnvelope childrenD_603_i0 b hb)

theorem finite_children_work_603 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_603 j) (childrenD_603 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 6 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_603_i0.mono (by decide +kernel)

theorem finite_row_works_603 : FiniteTemplate HasSnaky 13 required_603 envelope_603 := by
  refine finite_compose HasSnaky 12 childrenC_603 childrenD_603 finite_children_work_603 (1, 5)
    required_603 envelope_603 pivot_mem_603 child_required_sub_603 child_envelope_sub_603 ?_
  intro b hb
  exact common_sub_603 (mem_commonEnvelope childrenD_603 b hb)

theorem finite_children_work_634 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_634 j) (childrenD_634 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_438 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_452 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 7 (6, 5)).mono (by decide +kernel)
  · exact finite_row_works_633.mono (by decide +kernel)

theorem finite_row_works_634 : FiniteTemplate HasSnaky 13 required_634 envelope_634 := by
  refine finite_compose HasSnaky 12 childrenC_634 childrenD_634 finite_children_work_634 (5, 5)
    required_634 envelope_634 pivot_mem_634 child_required_sub_634 child_envelope_sub_634 ?_
  intro b hb
  exact common_sub_634 (mem_commonEnvelope childrenD_634 b hb)

theorem finite_children_work_642 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_642 j) (childrenD_642 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_299 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_349 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_476 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_641 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_642 : FiniteTemplate HasSnaky 13 required_642 envelope_642 := by
  refine finite_compose HasSnaky 12 childrenC_642 childrenD_642 finite_children_work_642 (3, 5)
    required_642 envelope_642 pivot_mem_642 child_required_sub_642 child_envelope_sub_642 ?_
  intro b hb
  exact common_sub_642 (mem_commonEnvelope childrenD_642 b hb)

theorem finite_children_work_643 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_643 j) (childrenD_643 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_299 4 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_349 4 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_476 4 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_641 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_643 : FiniteTemplate HasSnaky 13 required_643 envelope_643 := by
  refine finite_compose HasSnaky 12 childrenC_643 childrenD_643 finite_children_work_643 (3, 5)
    required_643 envelope_643 pivot_mem_643 child_required_sub_643 child_envelope_sub_643 ?_
  intro b hb
  exact common_sub_643 (mem_commonEnvelope childrenD_643 b hb)

theorem finite_children_work_647_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_647_i1 j) (childrenD_647_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 7 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_65 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_282 6 (6, 7)).mono (by decide +kernel)

theorem finite_row_works_647_i1 : FiniteTemplate HasSnaky 6 required_647_i1 envelope_647_i1 := by
  refine finite_compose HasSnaky 5 childrenC_647_i1 childrenD_647_i1 finite_children_work_647_i1 (6, 5)
    required_647_i1 envelope_647_i1 pivot_mem_647_i1 child_required_sub_647_i1 child_envelope_sub_647_i1 ?_
  intro b hb
  exact common_sub_647_i1 (mem_commonEnvelope childrenD_647_i1 b hb)

theorem finite_children_work_647_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_647_i0 j) (childrenD_647_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_600 5 (8, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_600 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_621 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_647_i1.mono (by decide +kernel)

theorem finite_row_works_647_i0 : FiniteTemplate HasSnaky 8 required_647_i0 envelope_647_i0 := by
  refine finite_compose HasSnaky 7 childrenC_647_i0 childrenD_647_i0 finite_children_work_647_i0 (5, 5)
    required_647_i0 envelope_647_i0 pivot_mem_647_i0 child_required_sub_647_i0 child_envelope_sub_647_i0 ?_
  intro b hb
  exact common_sub_647_i0 (mem_commonEnvelope childrenD_647_i0 b hb)

theorem finite_children_work_647 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_647 j) (childrenD_647 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_399 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_408 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_410 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_480 5 (9, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_546 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_635 7 (9, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_646 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_647_i0.mono (by decide +kernel)

theorem finite_row_works_647 : FiniteTemplate HasSnaky 13 required_647 envelope_647 := by
  refine finite_compose HasSnaky 12 childrenC_647 childrenD_647 finite_children_work_647 (5, 4)
    required_647 envelope_647 pivot_mem_647 child_required_sub_647 child_envelope_sub_647 ?_
  intro b hb
  exact common_sub_647 (mem_commonEnvelope childrenD_647 b hb)

end FiniteCongruenceChecks.SnakyFinite
