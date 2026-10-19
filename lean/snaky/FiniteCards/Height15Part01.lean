/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part03
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height08Part04
import FiniteCards.Height09Part02
import FiniteCards.Height10Part01
import FiniteCards.Height10Part03
import FiniteCards.Height10Part04
import FiniteCards.Height10Part06
import FiniteCards.Height11Part02
import FiniteCards.Height12Part02
import FiniteCards.Height12Part03
import FiniteCards.Height12Part04
import FiniteCards.Height13Part01
import FiniteCards.Height13Part02
import FiniteCards.Height13Part03
import FiniteCards.Height13Part04
import FiniteCards.Height14Part01
import FiniteCards.Height14Part02
import FiniteCards.Height14Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_573_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_573_i0 j) (childrenD_573_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 5 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_286 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_339 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_573_i0 : FiniteTemplate HasSnaky 8 required_573_i0 envelope_573_i0 := by
  refine finite_compose HasSnaky 7 childrenC_573_i0 childrenD_573_i0 finite_children_work_573_i0 (3, 5)
    required_573_i0 envelope_573_i0 pivot_mem_573_i0 child_required_sub_573_i0 child_envelope_sub_573_i0 ?_
  intro b hb
  exact common_sub_573_i0 (mem_commonEnvelope childrenD_573_i0 b hb)

theorem finite_children_work_573_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_573_i1 j) (childrenD_573_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_473 3 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_573_i1 : FiniteTemplate HasSnaky 9 required_573_i1 envelope_573_i1 := by
  refine finite_compose HasSnaky 8 childrenC_573_i1 childrenD_573_i1 finite_children_work_573_i1 (3, 5)
    required_573_i1 envelope_573_i1 pivot_mem_573_i1 child_required_sub_573_i1 child_envelope_sub_573_i1 ?_
  intro b hb
  exact common_sub_573_i1 (mem_commonEnvelope childrenD_573_i1 b hb)

theorem finite_children_work_573_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_573_i2 j) (childrenD_573_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_403 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_487 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_492 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_573_i2 : FiniteTemplate HasSnaky 8 required_573_i2 envelope_573_i2 := by
  refine finite_compose HasSnaky 7 childrenC_573_i2 childrenD_573_i2 finite_children_work_573_i2 (3, 5)
    required_573_i2 envelope_573_i2 pivot_mem_573_i2 child_required_sub_573_i2 child_envelope_sub_573_i2 ?_
  intro b hb
  exact common_sub_573_i2 (mem_commonEnvelope childrenD_573_i2 b hb)

theorem finite_children_work_573_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_573_i3 j) (childrenD_573_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_87 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_487 0 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_573_i3 : FiniteTemplate HasSnaky 8 required_573_i3 envelope_573_i3 := by
  refine finite_compose HasSnaky 7 childrenC_573_i3 childrenD_573_i3 finite_children_work_573_i3 (3, 5)
    required_573_i3 envelope_573_i3 pivot_mem_573_i3 child_required_sub_573_i3 child_envelope_sub_573_i3 ?_
  intro b hb
  exact common_sub_573_i3 (mem_commonEnvelope childrenD_573_i3 b hb)

theorem finite_children_work_573_i4 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_573_i4 j) (childrenD_573_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_107 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_572.mono (by decide +kernel)

theorem finite_row_works_573_i4 : FiniteTemplate HasSnaky 14 required_573_i4 envelope_573_i4 := by
  refine finite_compose HasSnaky 13 childrenC_573_i4 childrenD_573_i4 finite_children_work_573_i4 (1, 7)
    required_573_i4 envelope_573_i4 pivot_mem_573_i4 child_required_sub_573_i4 child_envelope_sub_573_i4 ?_
  intro b hb
  exact common_sub_573_i4 (mem_commonEnvelope childrenD_573_i4 b hb)

theorem finite_children_work_573_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_573_i5 j) (childrenD_573_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_249 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_383 7 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_403 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_573_i5 : FiniteTemplate HasSnaky 7 required_573_i5 envelope_573_i5 := by
  refine finite_compose HasSnaky 6 childrenC_573_i5 childrenD_573_i5 finite_children_work_573_i5 (3, 5)
    required_573_i5 envelope_573_i5 pivot_mem_573_i5 child_required_sub_573_i5 child_envelope_sub_573_i5 ?_
  intro b hb
  exact common_sub_573_i5 (mem_commonEnvelope childrenD_573_i5 b hb)

theorem finite_children_work_573 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_573 j) (childrenD_573 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_384 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_385 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_493 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_494 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_573_i0.mono (by decide +kernel)
  · exact finite_row_works_573_i1.mono (by decide +kernel)
  · exact finite_row_works_573_i2.mono (by decide +kernel)
  · exact finite_row_works_573_i3.mono (by decide +kernel)
  · exact finite_row_works_573_i4.mono (by decide +kernel)
  · exact finite_row_works_573_i5.mono (by decide +kernel)

theorem finite_row_works_573 : FiniteTemplate HasSnaky 15 required_573 envelope_573 := by
  refine finite_compose HasSnaky 14 childrenC_573 childrenD_573 finite_children_work_573 (3, 6)
    required_573 envelope_573 pivot_mem_573 child_required_sub_573 child_envelope_sub_573 ?_
  intro b hb
  exact common_sub_573 (mem_commonEnvelope childrenD_573 b hb)

theorem finite_children_work_583_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_583_i2 j) (childrenD_583_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_576 4 (2, 10)).mono (by decide +kernel)

theorem finite_row_works_583_i2 : FiniteTemplate HasSnaky 8 required_583_i2 envelope_583_i2 := by
  refine finite_compose HasSnaky 7 childrenC_583_i2 childrenD_583_i2 finite_children_work_583_i2 (9, 6)
    required_583_i2 envelope_583_i2 pivot_mem_583_i2 child_required_sub_583_i2 child_envelope_sub_583_i2 ?_
  intro b hb
  exact common_sub_583_i2 (mem_commonEnvelope childrenD_583_i2 b hb)

theorem finite_children_work_583_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_583_i3 j) (childrenD_583_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_576 4 (2, 10)).mono (by decide +kernel)

theorem finite_row_works_583_i3 : FiniteTemplate HasSnaky 8 required_583_i3 envelope_583_i3 := by
  refine finite_compose HasSnaky 7 childrenC_583_i3 childrenD_583_i3 finite_children_work_583_i3 (9, 6)
    required_583_i3 envelope_583_i3 pivot_mem_583_i3 child_required_sub_583_i3 child_envelope_sub_583_i3 ?_
  intro b hb
  exact common_sub_583_i3 (mem_commonEnvelope childrenD_583_i3 b hb)

theorem finite_children_work_583_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_583_i1 j) (childrenD_583_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 4 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 4 (5, 10)).mono (by decide +kernel)
  · exact finite_row_works_583_i2.mono (by decide +kernel)
  · exact finite_row_works_583_i3.mono (by decide +kernel)

theorem finite_row_works_583_i1 : FiniteTemplate HasSnaky 9 required_583_i1 envelope_583_i1 := by
  refine finite_compose HasSnaky 8 childrenC_583_i1 childrenD_583_i1 finite_children_work_583_i1 (8, 6)
    required_583_i1 envelope_583_i1 pivot_mem_583_i1 child_required_sub_583_i1 child_envelope_sub_583_i1 ?_
  intro b hb
  exact common_sub_583_i1 (mem_commonEnvelope childrenD_583_i1 b hb)

theorem finite_children_work_583_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_583_i0 j) (childrenD_583_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (7, 6)).mono (by decide +kernel)
  · exact finite_row_works_583_i1.mono (by decide +kernel)

theorem finite_row_works_583_i0 : FiniteTemplate HasSnaky 10 required_583_i0 envelope_583_i0 := by
  refine finite_compose HasSnaky 9 childrenC_583_i0 childrenD_583_i0 finite_children_work_583_i0 (5, 6)
    required_583_i0 envelope_583_i0 pivot_mem_583_i0 child_required_sub_583_i0 child_envelope_sub_583_i0 ?_
  intro b hb
  exact common_sub_583_i0 (mem_commonEnvelope childrenD_583_i0 b hb)

theorem finite_children_work_583_i5 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_583_i5 j) (childrenD_583_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_86 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_542 1 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_583_i5 : FiniteTemplate HasSnaky 8 required_583_i5 envelope_583_i5 := by
  refine finite_compose HasSnaky 7 childrenC_583_i5 childrenD_583_i5 finite_children_work_583_i5 (5, 8)
    required_583_i5 envelope_583_i5 pivot_mem_583_i5 child_required_sub_583_i5 child_envelope_sub_583_i5 ?_
  intro b hb
  exact common_sub_583_i5 (mem_commonEnvelope childrenD_583_i5 b hb)

theorem finite_children_work_583_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_583_i6 j) (childrenD_583_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_48 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_109 0 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_246 2 (7, 5)).mono (by decide +kernel)

theorem finite_row_works_583_i6 : FiniteTemplate HasSnaky 5 required_583_i6 envelope_583_i6 := by
  refine finite_compose HasSnaky 4 childrenC_583_i6 childrenD_583_i6 finite_children_work_583_i6 (6, 7)
    required_583_i6 envelope_583_i6 pivot_mem_583_i6 child_required_sub_583_i6 child_envelope_sub_583_i6 ?_
  intro b hb
  exact common_sub_583_i6 (mem_commonEnvelope childrenD_583_i6 b hb)

theorem finite_children_work_583_i4 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_583_i4 j) (childrenD_583_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_184 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_423 2 (7, 5)).mono (by decide +kernel)
  · exact finite_row_works_583_i5.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_572 1 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_583_i6.mono (by decide +kernel)

theorem finite_row_works_583_i4 : FiniteTemplate HasSnaky 14 required_583_i4 envelope_583_i4 := by
  refine finite_compose HasSnaky 13 childrenC_583_i4 childrenD_583_i4 finite_children_work_583_i4 (6, 8)
    required_583_i4 envelope_583_i4 pivot_mem_583_i4 child_required_sub_583_i4 child_envelope_sub_583_i4 ?_
  intro b hb
  exact common_sub_583_i4 (mem_commonEnvelope childrenD_583_i4 b hb)

theorem finite_children_work_583 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_583 j) (childrenD_583 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_401 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_552 4 (0, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_556 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_575 0 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_583_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_579 4 (5, 10)).mono (by decide +kernel)
  · exact finite_row_works_583_i4.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_582 1 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_583 : FiniteTemplate HasSnaky 15 required_583 envelope_583 := by
  refine finite_compose HasSnaky 14 childrenC_583 childrenD_583 finite_children_work_583 (7, 6)
    required_583 envelope_583 pivot_mem_583 child_required_sub_583 child_envelope_sub_583 ?_
  intro b hb
  exact common_sub_583 (mem_commonEnvelope childrenD_583 b hb)

theorem finite_children_work_648 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_648 j) (childrenD_648 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_174 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_480 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_480 2 (7, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_483 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_566 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_635 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_644.mono (by decide +kernel)
  · exact finite_row_works_647.mono (by decide +kernel)

theorem finite_row_works_648 : FiniteTemplate HasSnaky 15 required_648 envelope_648 := by
  refine finite_compose HasSnaky 14 childrenC_648 childrenD_648 finite_children_work_648 (4, 4)
    required_648 envelope_648 pivot_mem_648 child_required_sub_648 child_envelope_sub_648 ?_
  intro b hb
  exact common_sub_648 (mem_commonEnvelope childrenD_648 b hb)

theorem finite_children_work_656_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_656_i1 j) (childrenD_656_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_117 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_337 6 (6, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_341 6 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 3 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_656_i1 : FiniteTemplate HasSnaky 9 required_656_i1 envelope_656_i1 := by
  refine finite_compose HasSnaky 8 childrenC_656_i1 childrenD_656_i1 finite_children_work_656_i1 (5, 4)
    required_656_i1 envelope_656_i1 pivot_mem_656_i1 child_required_sub_656_i1 child_envelope_sub_656_i1 ?_
  intro b hb
  exact common_sub_656_i1 (mem_commonEnvelope childrenD_656_i1 b hb)

theorem finite_children_work_656_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_656_i2 j) (childrenD_656_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_651 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_656_i2 : FiniteTemplate HasSnaky 9 required_656_i2 envelope_656_i2 := by
  refine finite_compose HasSnaky 8 childrenC_656_i2 childrenD_656_i2 finite_children_work_656_i2 (4, 5)
    required_656_i2 envelope_656_i2 pivot_mem_656_i2 child_required_sub_656_i2 child_envelope_sub_656_i2 ?_
  intro b hb
  exact common_sub_656_i2 (mem_commonEnvelope childrenD_656_i2 b hb)

theorem finite_children_work_656_i3 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_656_i3 j) (childrenD_656_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_652 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_656_i3 : FiniteTemplate HasSnaky 11 required_656_i3 envelope_656_i3 := by
  refine finite_compose HasSnaky 10 childrenC_656_i3 childrenD_656_i3 finite_children_work_656_i3 (4, 5)
    required_656_i3 envelope_656_i3 pivot_mem_656_i3 child_required_sub_656_i3 child_envelope_sub_656_i3 ?_
  intro b hb
  exact common_sub_656_i3 (mem_commonEnvelope childrenD_656_i3 b hb)

theorem finite_children_work_656_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_656_i0 j) (childrenD_656_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_248 6 (7, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_300 6 (7, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_436 6 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_449 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_510 3 (2, 8)).mono (by decide +kernel)
  · exact finite_row_works_656_i1.mono (by decide +kernel)
  · exact finite_row_works_656_i2.mono (by decide +kernel)
  · exact finite_row_works_656_i3.mono (by decide +kernel)

theorem finite_row_works_656_i0 : FiniteTemplate HasSnaky 12 required_656_i0 envelope_656_i0 := by
  refine finite_compose HasSnaky 11 childrenC_656_i0 childrenD_656_i0 finite_children_work_656_i0 (5, 5)
    required_656_i0 envelope_656_i0 pivot_mem_656_i0 child_required_sub_656_i0 child_envelope_sub_656_i0 ?_
  intro b hb
  exact common_sub_656_i0 (mem_commonEnvelope childrenD_656_i0 b hb)

theorem finite_children_work_656 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_656 j) (childrenD_656 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_508 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_508 4 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 4 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_644 5 (10, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_645 5 (10, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_647 5 (10, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 4 (2, 11)).mono (by decide +kernel)
  · exact finite_row_works_656_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_654 5 (9, 3)).mono (by decide +kernel)

theorem finite_row_works_656 : FiniteTemplate HasSnaky 15 required_656 envelope_656 := by
  refine finite_compose HasSnaky 14 childrenC_656 childrenD_656 finite_children_work_656 (6, 6)
    required_656 envelope_656 pivot_mem_656 child_required_sub_656 child_envelope_sub_656 ?_
  intro b hb
  exact common_sub_656 (mem_commonEnvelope childrenD_656 b hb)

end FiniteCongruenceChecks.SnakyFinite
