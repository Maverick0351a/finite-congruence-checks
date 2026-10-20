/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part05
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height07Part04
import FiniteCards.Height08Part02
import FiniteCards.Height09Part02
import FiniteCards.Height09Part04
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height11Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_428 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_428 j) (childrenD_428 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_427 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_428 : FiniteTemplate HasSnaky 12 required_428 envelope_428 := by
  refine finite_compose HasSnaky 11 childrenC_428 childrenD_428 finite_children_work_428 (1, 4)
    required_428 envelope_428 pivot_mem_428 child_required_sub_428 child_envelope_sub_428 ?_
  intro b hb
  exact common_sub_428 (mem_commonEnvelope childrenD_428 b hb)

theorem finite_children_work_485_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_485_i0 j) (childrenD_485_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_81 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_204 4 (0, 8)).mono (by decide +kernel)
  · exact finite_row_works_353.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_481 4 (2, 8)).mono (by decide +kernel)

theorem finite_row_works_485_i0 : FiniteTemplate HasSnaky 11 required_485_i0 envelope_485_i0 := by
  refine finite_compose HasSnaky 10 childrenC_485_i0 childrenD_485_i0 finite_children_work_485_i0 (4, 5)
    required_485_i0 envelope_485_i0 pivot_mem_485_i0 child_required_sub_485_i0 child_envelope_sub_485_i0 ?_
  intro b hb
  exact common_sub_485_i0 (mem_commonEnvelope childrenD_485_i0 b hb)

theorem finite_children_work_485_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_485_i2 j) (childrenD_485_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_193 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_477 3 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_485_i2 : FiniteTemplate HasSnaky 10 required_485_i2 envelope_485_i2 := by
  refine finite_compose HasSnaky 9 childrenC_485_i2 childrenD_485_i2 finite_children_work_485_i2 (4, 4)
    required_485_i2 envelope_485_i2 pivot_mem_485_i2 child_required_sub_485_i2 child_envelope_sub_485_i2 ?_
  intro b hb
  exact common_sub_485_i2 (mem_commonEnvelope childrenD_485_i2 b hb)

theorem finite_children_work_485_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_485_i3 j) (childrenD_485_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_166 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 5 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_485_i3 : FiniteTemplate HasSnaky 7 required_485_i3 envelope_485_i3 := by
  refine finite_compose HasSnaky 6 childrenC_485_i3 childrenD_485_i3 finite_children_work_485_i3 (2, 4)
    required_485_i3 envelope_485_i3 pivot_mem_485_i3 child_required_sub_485_i3 child_envelope_sub_485_i3 ?_
  intro b hb
  exact common_sub_485_i3 (mem_commonEnvelope childrenD_485_i3 b hb)

theorem finite_children_work_485_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_485_i1 j) (childrenD_485_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_81 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_167 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_485_i2.mono (by decide +kernel)
  · exact finite_row_works_485_i3.mono (by decide +kernel)

theorem finite_row_works_485_i1 : FiniteTemplate HasSnaky 11 required_485_i1 envelope_485_i1 := by
  refine finite_compose HasSnaky 10 childrenC_485_i1 childrenD_485_i1 finite_children_work_485_i1 (4, 5)
    required_485_i1 envelope_485_i1 pivot_mem_485_i1 child_required_sub_485_i1 child_envelope_sub_485_i1 ?_
  intro b hb
  exact common_sub_485_i1 (mem_commonEnvelope childrenD_485_i1 b hb)

theorem finite_children_work_485 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_485 j) (childrenD_485 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_313 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_469 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_485_i0.mono (by decide +kernel)
  · exact finite_row_works_485_i1.mono (by decide +kernel)
  · exact finite_row_works_484.mono (by decide +kernel)

theorem finite_row_works_485 : FiniteTemplate HasSnaky 12 required_485 envelope_485 := by
  refine finite_compose HasSnaky 11 childrenC_485 childrenD_485 finite_children_work_485 (4, 3)
    required_485 envelope_485 pivot_mem_485 child_required_sub_485 child_envelope_sub_485 ?_
  intro b hb
  exact common_sub_485 (mem_commonEnvelope childrenD_485 b hb)

theorem finite_children_work_489_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_489_i1 j) (childrenD_489_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 6 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_486 3 (2, 8)).mono (by decide +kernel)

theorem finite_row_works_489_i1 : FiniteTemplate HasSnaky 7 required_489_i1 envelope_489_i1 := by
  refine finite_compose HasSnaky 6 childrenC_489_i1 childrenD_489_i1 finite_children_work_489_i1 (5, 7)
    required_489_i1 envelope_489_i1 pivot_mem_489_i1 child_required_sub_489_i1 child_envelope_sub_489_i1 ?_
  intro b hb
  exact common_sub_489_i1 (mem_commonEnvelope childrenD_489_i1 b hb)

theorem finite_children_work_489_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_489_i0 j) (childrenD_489_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_489_i1.mono (by decide +kernel)

theorem finite_row_works_489_i0 : FiniteTemplate HasSnaky 8 required_489_i0 envelope_489_i0 := by
  refine finite_compose HasSnaky 7 childrenC_489_i0 childrenD_489_i0 finite_children_work_489_i0 (5, 6)
    required_489_i0 envelope_489_i0 pivot_mem_489_i0 child_required_sub_489_i0 child_envelope_sub_489_i0 ?_
  intro b hb
  exact common_sub_489_i0 (mem_commonEnvelope childrenD_489_i0 b hb)

theorem finite_children_work_489_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_489_i2 j) (childrenD_489_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_81 0 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_167 0 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_481 5 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_488 1 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_489_i2 : FiniteTemplate HasSnaky 11 required_489_i2 envelope_489_i2 := by
  refine finite_compose HasSnaky 10 childrenC_489_i2 childrenD_489_i2 finite_children_work_489_i2 (5, 8)
    required_489_i2 envelope_489_i2 pivot_mem_489_i2 child_required_sub_489_i2 child_envelope_sub_489_i2 ?_
  intro b hb
  exact common_sub_489_i2 (mem_commonEnvelope childrenD_489_i2 b hb)

theorem finite_children_work_489 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_489 j) (childrenD_489 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_313 2 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_470 4 (1, 10)).mono (by decide +kernel)
  · exact finite_row_works_489_i0.mono (by decide +kernel)
  · exact finite_row_works_489_i2.mono (by decide +kernel)

theorem finite_row_works_489 : FiniteTemplate HasSnaky 12 required_489 envelope_489 := by
  refine finite_compose HasSnaky 11 childrenC_489 childrenD_489 finite_children_work_489 (3, 8)
    required_489 envelope_489 pivot_mem_489 child_required_sub_489 child_envelope_sub_489 ?_
  intro b hb
  exact common_sub_489 (mem_commonEnvelope childrenD_489 b hb)

theorem finite_children_work_543_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_543_i1 j) (childrenD_543_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_261 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_370 1 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_543_i1 : FiniteTemplate HasSnaky 6 required_543_i1 envelope_543_i1 := by
  refine finite_compose HasSnaky 5 childrenC_543_i1 childrenD_543_i1 finite_children_work_543_i1 (5, 7)
    required_543_i1 envelope_543_i1 pivot_mem_543_i1 child_required_sub_543_i1 child_envelope_sub_543_i1 ?_
  intro b hb
  exact common_sub_543_i1 (mem_commonEnvelope childrenD_543_i1 b hb)

theorem finite_children_work_543_i6 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_543_i6 j) (childrenD_543_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_154 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_170 0 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_543_i6 : FiniteTemplate HasSnaky 3 required_543_i6 envelope_543_i6 := by
  refine finite_compose HasSnaky 2 childrenC_543_i6 childrenD_543_i6 finite_children_work_543_i6 (5, 5)
    required_543_i6 envelope_543_i6 pivot_mem_543_i6 child_required_sub_543_i6 child_envelope_sub_543_i6 ?_
  intro b hb
  exact common_sub_543_i6 (mem_commonEnvelope childrenD_543_i6 b hb)

theorem finite_children_work_543_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_543_i5 j) (childrenD_543_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 6 (5, 7)).mono (by decide +kernel)
  · exact finite_row_works_543_i6.mono (by decide +kernel)

theorem finite_row_works_543_i5 : FiniteTemplate HasSnaky 4 required_543_i5 envelope_543_i5 := by
  refine finite_compose HasSnaky 3 childrenC_543_i5 childrenD_543_i5 finite_children_work_543_i5 (5, 7)
    required_543_i5 envelope_543_i5 pivot_mem_543_i5 child_required_sub_543_i5 child_envelope_sub_543_i5 ?_
  intro b hb
  exact common_sub_543_i5 (mem_commonEnvelope childrenD_543_i5 b hb)

theorem finite_children_work_543_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_543_i4 j) (childrenD_543_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 0 (2, 7)).mono (by decide +kernel)
  · exact finite_row_works_543_i5.mono (by decide +kernel)

theorem finite_row_works_543_i4 : FiniteTemplate HasSnaky 5 required_543_i4 envelope_543_i4 := by
  refine finite_compose HasSnaky 4 childrenC_543_i4 childrenD_543_i4 finite_children_work_543_i4 (3, 7)
    required_543_i4 envelope_543_i4 pivot_mem_543_i4 child_required_sub_543_i4 child_envelope_sub_543_i4 ?_
  intro b hb
  exact common_sub_543_i4 (mem_commonEnvelope childrenD_543_i4 b hb)

theorem finite_children_work_543_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_543_i3 j) (childrenD_543_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (2, 10)).mono (by decide +kernel)
  · exact finite_row_works_543_i4.mono (by decide +kernel)

theorem finite_row_works_543_i3 : FiniteTemplate HasSnaky 6 required_543_i3 envelope_543_i3 := by
  refine finite_compose HasSnaky 5 childrenC_543_i3 childrenD_543_i3 finite_children_work_543_i3 (1, 6)
    required_543_i3 envelope_543_i3 pivot_mem_543_i3 child_required_sub_543_i3 child_envelope_sub_543_i3 ?_
  intro b hb
  exact common_sub_543_i3 (mem_commonEnvelope childrenD_543_i3 b hb)

theorem finite_children_work_543_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_543_i2 j) (childrenD_543_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_543_i3.mono (by decide +kernel)

theorem finite_row_works_543_i2 : FiniteTemplate HasSnaky 7 required_543_i2 envelope_543_i2 := by
  refine finite_compose HasSnaky 6 childrenC_543_i2 childrenD_543_i2 finite_children_work_543_i2 (2, 10)
    required_543_i2 envelope_543_i2 pivot_mem_543_i2 child_required_sub_543_i2 child_envelope_sub_543_i2 ?_
  intro b hb
  exact common_sub_543_i2 (mem_commonEnvelope childrenD_543_i2 b hb)

theorem finite_children_work_543_i7 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_543_i7 j) (childrenD_543_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_539 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_543_i7 : FiniteTemplate HasSnaky 10 required_543_i7 envelope_543_i7 := by
  refine finite_compose HasSnaky 9 childrenC_543_i7 childrenD_543_i7 finite_children_work_543_i7 (2, 10)
    required_543_i7 envelope_543_i7 pivot_mem_543_i7 child_required_sub_543_i7 child_envelope_sub_543_i7 ?_
  intro b hb
  exact common_sub_543_i7 (mem_commonEnvelope childrenD_543_i7 b hb)

theorem finite_children_work_543_i8 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_543_i8 j) (childrenD_543_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_86 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_542 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_543_i8 : FiniteTemplate HasSnaky 8 required_543_i8 envelope_543_i8 := by
  refine finite_compose HasSnaky 7 childrenC_543_i8 childrenD_543_i8 finite_children_work_543_i8 (4, 6)
    required_543_i8 envelope_543_i8 pivot_mem_543_i8 child_required_sub_543_i8 child_envelope_sub_543_i8 ?_
  intro b hb
  exact common_sub_543_i8 (mem_commonEnvelope childrenD_543_i8 b hb)

theorem finite_children_work_543_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_543_i0 j) (childrenD_543_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_433 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_543_i1.mono (by decide +kernel)
  · exact finite_row_works_543_i2.mono (by decide +kernel)
  · exact finite_row_works_543_i7.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_540 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_541 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_543_i8.mono (by decide +kernel)

theorem finite_row_works_543_i0 : FiniteTemplate HasSnaky 11 required_543_i0 envelope_543_i0 := by
  refine finite_compose HasSnaky 10 childrenC_543_i0 childrenD_543_i0 finite_children_work_543_i0 (4, 5)
    required_543_i0 envelope_543_i0 pivot_mem_543_i0 child_required_sub_543_i0 child_envelope_sub_543_i0 ?_
  intro b hb
  exact common_sub_543_i0 (mem_commonEnvelope childrenD_543_i0 b hb)

theorem finite_children_work_543_i10 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_543_i10 j) (childrenD_543_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 7 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_543_i10 : FiniteTemplate HasSnaky 2 required_543_i10 envelope_543_i10 := by
  refine finite_compose HasSnaky 1 childrenC_543_i10 childrenD_543_i10 finite_children_work_543_i10 (2, 5)
    required_543_i10 envelope_543_i10 pivot_mem_543_i10 child_required_sub_543_i10 child_envelope_sub_543_i10 ?_
  intro b hb
  exact common_sub_543_i10 (mem_commonEnvelope childrenD_543_i10 b hb)

theorem finite_children_work_543_i9 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_543_i9 j) (childrenD_543_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_278 1 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_543_i10.mono (by decide +kernel)

theorem finite_row_works_543_i9 : FiniteTemplate HasSnaky 6 required_543_i9 envelope_543_i9 := by
  refine finite_compose HasSnaky 5 childrenC_543_i9 childrenD_543_i9 finite_children_work_543_i9 (3, 8)
    required_543_i9 envelope_543_i9 pivot_mem_543_i9 child_required_sub_543_i9 child_envelope_sub_543_i9 ?_
  intro b hb
  exact common_sub_543_i9 (mem_commonEnvelope childrenD_543_i9 b hb)

theorem finite_children_work_543 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_543 j) (childrenD_543 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_280 0 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_543_i0.mono (by decide +kernel)
  · exact finite_row_works_543_i9.mono (by decide +kernel)

theorem finite_row_works_543 : FiniteTemplate HasSnaky 12 required_543 envelope_543 := by
  refine finite_compose HasSnaky 11 childrenC_543 childrenD_543 finite_children_work_543 (2, 9)
    required_543 envelope_543 pivot_mem_543 child_required_sub_543 child_envelope_sub_543 ?_
  intro b hb
  exact common_sub_543 (mem_commonEnvelope childrenD_543 b hb)

end FiniteCongruenceChecks.SnakyFinite
