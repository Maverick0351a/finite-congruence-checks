/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part03
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03
import FiniteCards.Height09Part04
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height10Part03
import FiniteCards.Height11Part02
import FiniteCards.Height12Part01
import FiniteCards.Height12Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_462 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_462 j) (childrenD_462 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 6 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_428 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_462 : FiniteTemplate HasSnaky 13 required_462 envelope_462 := by
  refine finite_compose HasSnaky 12 childrenC_462 childrenD_462 finite_children_work_462 (1, 5)
    required_462 envelope_462 pivot_mem_462 child_required_sub_462 child_envelope_sub_462 ?_
  intro b hb
  exact common_sub_462 (mem_commonEnvelope childrenD_462 b hb)

theorem finite_children_work_490 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_490 j) (childrenD_490 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_321 0 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 4 (2, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_485 1 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_485 3 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_489 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_489 4 (0, 12)).mono (by decide +kernel)

theorem finite_row_works_490 : FiniteTemplate HasSnaky 13 required_490 envelope_490 := by
  refine finite_compose HasSnaky 12 childrenC_490 childrenD_490 finite_children_work_490 (5, 7)
    required_490 envelope_490 pivot_mem_490 child_required_sub_490 child_envelope_sub_490 ?_
  intro b hb
  exact common_sub_490 (mem_commonEnvelope childrenD_490 b hb)

theorem finite_children_work_538_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_538_i0 j) (childrenD_538_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_190 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_190 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_258 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_273 4 (1, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_415 0 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 1 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_538_i0 : FiniteTemplate HasSnaky 9 required_538_i0 envelope_538_i0 := by
  refine finite_compose HasSnaky 8 childrenC_538_i0 childrenD_538_i0 finite_children_work_538_i0 (5, 7)
    required_538_i0 envelope_538_i0 pivot_mem_538_i0 child_required_sub_538_i0 child_envelope_sub_538_i0 ?_
  intro b hb
  exact common_sub_538_i0 (mem_commonEnvelope childrenD_538_i0 b hb)

theorem finite_children_work_538_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_538_i1 j) (childrenD_538_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_512 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_538_i1 : FiniteTemplate HasSnaky 10 required_538_i1 envelope_538_i1 := by
  refine finite_compose HasSnaky 9 childrenC_538_i1 childrenD_538_i1 finite_children_work_538_i1 (4, 6)
    required_538_i1 envelope_538_i1 pivot_mem_538_i1 child_required_sub_538_i1 child_envelope_sub_538_i1 ?_
  intro b hb
  exact common_sub_538_i1 (mem_commonEnvelope childrenD_538_i1 b hb)

theorem finite_children_work_538_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_538_i3 j) (childrenD_538_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_354 5 (6, 4)).mono (by decide +kernel)

theorem finite_row_works_538_i3 : FiniteTemplate HasSnaky 5 required_538_i3 envelope_538_i3 := by
  refine finite_compose HasSnaky 4 childrenC_538_i3 childrenD_538_i3 finite_children_work_538_i3 (5, 7)
    required_538_i3 envelope_538_i3 pivot_mem_538_i3 child_required_sub_538_i3 child_envelope_sub_538_i3 ?_
  intro b hb
  exact common_sub_538_i3 (mem_commonEnvelope childrenD_538_i3 b hb)

theorem finite_children_work_538_i4 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_538_i4 j) (childrenD_538_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_15 2 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_538_i4 : FiniteTemplate HasSnaky 3 required_538_i4 envelope_538_i4 := by
  refine finite_compose HasSnaky 2 childrenC_538_i4 childrenD_538_i4 finite_children_work_538_i4 (4, 6)
    required_538_i4 envelope_538_i4 pivot_mem_538_i4 child_required_sub_538_i4 child_envelope_sub_538_i4 ?_
  intro b hb
  exact common_sub_538_i4 (mem_commonEnvelope childrenD_538_i4 b hb)

theorem finite_children_work_538_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_538_i5 j) (childrenD_538_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_505 7 (6, 7)).mono (by decide +kernel)

theorem finite_row_works_538_i5 : FiniteTemplate HasSnaky 6 required_538_i5 envelope_538_i5 := by
  refine finite_compose HasSnaky 5 childrenC_538_i5 childrenD_538_i5 finite_children_work_538_i5 (5, 7)
    required_538_i5 envelope_538_i5 pivot_mem_538_i5 child_required_sub_538_i5 child_envelope_sub_538_i5 ?_
  intro b hb
  exact common_sub_538_i5 (mem_commonEnvelope childrenD_538_i5 b hb)

theorem finite_children_work_538_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_538_i2 j) (childrenD_538_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_136 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_538_i3.mono (by decide +kernel)
  · exact finite_row_works_538_i4.mono (by decide +kernel)
  · exact finite_row_works_538_i5.mono (by decide +kernel)

theorem finite_row_works_538_i2 : FiniteTemplate HasSnaky 7 required_538_i2 envelope_538_i2 := by
  refine finite_compose HasSnaky 6 childrenC_538_i2 childrenD_538_i2 finite_children_work_538_i2 (5, 4)
    required_538_i2 envelope_538_i2 pivot_mem_538_i2 child_required_sub_538_i2 child_envelope_sub_538_i2 ?_
  intro b hb
  exact common_sub_538_i2 (mem_commonEnvelope childrenD_538_i2 b hb)

theorem finite_children_work_538_i6 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_538_i6 j) (childrenD_538_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_517 0 (3, 2)).mono (by decide +kernel)

theorem finite_row_works_538_i6 : FiniteTemplate HasSnaky 12 required_538_i6 envelope_538_i6 := by
  refine finite_compose HasSnaky 11 childrenC_538_i6 childrenD_538_i6 finite_children_work_538_i6 (4, 6)
    required_538_i6 envelope_538_i6 pivot_mem_538_i6 child_required_sub_538_i6 child_envelope_sub_538_i6 ?_
  intro b hb
  exact common_sub_538_i6 (mem_commonEnvelope childrenD_538_i6 b hb)

theorem finite_children_work_538_i7 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_538_i7 j) (childrenD_538_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_258 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_273 4 (1, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_275 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_415 0 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_518 2 (8, 2)).mono (by decide +kernel)

theorem finite_row_works_538_i7 : FiniteTemplate HasSnaky 9 required_538_i7 envelope_538_i7 := by
  refine finite_compose HasSnaky 8 childrenC_538_i7 childrenD_538_i7 finite_children_work_538_i7 (5, 7)
    required_538_i7 envelope_538_i7 pivot_mem_538_i7 child_required_sub_538_i7 child_envelope_sub_538_i7 ?_
  intro b hb
  exact common_sub_538_i7 (mem_commonEnvelope childrenD_538_i7 b hb)

theorem finite_children_work_538_i8 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_538_i8 j) (childrenD_538_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_527 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_538_i8 : FiniteTemplate HasSnaky 12 required_538_i8 envelope_538_i8 := by
  refine finite_compose HasSnaky 11 childrenC_538_i8 childrenD_538_i8 finite_children_work_538_i8 (4, 6)
    required_538_i8 envelope_538_i8 pivot_mem_538_i8 child_required_sub_538_i8 child_envelope_sub_538_i8 ?_
  intro b hb
  exact common_sub_538_i8 (mem_commonEnvelope childrenD_538_i8 b hb)

theorem finite_children_work_538_i9 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_538_i9 j) (childrenD_538_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_537 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_538_i9 : FiniteTemplate HasSnaky 10 required_538_i9 envelope_538_i9 := by
  refine finite_compose HasSnaky 9 childrenC_538_i9 childrenD_538_i9 finite_children_work_538_i9 (4, 6)
    required_538_i9 envelope_538_i9 pivot_mem_538_i9 child_required_sub_538_i9 child_envelope_sub_538_i9 ?_
  intro b hb
  exact common_sub_538_i9 (mem_commonEnvelope childrenD_538_i9 b hb)

theorem finite_children_work_538 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_538 j) (childrenD_538 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 0 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_538_i0.mono (by decide +kernel)
  · exact finite_row_works_538_i1.mono (by decide +kernel)
  · exact finite_row_works_538_i2.mono (by decide +kernel)
  · exact finite_row_works_538_i6.mono (by decide +kernel)
  · exact finite_row_works_538_i7.mono (by decide +kernel)
  · exact finite_row_works_538_i8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_529 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_535 4 (3, 10)).mono (by decide +kernel)
  · exact finite_row_works_538_i9.mono (by decide +kernel)

theorem finite_row_works_538 : FiniteTemplate HasSnaky 13 required_538 envelope_538 := by
  refine finite_compose HasSnaky 12 childrenC_538 childrenD_538 finite_children_work_538 (5, 6)
    required_538 envelope_538 pivot_mem_538 child_required_sub_538 child_envelope_sub_538 ?_
  intro b hb
  exact common_sub_538 (mem_commonEnvelope childrenD_538 b hb)

theorem finite_children_work_552_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_552_i1 j) (childrenD_552_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_389 1 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_552_i1 : FiniteTemplate HasSnaky 6 required_552_i1 envelope_552_i1 := by
  refine finite_compose HasSnaky 5 childrenC_552_i1 childrenD_552_i1 finite_children_work_552_i1 (5, 6)
    required_552_i1 envelope_552_i1 pivot_mem_552_i1 child_required_sub_552_i1 child_envelope_sub_552_i1 ?_
  intro b hb
  exact common_sub_552_i1 (mem_commonEnvelope childrenD_552_i1 b hb)

theorem finite_children_work_552_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_552_i0 j) (childrenD_552_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_544 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 4 (6, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_546 0 (6, 2)).mono (by decide +kernel)
  · exact finite_row_works_552_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_548 0 (6, 1)).mono (by decide +kernel)

theorem finite_row_works_552_i0 : FiniteTemplate HasSnaky 11 required_552_i0 envelope_552_i0 := by
  refine finite_compose HasSnaky 10 childrenC_552_i0 childrenD_552_i0 finite_children_work_552_i0 (7, 7)
    required_552_i0 envelope_552_i0 pivot_mem_552_i0 child_required_sub_552_i0 child_envelope_sub_552_i0 ?_
  intro b hb
  exact common_sub_552_i0 (mem_commonEnvelope childrenD_552_i0 b hb)

theorem finite_children_work_552 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_552 j) (childrenD_552 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_258 0 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_326 4 (3, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_543 3 (0, 8)).mono (by decide +kernel)
  · exact finite_row_works_552_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_551 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_552 : FiniteTemplate HasSnaky 13 required_552 envelope_552 := by
  refine finite_compose HasSnaky 12 childrenC_552 childrenD_552 finite_children_work_552 (8, 6)
    required_552 envelope_552 pivot_mem_552 child_required_sub_552 child_envelope_sub_552 ?_
  intro b hb
  exact common_sub_552 (mem_commonEnvelope childrenD_552 b hb)

theorem finite_children_work_555_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_555_i0 j) (childrenD_555_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_61 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_194 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_224 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_555_i0 : FiniteTemplate HasSnaky 5 required_555_i0 envelope_555_i0 := by
  refine finite_compose HasSnaky 4 childrenC_555_i0 childrenD_555_i0 finite_children_work_555_i0 (2, 2)
    required_555_i0 envelope_555_i0 pivot_mem_555_i0 child_required_sub_555_i0 child_envelope_sub_555_i0 ?_
  intro b hb
  exact common_sub_555_i0 (mem_commonEnvelope childrenD_555_i0 b hb)

theorem finite_children_work_555 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_555 j) (childrenD_555 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_230 7 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_428 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_555_i0.mono (by decide +kernel)

theorem finite_row_works_555 : FiniteTemplate HasSnaky 13 required_555 envelope_555 := by
  refine finite_compose HasSnaky 12 childrenC_555 childrenD_555 finite_children_work_555 (3, 3)
    required_555 envelope_555 pivot_mem_555 child_required_sub_555 child_envelope_sub_555 ?_
  intro b hb
  exact common_sub_555 (mem_commonEnvelope childrenD_555 b hb)

end FiniteCongruenceChecks.SnakyFinite
