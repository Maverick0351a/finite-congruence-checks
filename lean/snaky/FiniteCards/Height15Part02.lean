/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06
import FiniteCards.Height05Part07
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height07Part02
import FiniteCards.Height07Part05
import FiniteCards.Height07Part06
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height08Part05
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height11Part04
import FiniteCards.Height11Part05
import FiniteCards.Height12Part02
import FiniteCards.Height13Part02
import FiniteCards.Height13Part03
import FiniteCards.Height13Part04
import FiniteCards.Height14Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_670_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_670_i0 j) (childrenD_670_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_660 1 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_670_i0 : FiniteTemplate HasSnaky 12 required_670_i0 envelope_670_i0 := by
  refine finite_compose HasSnaky 11 childrenC_670_i0 childrenD_670_i0 finite_children_work_670_i0 (5, 5)
    required_670_i0 envelope_670_i0 pivot_mem_670_i0 child_required_sub_670_i0 child_envelope_sub_670_i0 ?_
  intro b hb
  exact common_sub_670_i0 (mem_commonEnvelope childrenD_670_i0 b hb)

theorem finite_children_work_670_i1 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_670_i1 j) (childrenD_670_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_663 1 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_670_i1 : FiniteTemplate HasSnaky 12 required_670_i1 envelope_670_i1 := by
  refine finite_compose HasSnaky 11 childrenC_670_i1 childrenD_670_i1 finite_children_work_670_i1 (5, 5)
    required_670_i1 envelope_670_i1 pivot_mem_670_i1 child_required_sub_670_i1 child_envelope_sub_670_i1 ?_
  intro b hb
  exact common_sub_670_i1 (mem_commonEnvelope childrenD_670_i1 b hb)

theorem finite_children_work_670_i3 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_670_i3 j) (childrenD_670_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_106 1 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_219 1 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_530 4 (5, 9)).mono (by decide +kernel)

theorem finite_row_works_670_i3 : FiniteTemplate HasSnaky 9 required_670_i3 envelope_670_i3 := by
  refine finite_compose HasSnaky 8 childrenC_670_i3 childrenD_670_i3 finite_children_work_670_i3 (7, 6)
    required_670_i3 envelope_670_i3 pivot_mem_670_i3 child_required_sub_670_i3 child_envelope_sub_670_i3 ?_
  intro b hb
  exact common_sub_670_i3 (mem_commonEnvelope childrenD_670_i3 b hb)

theorem finite_children_work_670_i4 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_670_i4 j) (childrenD_670_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_98 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_512 4 (4, 9)).mono (by decide +kernel)

theorem finite_row_works_670_i4 : FiniteTemplate HasSnaky 10 required_670_i4 envelope_670_i4 := by
  refine finite_compose HasSnaky 9 childrenC_670_i4 childrenD_670_i4 finite_children_work_670_i4 (5, 5)
    required_670_i4 envelope_670_i4 pivot_mem_670_i4 child_required_sub_670_i4 child_envelope_sub_670_i4 ?_
  intro b hb
  exact common_sub_670_i4 (mem_commonEnvelope childrenD_670_i4 b hb)

theorem finite_children_work_670_i2 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_670_i2 j) (childrenD_670_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_270 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_588 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_638 4 (4, 9)).mono (by decide +kernel)
  · exact finite_row_works_670_i3.mono (by decide +kernel)
  · exact finite_row_works_670_i4.mono (by decide +kernel)

theorem finite_row_works_670_i2 : FiniteTemplate HasSnaky 13 required_670_i2 envelope_670_i2 := by
  refine finite_compose HasSnaky 12 childrenC_670_i2 childrenD_670_i2 finite_children_work_670_i2 (5, 6)
    required_670_i2 envelope_670_i2 pivot_mem_670_i2 child_required_sub_670_i2 child_envelope_sub_670_i2 ?_
  intro b hb
  exact common_sub_670_i2 (mem_commonEnvelope childrenD_670_i2 b hb)

theorem finite_children_work_670_i5 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_670_i5 j) (childrenD_670_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_617 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_670_i5 : FiniteTemplate HasSnaky 12 required_670_i5 envelope_670_i5 := by
  refine finite_compose HasSnaky 11 childrenC_670_i5 childrenD_670_i5 finite_children_work_670_i5 (5, 5)
    required_670_i5 envelope_670_i5 pivot_mem_670_i5 child_required_sub_670_i5 child_envelope_sub_670_i5 ?_
  intro b hb
  exact common_sub_670_i5 (mem_commonEnvelope childrenD_670_i5 b hb)

theorem finite_children_work_670_i6 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_670_i6 j) (childrenD_670_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 4 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_355 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_356 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_434 0 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_441 6 (7, 8)).mono (by decide +kernel)

theorem finite_row_works_670_i6 : FiniteTemplate HasSnaky 10 required_670_i6 envelope_670_i6 := by
  refine finite_compose HasSnaky 9 childrenC_670_i6 childrenD_670_i6 finite_children_work_670_i6 (6, 4)
    required_670_i6 envelope_670_i6 pivot_mem_670_i6 child_required_sub_670_i6 child_envelope_sub_670_i6 ?_
  intro b hb
  exact common_sub_670_i6 (mem_commonEnvelope childrenD_670_i6 b hb)

theorem finite_children_work_670_i7 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_670_i7 j) (childrenD_670_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_535 4 (4, 10)).mono (by decide +kernel)

theorem finite_row_works_670_i7 : FiniteTemplate HasSnaky 11 required_670_i7 envelope_670_i7 := by
  refine finite_compose HasSnaky 10 childrenC_670_i7 childrenD_670_i7 finite_children_work_670_i7 (5, 5)
    required_670_i7 envelope_670_i7 pivot_mem_670_i7 child_required_sub_670_i7 child_envelope_sub_670_i7 ?_
  intro b hb
  exact common_sub_670_i7 (mem_commonEnvelope childrenD_670_i7 b hb)

theorem finite_children_work_670_i8 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_670_i8 j) (childrenD_670_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 4 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_441 6 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_442 6 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_514 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_667 4 (3, 7)).mono (by decide +kernel)

theorem finite_row_works_670_i8 : FiniteTemplate HasSnaky 10 required_670_i8 envelope_670_i8 := by
  refine finite_compose HasSnaky 9 childrenC_670_i8 childrenD_670_i8 finite_children_work_670_i8 (6, 4)
    required_670_i8 envelope_670_i8 pivot_mem_670_i8 child_required_sub_670_i8 child_envelope_sub_670_i8 ?_
  intro b hb
  exact common_sub_670_i8 (mem_commonEnvelope childrenD_670_i8 b hb)

theorem finite_children_work_670_i10 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_670_i10 j) (childrenD_670_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_125 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_136 4 (4, 7)).mono (by decide +kernel)

theorem finite_row_works_670_i10 : FiniteTemplate HasSnaky 7 required_670_i10 envelope_670_i10 := by
  refine finite_compose HasSnaky 6 childrenC_670_i10 childrenD_670_i10 finite_children_work_670_i10 (5, 5)
    required_670_i10 envelope_670_i10 pivot_mem_670_i10 child_required_sub_670_i10 child_envelope_sub_670_i10 ?_
  intro b hb
  exact common_sub_670_i10 (mem_commonEnvelope childrenD_670_i10 b hb)

theorem finite_children_work_670_i9 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_670_i9 j) (childrenD_670_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_514 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_590 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_668 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_670_i10.mono (by decide +kernel)

theorem finite_row_works_670_i9 : FiniteTemplate HasSnaky 14 required_670_i9 envelope_670_i9 := by
  refine finite_compose HasSnaky 13 childrenC_670_i9 childrenD_670_i9 finite_children_work_670_i9 (6, 4)
    required_670_i9 envelope_670_i9 pivot_mem_670_i9 child_required_sub_670_i9 child_envelope_sub_670_i9 ?_
  intro b hb
  exact common_sub_670_i9 (mem_commonEnvelope childrenD_670_i9 b hb)

theorem finite_children_work_670 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_670 j) (childrenD_670 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 0 (5, 1)).mono (by decide +kernel)
  · exact finite_row_works_670_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_661 4 (2, 10)).mono (by decide +kernel)
  · exact finite_row_works_670_i1.mono (by decide +kernel)
  · exact finite_row_works_670_i2.mono (by decide +kernel)
  · exact finite_row_works_670_i5.mono (by decide +kernel)
  · exact finite_row_works_670_i6.mono (by decide +kernel)
  · exact finite_row_works_670_i7.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_665 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_670_i8.mono (by decide +kernel)
  · exact finite_row_works_670_i9.mono (by decide +kernel)
  · exact finite_row_works_669.mono (by decide +kernel)

theorem finite_row_works_670 : FiniteTemplate HasSnaky 15 required_670 envelope_670 := by
  refine finite_compose HasSnaky 14 childrenC_670 childrenD_670 finite_children_work_670 (6, 6)
    required_670 envelope_670 pivot_mem_670 child_required_sub_670 child_envelope_sub_670 ?_
  intro b hb
  exact common_sub_670 (mem_commonEnvelope childrenD_670 b hb)

theorem finite_children_work_682_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_682_i0 j) (childrenD_682_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_128 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_676 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_682_i0 : FiniteTemplate HasSnaky 12 required_682_i0 envelope_682_i0 := by
  refine finite_compose HasSnaky 11 childrenC_682_i0 childrenD_682_i0 finite_children_work_682_i0 (4, 3)
    required_682_i0 envelope_682_i0 pivot_mem_682_i0 child_required_sub_682_i0 child_envelope_sub_682_i0 ?_
  intro b hb
  exact common_sub_682_i0 (mem_commonEnvelope childrenD_682_i0 b hb)

theorem finite_children_work_682_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_682_i5 j) (childrenD_682_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_386 5 (8, 4)).mono (by decide +kernel)

theorem finite_row_works_682_i5 : FiniteTemplate HasSnaky 6 required_682_i5 envelope_682_i5 := by
  refine finite_compose HasSnaky 5 childrenC_682_i5 childrenD_682_i5 finite_children_work_682_i5 (6, 7)
    required_682_i5 envelope_682_i5 pivot_mem_682_i5 child_required_sub_682_i5 child_envelope_sub_682_i5 ?_
  intro b hb
  exact common_sub_682_i5 (mem_commonEnvelope childrenD_682_i5 b hb)

theorem finite_children_work_682_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_682_i6 j) (childrenD_682_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_222 1 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_682_i6 : FiniteTemplate HasSnaky 4 required_682_i6 envelope_682_i6 := by
  refine finite_compose HasSnaky 3 childrenC_682_i6 childrenD_682_i6 finite_children_work_682_i6 (5, 6)
    required_682_i6 envelope_682_i6 pivot_mem_682_i6 child_required_sub_682_i6 child_envelope_sub_682_i6 ?_
  intro b hb
  exact common_sub_682_i6 (mem_commonEnvelope childrenD_682_i6 b hb)

theorem finite_children_work_682_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_682_i4 j) (childrenD_682_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_377 2 (7, 3)).mono (by decide +kernel)
  · exact finite_row_works_682_i5.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_426 0 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_682_i6.mono (by decide +kernel)

theorem finite_row_works_682_i4 : FiniteTemplate HasSnaky 7 required_682_i4 envelope_682_i4 := by
  refine finite_compose HasSnaky 6 childrenC_682_i4 childrenD_682_i4 finite_children_work_682_i4 (4, 6)
    required_682_i4 envelope_682_i4 pivot_mem_682_i4 child_required_sub_682_i4 child_envelope_sub_682_i4 ?_
  intro b hb
  exact common_sub_682_i4 (mem_commonEnvelope childrenD_682_i4 b hb)

theorem finite_children_work_682_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_682_i3 j) (childrenD_682_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 6 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_679 2 (7, 3)).mono (by decide +kernel)
  · exact finite_row_works_682_i4.mono (by decide +kernel)

theorem finite_row_works_682_i3 : FiniteTemplate HasSnaky 8 required_682_i3 envelope_682_i3 := by
  refine finite_compose HasSnaky 7 childrenC_682_i3 childrenD_682_i3 finite_children_work_682_i3 (6, 6)
    required_682_i3 envelope_682_i3 pivot_mem_682_i3 child_required_sub_682_i3 child_envelope_sub_682_i3 ?_
  intro b hb
  exact common_sub_682_i3 (mem_commonEnvelope childrenD_682_i3 b hb)

theorem finite_children_work_682_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_682_i2 j) (childrenD_682_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_59 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_105 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_678 2 (7, 1)).mono (by decide +kernel)
  · exact finite_row_works_682_i3.mono (by decide +kernel)

theorem finite_row_works_682_i2 : FiniteTemplate HasSnaky 9 required_682_i2 envelope_682_i2 := by
  refine finite_compose HasSnaky 8 childrenC_682_i2 childrenD_682_i2 finite_children_work_682_i2 (6, 5)
    required_682_i2 envelope_682_i2 pivot_mem_682_i2 child_required_sub_682_i2 child_envelope_sub_682_i2 ?_
  intro b hb
  exact common_sub_682_i2 (mem_commonEnvelope childrenD_682_i2 b hb)

theorem finite_children_work_682_i8 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_682_i8 j) (childrenD_682_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_243 2 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_679 2 (7, 3)).mono (by decide +kernel)

theorem finite_row_works_682_i8 : FiniteTemplate HasSnaky 6 required_682_i8 envelope_682_i8 := by
  refine finite_compose HasSnaky 5 childrenC_682_i8 childrenD_682_i8 finite_children_work_682_i8 (6, 6)
    required_682_i8 envelope_682_i8 pivot_mem_682_i8 child_required_sub_682_i8 child_envelope_sub_682_i8 ?_
  intro b hb
  exact common_sub_682_i8 (mem_commonEnvelope childrenD_682_i8 b hb)

theorem finite_children_work_682_i7 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_682_i7 j) (childrenD_682_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_430 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_431 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_592 7 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_678 2 (7, 1)).mono (by decide +kernel)
  · exact finite_row_works_682_i8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_681 4 (2, 9)).mono (by decide +kernel)

theorem finite_row_works_682_i7 : FiniteTemplate HasSnaky 9 required_682_i7 envelope_682_i7 := by
  refine finite_compose HasSnaky 8 childrenC_682_i7 childrenD_682_i7 finite_children_work_682_i7 (6, 5)
    required_682_i7 envelope_682_i7 pivot_mem_682_i7 child_required_sub_682_i7 child_envelope_sub_682_i7 ?_
  intro b hb
  exact common_sub_682_i7 (mem_commonEnvelope childrenD_682_i7 b hb)

theorem finite_children_work_682_i1 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_682_i1 j) (childrenD_682_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_422 2 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_450 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_503 6 (7, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_642 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_682_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_680 4 (2, 7)).mono (by decide +kernel)
  · exact finite_row_works_682_i7.mono (by decide +kernel)

theorem finite_row_works_682_i1 : FiniteTemplate HasSnaky 14 required_682_i1 envelope_682_i1 := by
  refine finite_compose HasSnaky 13 childrenC_682_i1 childrenD_682_i1 finite_children_work_682_i1 (6, 4)
    required_682_i1 envelope_682_i1 pivot_mem_682_i1 child_required_sub_682_i1 child_envelope_sub_682_i1 ?_
  intro b hb
  exact common_sub_682_i1 (mem_commonEnvelope childrenD_682_i1 b hb)

theorem finite_children_work_682 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_682 j) (childrenD_682 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_408 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_410 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_509 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_510 7 (7, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_646 6 (7, 8)).mono (by decide +kernel)
  · exact finite_row_works_682_i0.mono (by decide +kernel)
  · exact finite_row_works_682_i1.mono (by decide +kernel)

theorem finite_row_works_682 : FiniteTemplate HasSnaky 15 required_682 envelope_682 := by
  refine finite_compose HasSnaky 14 childrenC_682 childrenD_682 finite_children_work_682 (4, 4)
    required_682 envelope_682 pivot_mem_682 child_required_sub_682 child_envelope_sub_682 ?_
  intro b hb
  exact common_sub_682 (mem_commonEnvelope childrenD_682 b hb)

end FiniteCongruenceChecks.SnakyFinite
