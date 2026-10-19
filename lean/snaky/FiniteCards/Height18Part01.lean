/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height18Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part04
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height10Part01
import FiniteCards.Height11Part01
import FiniteCards.Height11Part04
import FiniteCards.Height11Part05
import FiniteCards.Height12Part01
import FiniteCards.Height12Part02
import FiniteCards.Height12Part04
import FiniteCards.Height13Part01
import FiniteCards.Height13Part03
import FiniteCards.Height13Part04
import FiniteCards.Height13Part05
import FiniteCards.Height14Part02
import FiniteCards.Height14Part03
import FiniteCards.Height15Part01
import FiniteCards.Height15Part02
import FiniteCards.Height16Part02
import FiniteCards.Height17Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_684_i1 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_684_i1 j) (childrenD_684_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 4 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 4 (6, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_469 1 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_470 4 (5, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_485 3 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_489 4 (4, 12)).mono (by decide +kernel)

theorem finite_row_works_684_i1 : FiniteTemplate HasSnaky 13 required_684_i1 envelope_684_i1 := by
  refine finite_compose HasSnaky 12 childrenC_684_i1 childrenD_684_i1 finite_children_work_684_i1 (9, 7)
    required_684_i1 envelope_684_i1 pivot_mem_684_i1 child_required_sub_684_i1 child_envelope_sub_684_i1 ?_
  intro b hb
  exact common_sub_684_i1 (mem_commonEnvelope childrenD_684_i1 b hb)

theorem finite_children_work_684_i0 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_684_i0 j) (childrenD_684_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_118 4 (5, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_355 3 (5, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_434 3 (5, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_468 1 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_684_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_491 7 (9, 11)).mono (by decide +kernel)

theorem finite_row_works_684_i0 : FiniteTemplate HasSnaky 14 required_684_i0 envelope_684_i0 := by
  refine finite_compose HasSnaky 13 childrenC_684_i0 childrenD_684_i0 finite_children_work_684_i0 (8, 7)
    required_684_i0 envelope_684_i0 pivot_mem_684_i0 child_required_sub_684_i0 child_envelope_sub_684_i0 ?_
  intro b hb
  exact common_sub_684_i0 (mem_commonEnvelope childrenD_684_i0 b hb)

theorem finite_children_work_684_i2 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_684_i2 j) (childrenD_684_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 0 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_97 0 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_98 2 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_454 6 (8, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_455 5 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_624 1 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_684_i2 : FiniteTemplate HasSnaky 12 required_684_i2 envelope_684_i2 := by
  refine finite_compose HasSnaky 11 childrenC_684_i2 childrenD_684_i2 finite_children_work_684_i2 (7, 9)
    required_684_i2 envelope_684_i2 pivot_mem_684_i2 child_required_sub_684_i2 child_envelope_sub_684_i2 ?_
  intro b hb
  exact common_sub_684_i2 (mem_commonEnvelope childrenD_684_i2 b hb)

theorem finite_children_work_684_i3 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_684_i3 j) (childrenD_684_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_174 4 (4, 14)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 0 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 2 (9, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_483 0 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_508 1 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_508 5 (10, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_566 4 (4, 14)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 0 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 2 (9, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_635 4 (5, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_644 4 (3, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_645 4 (3, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_647 4 (3, 15)).mono (by decide +kernel)

theorem finite_row_works_684_i3 : FiniteTemplate HasSnaky 15 required_684_i3 envelope_684_i3 := by
  refine finite_compose HasSnaky 14 childrenC_684_i3 childrenD_684_i3 finite_children_work_684_i3 (7, 11)
    required_684_i3 envelope_684_i3 pivot_mem_684_i3 child_required_sub_684_i3 child_envelope_sub_684_i3 ?_
  intro b hb
  exact common_sub_684_i3 (mem_commonEnvelope childrenD_684_i3 b hb)

theorem finite_children_work_684_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_684_i5 j) (childrenD_684_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_313 2 (9, 6)).mono (by decide +kernel)

theorem finite_row_works_684_i5 : FiniteTemplate HasSnaky 7 required_684_i5 envelope_684_i5 := by
  refine finite_compose HasSnaky 6 childrenC_684_i5 childrenD_684_i5 finite_children_work_684_i5 (9, 7)
    required_684_i5 envelope_684_i5 pivot_mem_684_i5 child_required_sub_684_i5 child_envelope_sub_684_i5 ?_
  intro b hb
  exact common_sub_684_i5 (mem_commonEnvelope childrenD_684_i5 b hb)

theorem finite_children_work_684_i4 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_684_i4 j) (childrenD_684_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_257 0 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_684_i5.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_434 3 (5, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_468 5 (11, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_491 7 (9, 11)).mono (by decide +kernel)

theorem finite_row_works_684_i4 : FiniteTemplate HasSnaky 12 required_684_i4 envelope_684_i4 := by
  refine finite_compose HasSnaky 11 childrenC_684_i4 childrenD_684_i4 finite_children_work_684_i4 (8, 7)
    required_684_i4 envelope_684_i4 pivot_mem_684_i4 child_required_sub_684_i4 child_envelope_sub_684_i4 ?_
  intro b hb
  exact common_sub_684_i4 (mem_commonEnvelope childrenD_684_i4 b hb)

theorem finite_children_work_684 : ∀ j, FiniteTemplate HasSnaky 17 (childrenC_684 j) (childrenD_684 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_684_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_623 3 (0, 15)).mono (by decide +kernel)
  · exact finite_row_works_684_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_625 5 (9, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_630 3 (0, 14)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_632 5 (10, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_636 5 (11, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_639 1 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_684_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_656 1 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_657 1 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_670 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_675 5 (12, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_683 1 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_684_i4.mono (by decide +kernel)

theorem finite_row_works_684 : FiniteTemplate HasSnaky 18 required_684 envelope_684 := by
  refine finite_compose HasSnaky 17 childrenC_684 childrenD_684 finite_children_work_684 (7, 10)
    required_684 envelope_684 pivot_mem_684 child_required_sub_684 child_envelope_sub_684 ?_
  intro b hb
  exact common_sub_684 (mem_commonEnvelope childrenD_684 b hb)

theorem finite_children_work_691_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_691_i0 j) (childrenD_691_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_277 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_278 1 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_691_i0 : FiniteTemplate HasSnaky 6 required_691_i0 envelope_691_i0 := by
  refine finite_compose HasSnaky 5 childrenC_691_i0 childrenD_691_i0 finite_children_work_691_i0 (4, 5)
    required_691_i0 envelope_691_i0 pivot_mem_691_i0 child_required_sub_691_i0 child_envelope_sub_691_i0 ?_
  intro b hb
  exact common_sub_691_i0 (mem_commonEnvelope childrenD_691_i0 b hb)

theorem finite_children_work_691_i5 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_691_i5 j) (childrenD_691_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_317 0 (3, 2)).mono (by decide +kernel)

theorem finite_row_works_691_i5 : FiniteTemplate HasSnaky 8 required_691_i5 envelope_691_i5 := by
  refine finite_compose HasSnaky 7 childrenC_691_i5 childrenD_691_i5 finite_children_work_691_i5 (5, 6)
    required_691_i5 envelope_691_i5 pivot_mem_691_i5 child_required_sub_691_i5 child_envelope_sub_691_i5 ?_
  intro b hb
  exact common_sub_691_i5 (mem_commonEnvelope childrenD_691_i5 b hb)

theorem finite_children_work_691_i4 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_691_i4 j) (childrenD_691_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_59 4 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_462 0 (5, 2)).mono (by decide +kernel)
  · exact finite_row_works_691_i5.mono (by decide +kernel)

theorem finite_row_works_691_i4 : FiniteTemplate HasSnaky 14 required_691_i4 envelope_691_i4 := by
  refine finite_compose HasSnaky 13 childrenC_691_i4 childrenD_691_i4 finite_children_work_691_i4 (6, 6)
    required_691_i4 envelope_691_i4 pivot_mem_691_i4 child_required_sub_691_i4 child_envelope_sub_691_i4 ?_
  intro b hb
  exact common_sub_691_i4 (mem_commonEnvelope childrenD_691_i4 b hb)

theorem finite_children_work_691_i3 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_691_i3 j) (childrenD_691_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_102 3 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_400 0 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_691_i4.mono (by decide +kernel)

theorem finite_row_works_691_i3 : FiniteTemplate HasSnaky 15 required_691_i3 envelope_691_i3 := by
  refine finite_compose HasSnaky 14 childrenC_691_i3 childrenD_691_i3 finite_children_work_691_i3 (6, 5)
    required_691_i3 envelope_691_i3 pivot_mem_691_i3 child_required_sub_691_i3 child_envelope_sub_691_i3 ?_
  intro b hb
  exact common_sub_691_i3 (mem_commonEnvelope childrenD_691_i3 b hb)

theorem finite_children_work_691_i2 : ∀ j, FiniteTemplate HasSnaky 15 (childrenC_691_i2 j) (childrenD_691_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_691_i3.mono (by decide +kernel)

theorem finite_row_works_691_i2 : FiniteTemplate HasSnaky 16 required_691_i2 envelope_691_i2 := by
  refine finite_compose HasSnaky 15 childrenC_691_i2 childrenD_691_i2 finite_children_work_691_i2 (4, 5)
    required_691_i2 envelope_691_i2 pivot_mem_691_i2 child_required_sub_691_i2 child_envelope_sub_691_i2 ?_
  intro b hb
  exact common_sub_691_i2 (mem_commonEnvelope childrenD_691_i2 b hb)

theorem finite_children_work_691_i1 : ∀ j, FiniteTemplate HasSnaky 16 (childrenC_691_i1 j) (childrenD_691_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 3)).mono (by decide +kernel)
  · exact finite_row_works_691_i2.mono (by decide +kernel)

theorem finite_row_works_691_i1 : FiniteTemplate HasSnaky 17 required_691_i1 envelope_691_i1 := by
  refine finite_compose HasSnaky 16 childrenC_691_i1 childrenD_691_i1 finite_children_work_691_i1 (4, 6)
    required_691_i1 envelope_691_i1 pivot_mem_691_i1 child_required_sub_691_i1 child_envelope_sub_691_i1 ?_
  intro b hb
  exact common_sub_691_i1 (mem_commonEnvelope childrenD_691_i1 b hb)

theorem finite_children_work_691_i10 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_691_i10 j) (childrenD_691_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 1 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_691_i10 : FiniteTemplate HasSnaky 3 required_691_i10 envelope_691_i10 := by
  refine finite_compose HasSnaky 2 childrenC_691_i10 childrenD_691_i10 finite_children_work_691_i10 (2, 6)
    required_691_i10 envelope_691_i10 pivot_mem_691_i10 child_required_sub_691_i10 child_envelope_sub_691_i10 ?_
  intro b hb
  exact common_sub_691_i10 (mem_commonEnvelope childrenD_691_i10 b hb)

theorem finite_children_work_691_i9 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_691_i9 j) (childrenD_691_i9 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_691_i10.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_460 4 (5, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_488 0 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_691_i9 : FiniteTemplate HasSnaky 11 required_691_i9 envelope_691_i9 := by
  refine finite_compose HasSnaky 10 childrenC_691_i9 childrenD_691_i9 finite_children_work_691_i9 (6, 7)
    required_691_i9 envelope_691_i9 pivot_mem_691_i9 child_required_sub_691_i9 child_envelope_sub_691_i9 ?_
  intro b hb
  exact common_sub_691_i9 (mem_commonEnvelope childrenD_691_i9 b hb)

theorem finite_children_work_691_i8 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_691_i8 j) (childrenD_691_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_80 1 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_691_i9.mono (by decide +kernel)

theorem finite_row_works_691_i8 : FiniteTemplate HasSnaky 12 required_691_i8 envelope_691_i8 := by
  refine finite_compose HasSnaky 11 childrenC_691_i8 childrenD_691_i8 finite_children_work_691_i8 (6, 5)
    required_691_i8 envelope_691_i8 pivot_mem_691_i8 child_required_sub_691_i8 child_envelope_sub_691_i8 ?_
  intro b hb
  exact common_sub_691_i8 (mem_commonEnvelope childrenD_691_i8 b hb)

theorem finite_children_work_691_i7 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_691_i7 j) (childrenD_691_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 7 (6, 7)).mono (by decide +kernel)
  · exact finite_row_works_691_i8.mono (by decide +kernel)

theorem finite_row_works_691_i7 : FiniteTemplate HasSnaky 13 required_691_i7 envelope_691_i7 := by
  refine finite_compose HasSnaky 12 childrenC_691_i7 childrenD_691_i7 finite_children_work_691_i7 (4, 5)
    required_691_i7 envelope_691_i7 pivot_mem_691_i7 child_required_sub_691_i7 child_envelope_sub_691_i7 ?_
  intro b hb
  exact common_sub_691_i7 (mem_commonEnvelope childrenD_691_i7 b hb)

theorem finite_children_work_691_i6 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_691_i6 j) (childrenD_691_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_690 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_691_i7.mono (by decide +kernel)

theorem finite_row_works_691_i6 : FiniteTemplate HasSnaky 14 required_691_i6 envelope_691_i6 := by
  refine finite_compose HasSnaky 13 childrenC_691_i6 childrenD_691_i6 finite_children_work_691_i6 (3, 7)
    required_691_i6 envelope_691_i6 pivot_mem_691_i6 child_required_sub_691_i6 child_envelope_sub_691_i6 ?_
  intro b hb
  exact common_sub_691_i6 (mem_commonEnvelope childrenD_691_i6 b hb)

theorem finite_children_work_691 : ∀ j, FiniteTemplate HasSnaky 17 (childrenC_691 j) (childrenD_691 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_691_i0.mono (by decide +kernel)
  · exact finite_row_works_691_i1.mono (by decide +kernel)
  · exact finite_row_works_691_i6.mono (by decide +kernel)

theorem finite_row_works_691 : FiniteTemplate HasSnaky 18 required_691 envelope_691 := by
  refine finite_compose HasSnaky 17 childrenC_691 childrenD_691 finite_children_work_691 (3, 6)
    required_691 envelope_691 pivot_mem_691 child_required_sub_691 child_envelope_sub_691 ?_
  intro b hb
  exact common_sub_691 (mem_commonEnvelope childrenD_691 b hb)

end FiniteCongruenceChecks.SnakyFinite
