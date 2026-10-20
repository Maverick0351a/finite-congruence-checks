/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part05
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part05
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height09Part05
import FiniteCards.Height10Part02
import FiniteCards.Height10Part03
import FiniteCards.Height11Part03
import FiniteCards.Height11Part04
import FiniteCards.Height12Part03
import FiniteCards.Height13Part01
import FiniteCards.Height13Part02
import FiniteCards.Height13Part03
import FiniteCards.Height14Part01
import FiniteCards.Height14Part02
import FiniteCards.Height15Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_602_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_602_i1 j) (childrenD_602_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_320 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_496 3 (2, 8)).mono (by decide +kernel)

theorem finite_row_works_602_i1 : FiniteTemplate HasSnaky 8 required_602_i1 envelope_602_i1 := by
  refine finite_compose HasSnaky 7 childrenC_602_i1 childrenD_602_i1 finite_children_work_602_i1 (5, 8)
    required_602_i1 envelope_602_i1 pivot_mem_602_i1 child_required_sub_602_i1 child_envelope_sub_602_i1 ?_
  intro b hb
  exact common_sub_602_i1 (mem_commonEnvelope childrenD_602_i1 b hb)

theorem finite_children_work_602_i0 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_602_i0 j) (childrenD_602_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_59 4 (3, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_497 3 (2, 8)).mono (by decide +kernel)
  · exact finite_row_works_602_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_555 0 (3, 3)).mono (by decide +kernel)

theorem finite_row_works_602_i0 : FiniteTemplate HasSnaky 14 required_602_i0 envelope_602_i0 := by
  refine finite_compose HasSnaky 13 childrenC_602_i0 childrenD_602_i0 finite_children_work_602_i0 (6, 8)
    required_602_i0 envelope_602_i0 pivot_mem_602_i0 child_required_sub_602_i0 child_envelope_sub_602_i0 ?_
  intro b hb
  exact common_sub_602_i0 (mem_commonEnvelope childrenD_602_i0 b hb)

theorem finite_children_work_602_i3 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_602_i3 j) (childrenD_602_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 4 (5, 12)).mono (by decide +kernel)

theorem finite_row_works_602_i3 : FiniteTemplate HasSnaky 11 required_602_i3 envelope_602_i3 := by
  refine finite_compose HasSnaky 10 childrenC_602_i3 childrenD_602_i3 finite_children_work_602_i3 (6, 8)
    required_602_i3 envelope_602_i3 pivot_mem_602_i3 child_required_sub_602_i3 child_envelope_sub_602_i3 ?_
  intro b hb
  exact common_sub_602_i3 (mem_commonEnvelope childrenD_602_i3 b hb)

theorem finite_children_work_602_i2 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_602_i2 j) (childrenD_602_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_107 3 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_163 3 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_556 4 (3, 11)).mono (by decide +kernel)
  · exact finite_row_works_602_i3.mono (by decide +kernel)

theorem finite_row_works_602_i2 : FiniteTemplate HasSnaky 12 required_602_i2 envelope_602_i2 := by
  refine finite_compose HasSnaky 11 childrenC_602_i2 childrenD_602_i2 finite_children_work_602_i2 (7, 7)
    required_602_i2 envelope_602_i2 pivot_mem_602_i2 child_required_sub_602_i2 child_envelope_sub_602_i2 ?_
  intro b hb
  exact common_sub_602_i2 (mem_commonEnvelope childrenD_602_i2 b hb)

theorem finite_children_work_602_i6 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_602_i6 j) (childrenD_602_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_157 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_383 2 (6, 3)).mono (by decide +kernel)

theorem finite_row_works_602_i6 : FiniteTemplate HasSnaky 6 required_602_i6 envelope_602_i6 := by
  refine finite_compose HasSnaky 5 childrenC_602_i6 childrenD_602_i6 finite_children_work_602_i6 (6, 5)
    required_602_i6 envelope_602_i6 pivot_mem_602_i6 child_required_sub_602_i6 child_envelope_sub_602_i6 ?_
  intro b hb
  exact common_sub_602_i6 (mem_commonEnvelope childrenD_602_i6 b hb)

theorem finite_children_work_602_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_602_i7 j) (childrenD_602_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 0 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_381 7 (7, 8)).mono (by decide +kernel)

theorem finite_row_works_602_i7 : FiniteTemplate HasSnaky 5 required_602_i7 envelope_602_i7 := by
  refine finite_compose HasSnaky 4 childrenC_602_i7 childrenD_602_i7 finite_children_work_602_i7 (6, 6)
    required_602_i7 envelope_602_i7 pivot_mem_602_i7 child_required_sub_602_i7 child_envelope_sub_602_i7 ?_
  intro b hb
  exact common_sub_602_i7 (mem_commonEnvelope childrenD_602_i7 b hb)

theorem finite_children_work_602_i8 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_602_i8 j) (childrenD_602_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_64 0 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_500 3 (2, 8)).mono (by decide +kernel)

theorem finite_row_works_602_i8 : FiniteTemplate HasSnaky 5 required_602_i8 envelope_602_i8 := by
  refine finite_compose HasSnaky 4 childrenC_602_i8 childrenD_602_i8 finite_children_work_602_i8 (5, 7)
    required_602_i8 envelope_602_i8 pivot_mem_602_i8 child_required_sub_602_i8 child_envelope_sub_602_i8 ?_
  intro b hb
  exact common_sub_602_i8 (mem_commonEnvelope childrenD_602_i8 b hb)

theorem finite_children_work_602_i5 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_602_i5 j) (childrenD_602_i5 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_602_i6.mono (by decide +kernel)
  · exact finite_row_works_602_i7.mono (by decide +kernel)
  · exact finite_row_works_602_i8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_601 3 (1, 8)).mono (by decide +kernel)

theorem finite_row_works_602_i5 : FiniteTemplate HasSnaky 12 required_602_i5 envelope_602_i5 := by
  refine finite_compose HasSnaky 11 childrenC_602_i5 childrenD_602_i5 finite_children_work_602_i5 (5, 5)
    required_602_i5 envelope_602_i5 pivot_mem_602_i5 child_required_sub_602_i5 child_envelope_sub_602_i5 ?_
  intro b hb
  exact common_sub_602_i5 (mem_commonEnvelope childrenD_602_i5 b hb)

theorem finite_children_work_602_i4 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_602_i4 j) (childrenD_602_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_119 0 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_497 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_498 1 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_602_i5.mono (by decide +kernel)

theorem finite_row_works_602_i4 : FiniteTemplate HasSnaky 13 required_602_i4 envelope_602_i4 := by
  refine finite_compose HasSnaky 12 childrenC_602_i4 childrenD_602_i4 finite_children_work_602_i4 (6, 8)
    required_602_i4 envelope_602_i4 pivot_mem_602_i4 child_required_sub_602_i4 child_envelope_sub_602_i4 ?_
  intro b hb
  exact common_sub_602_i4 (mem_commonEnvelope childrenD_602_i4 b hb)

theorem finite_children_work_602 : ∀ j, FiniteTemplate HasSnaky 15 (childrenC_602 j) (childrenD_602 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_553 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_602_i0.mono (by decide +kernel)
  · exact finite_row_works_602_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_557 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_564 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_568 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_573 3 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_574 4 (2, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_583 4 (0, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_598 4 (0, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_599 0 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_602_i4.mono (by decide +kernel)

theorem finite_row_works_602 : FiniteTemplate HasSnaky 16 required_602 envelope_602 := by
  refine finite_compose HasSnaky 15 childrenC_602 childrenD_602 finite_children_work_602 (6, 7)
    required_602 envelope_602 pivot_mem_602 child_required_sub_602 child_envelope_sub_602 ?_
  intro b hb
  exact common_sub_602 (mem_commonEnvelope childrenD_602 b hb)

theorem finite_children_work_627_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_627_i0 j) (childrenD_627_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_472 2 (7, 2)).mono (by decide +kernel)

theorem finite_row_works_627_i0 : FiniteTemplate HasSnaky 8 required_627_i0 envelope_627_i0 := by
  refine finite_compose HasSnaky 7 childrenC_627_i0 childrenD_627_i0 finite_children_work_627_i0 (4, 4)
    required_627_i0 envelope_627_i0 pivot_mem_627_i0 child_required_sub_627_i0 child_envelope_sub_627_i0 ?_
  intro b hb
  exact common_sub_627_i0 (mem_commonEnvelope childrenD_627_i0 b hb)

theorem finite_children_work_627_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_627_i3 j) (childrenD_627_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_205 6 (6, 7)).mono (by decide +kernel)

theorem finite_row_works_627_i3 : FiniteTemplate HasSnaky 4 required_627_i3 envelope_627_i3 := by
  refine finite_compose HasSnaky 3 childrenC_627_i3 childrenD_627_i3 finite_children_work_627_i3 (5, 3)
    required_627_i3 envelope_627_i3 pivot_mem_627_i3 child_required_sub_627_i3 child_envelope_sub_627_i3 ?_
  intro b hb
  exact common_sub_627_i3 (mem_commonEnvelope childrenD_627_i3 b hb)

theorem finite_children_work_627_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_627_i2 j) (childrenD_627_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (5, 7)).mono (by decide +kernel)
  · exact finite_row_works_627_i3.mono (by decide +kernel)

theorem finite_row_works_627_i2 : FiniteTemplate HasSnaky 5 required_627_i2 envelope_627_i2 := by
  refine finite_compose HasSnaky 4 childrenC_627_i2 childrenD_627_i2 finite_children_work_627_i2 (5, 5)
    required_627_i2 envelope_627_i2 pivot_mem_627_i2 child_required_sub_627_i2 child_envelope_sub_627_i2 ?_
  intro b hb
  exact common_sub_627_i2 (mem_commonEnvelope childrenD_627_i2 b hb)

theorem finite_children_work_627_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_627_i5 j) (childrenD_627_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 3 (3, 7)).mono (by decide +kernel)

theorem finite_row_works_627_i5 : FiniteTemplate HasSnaky 6 required_627_i5 envelope_627_i5 := by
  refine finite_compose HasSnaky 5 childrenC_627_i5 childrenD_627_i5 finite_children_work_627_i5 (5, 3)
    required_627_i5 envelope_627_i5 pivot_mem_627_i5 child_required_sub_627_i5 child_envelope_sub_627_i5 ?_
  intro b hb
  exact common_sub_627_i5 (mem_commonEnvelope childrenD_627_i5 b hb)

theorem finite_children_work_627_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_627_i4 j) (childrenD_627_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (5, 7)).mono (by decide +kernel)
  · exact finite_row_works_627_i5.mono (by decide +kernel)

theorem finite_row_works_627_i4 : FiniteTemplate HasSnaky 7 required_627_i4 envelope_627_i4 := by
  refine finite_compose HasSnaky 6 childrenC_627_i4 childrenD_627_i4 finite_children_work_627_i4 (5, 5)
    required_627_i4 envelope_627_i4 pivot_mem_627_i4 child_required_sub_627_i4 child_envelope_sub_627_i4 ?_
  intro b hb
  exact common_sub_627_i4 (mem_commonEnvelope childrenD_627_i4 b hb)

theorem finite_children_work_627_i6 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_627_i6 j) (childrenD_627_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_97 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_98 0 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_454 4 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_455 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_624 5 (10, 3)).mono (by decide +kernel)

theorem finite_row_works_627_i6 : FiniteTemplate HasSnaky 12 required_627_i6 envelope_627_i6 := by
  refine finite_compose HasSnaky 11 childrenC_627_i6 childrenD_627_i6 finite_children_work_627_i6 (5, 7)
    required_627_i6 envelope_627_i6 pivot_mem_627_i6 child_required_sub_627_i6 child_envelope_sub_627_i6 ?_
  intro b hb
  exact common_sub_627_i6 (mem_commonEnvelope childrenD_627_i6 b hb)

theorem finite_children_work_627_i8 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_627_i8 j) (childrenD_627_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_413 0 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_627_i8 : FiniteTemplate HasSnaky 6 required_627_i8 envelope_627_i8 := by
  refine finite_compose HasSnaky 5 childrenC_627_i8 childrenD_627_i8 finite_children_work_627_i8 (5, 3)
    required_627_i8 envelope_627_i8 pivot_mem_627_i8 child_required_sub_627_i8 child_envelope_sub_627_i8 ?_
  intro b hb
  exact common_sub_627_i8 (mem_commonEnvelope childrenD_627_i8 b hb)

theorem finite_children_work_627_i7 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_627_i7 j) (childrenD_627_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (5, 7)).mono (by decide +kernel)
  · exact finite_row_works_627_i8.mono (by decide +kernel)

theorem finite_row_works_627_i7 : FiniteTemplate HasSnaky 7 required_627_i7 envelope_627_i7 := by
  refine finite_compose HasSnaky 6 childrenC_627_i7 childrenD_627_i7 finite_children_work_627_i7 (5, 5)
    required_627_i7 envelope_627_i7 pivot_mem_627_i7 child_required_sub_627_i7 child_envelope_sub_627_i7 ?_
  intro b hb
  exact common_sub_627_i7 (mem_commonEnvelope childrenD_627_i7 b hb)

theorem finite_children_work_627_i9 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_627_i9 j) (childrenD_627_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_59 5 (9, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_105 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_323 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_603 1 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_627_i9 : FiniteTemplate HasSnaky 14 required_627_i9 envelope_627_i9 := by
  refine finite_compose HasSnaky 13 childrenC_627_i9 childrenD_627_i9 finite_children_work_627_i9 (6, 6)
    required_627_i9 envelope_627_i9 pivot_mem_627_i9 child_required_sub_627_i9 child_envelope_sub_627_i9 ?_
  intro b hb
  exact common_sub_627_i9 (mem_commonEnvelope childrenD_627_i9 b hb)

theorem finite_children_work_627_i1 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_627_i1 j) (childrenD_627_i1 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_627_i2.mono (by decide +kernel)
  · exact finite_row_works_627_i4.mono (by decide +kernel)
  · exact finite_row_works_627_i6.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_626 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_627_i7.mono (by decide +kernel)
  · exact finite_row_works_627_i9.mono (by decide +kernel)

theorem finite_row_works_627_i1 : FiniteTemplate HasSnaky 15 required_627_i1 envelope_627_i1 := by
  refine finite_compose HasSnaky 14 childrenC_627_i1 childrenD_627_i1 finite_children_work_627_i1 (5, 6)
    required_627_i1 envelope_627_i1 pivot_mem_627_i1 child_required_sub_627_i1 child_envelope_sub_627_i1 ?_
  intro b hb
  exact common_sub_627_i1 (mem_commonEnvelope childrenD_627_i1 b hb)

theorem finite_children_work_627 : ∀ j, FiniteTemplate HasSnaky 15 (childrenC_627 j) (childrenD_627 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 7 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_478 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_627_i0.mono (by decide +kernel)
  · exact finite_row_works_627_i1.mono (by decide +kernel)

theorem finite_row_works_627 : FiniteTemplate HasSnaky 16 required_627 envelope_627 := by
  refine finite_compose HasSnaky 15 childrenC_627 childrenD_627 finite_children_work_627 (5, 4)
    required_627 envelope_627 pivot_mem_627 child_required_sub_627 child_envelope_sub_627 ?_
  intro b hb
  exact common_sub_627 (mem_commonEnvelope childrenD_627 b hb)

end FiniteCongruenceChecks.SnakyFinite
