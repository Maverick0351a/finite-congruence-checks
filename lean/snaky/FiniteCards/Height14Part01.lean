/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part05
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part04
import FiniteCards.Height07Part02
import FiniteCards.Height10Part01
import FiniteCards.Height13Part01
import FiniteCards.Height13Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_553_i3 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_553_i3 j) (childrenD_553_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (5, 7)).mono (by decide +kernel)

theorem finite_row_works_553_i3 : FiniteTemplate HasSnaky 2 required_553_i3 envelope_553_i3 := by
  refine finite_compose HasSnaky 1 childrenC_553_i3 childrenD_553_i3 finite_children_work_553_i3 (5, 7)
    required_553_i3 envelope_553_i3 pivot_mem_553_i3 child_required_sub_553_i3 child_envelope_sub_553_i3 ?_
  intro b hb
  exact common_sub_553_i3 (mem_commonEnvelope childrenD_553_i3 b hb)

theorem finite_children_work_553_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_553_i2 j) (childrenD_553_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 6 (6, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_553_i3.mono (by decide +kernel)

theorem finite_row_works_553_i2 : FiniteTemplate HasSnaky 5 required_553_i2 envelope_553_i2 := by
  refine finite_compose HasSnaky 4 childrenC_553_i2 childrenD_553_i2 finite_children_work_553_i2 (5, 5)
    required_553_i2 envelope_553_i2 pivot_mem_553_i2 child_required_sub_553_i2 child_envelope_sub_553_i2 ?_
  intro b hb
  exact common_sub_553_i2 (mem_commonEnvelope childrenD_553_i2 b hb)

theorem finite_children_work_553_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_553_i1 j) (childrenD_553_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (7, 6)).mono (by decide +kernel)
  · exact finite_row_works_553_i2.mono (by decide +kernel)

theorem finite_row_works_553_i1 : FiniteTemplate HasSnaky 6 required_553_i1 envelope_553_i1 := by
  refine finite_compose HasSnaky 5 childrenC_553_i1 childrenD_553_i1 finite_children_work_553_i1 (5, 6)
    required_553_i1 envelope_553_i1 pivot_mem_553_i1 child_required_sub_553_i1 child_envelope_sub_553_i1 ?_
  intro b hb
  exact common_sub_553_i1 (mem_commonEnvelope childrenD_553_i1 b hb)

theorem finite_children_work_553_i6 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_553_i6 j) (childrenD_553_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 7 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_145 0 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_553_i6 : FiniteTemplate HasSnaky 6 required_553_i6 envelope_553_i6 := by
  refine finite_compose HasSnaky 5 childrenC_553_i6 childrenD_553_i6 finite_children_work_553_i6 (6, 4)
    required_553_i6 envelope_553_i6 pivot_mem_553_i6 child_required_sub_553_i6 child_envelope_sub_553_i6 ?_
  intro b hb
  exact common_sub_553_i6 (mem_commonEnvelope childrenD_553_i6 b hb)

theorem finite_children_work_553_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_553_i5 j) (childrenD_553_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_158 3 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_553_i6.mono (by decide +kernel)

theorem finite_row_works_553_i5 : FiniteTemplate HasSnaky 7 required_553_i5 envelope_553_i5 := by
  refine finite_compose HasSnaky 6 childrenC_553_i5 childrenD_553_i5 finite_children_work_553_i5 (7, 4)
    required_553_i5 envelope_553_i5 pivot_mem_553_i5 child_required_sub_553_i5 child_envelope_sub_553_i5 ?_
  intro b hb
  exact common_sub_553_i5 (mem_commonEnvelope childrenD_553_i5 b hb)

theorem finite_children_work_553_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_553_i4 j) (childrenD_553_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_553_i5.mono (by decide +kernel)

theorem finite_row_works_553_i4 : FiniteTemplate HasSnaky 8 required_553_i4 envelope_553_i4 := by
  refine finite_compose HasSnaky 7 childrenC_553_i4 childrenD_553_i4 finite_children_work_553_i4 (6, 7)
    required_553_i4 envelope_553_i4 pivot_mem_553_i4 child_required_sub_553_i4 child_envelope_sub_553_i4 ?_
  intro b hb
  exact common_sub_553_i4 (mem_commonEnvelope childrenD_553_i4 b hb)

theorem finite_children_work_553_i8 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_553_i8 j) (childrenD_553_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_247 3 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_553_i8 : FiniteTemplate HasSnaky 4 required_553_i8 envelope_553_i8 := by
  refine finite_compose HasSnaky 3 childrenC_553_i8 childrenD_553_i8 finite_children_work_553_i8 (4, 3)
    required_553_i8 envelope_553_i8 pivot_mem_553_i8 child_required_sub_553_i8 child_envelope_sub_553_i8 ?_
  intro b hb
  exact common_sub_553_i8 (mem_commonEnvelope childrenD_553_i8 b hb)

theorem finite_children_work_553_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_553_i7 j) (childrenD_553_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (7, 6)).mono (by decide +kernel)
  · exact finite_row_works_553_i8.mono (by decide +kernel)

theorem finite_row_works_553_i7 : FiniteTemplate HasSnaky 5 required_553_i7 envelope_553_i7 := by
  refine finite_compose HasSnaky 4 childrenC_553_i7 childrenD_553_i7 finite_children_work_553_i7 (5, 6)
    required_553_i7 envelope_553_i7 pivot_mem_553_i7 child_required_sub_553_i7 child_envelope_sub_553_i7 ?_
  intro b hb
  exact common_sub_553_i7 (mem_commonEnvelope childrenD_553_i7 b hb)

theorem finite_children_work_553_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_553_i0 j) (childrenD_553_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_433 3 (2, 7)).mono (by decide +kernel)
  · exact finite_row_works_553_i1.mono (by decide +kernel)
  · exact finite_row_works_553_i4.mono (by decide +kernel)
  · exact finite_row_works_553_i7.mono (by decide +kernel)

theorem finite_row_works_553_i0 : FiniteTemplate HasSnaky 9 required_553_i0 envelope_553_i0 := by
  refine finite_compose HasSnaky 8 childrenC_553_i0 childrenD_553_i0 finite_children_work_553_i0 (5, 4)
    required_553_i0 envelope_553_i0 pivot_mem_553_i0 child_required_sub_553_i0 child_envelope_sub_553_i0 ?_
  intro b hb
  exact common_sub_553_i0 (mem_commonEnvelope childrenD_553_i0 b hb)

theorem finite_children_work_553 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_553 j) (childrenD_553 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_107 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_163 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_538 0 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_552.mono (by decide +kernel)
  · exact finite_row_works_553_i0.mono (by decide +kernel)

theorem finite_row_works_553 : FiniteTemplate HasSnaky 14 required_553 envelope_553 := by
  refine finite_compose HasSnaky 13 childrenC_553 childrenD_553 finite_children_work_553 (7, 6)
    required_553 envelope_553 pivot_mem_553 child_required_sub_553 child_envelope_sub_553 ?_
  intro b hb
  exact common_sub_553 (mem_commonEnvelope childrenD_553 b hb)

theorem finite_children_work_557_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_557_i0 j) (childrenD_557_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_28 7 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 4 (1, 8)).mono (by decide +kernel)

theorem finite_row_works_557_i0 : FiniteTemplate HasSnaky 5 required_557_i0 envelope_557_i0 := by
  refine finite_compose HasSnaky 4 childrenC_557_i0 childrenD_557_i0 finite_children_work_557_i0 (4, 7)
    required_557_i0 envelope_557_i0 pivot_mem_557_i0 child_required_sub_557_i0 child_envelope_sub_557_i0 ?_
  intro b hb
  exact common_sub_557_i0 (mem_commonEnvelope childrenD_557_i0 b hb)

theorem finite_children_work_557_i4 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_557_i4 j) (childrenD_557_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_557_i4 : FiniteTemplate HasSnaky 2 required_557_i4 envelope_557_i4 := by
  refine finite_compose HasSnaky 1 childrenC_557_i4 childrenD_557_i4 finite_children_work_557_i4 (1, 5)
    required_557_i4 envelope_557_i4 pivot_mem_557_i4 child_required_sub_557_i4 child_envelope_sub_557_i4 ?_
  intro b hb
  exact common_sub_557_i4 (mem_commonEnvelope childrenD_557_i4 b hb)

theorem finite_children_work_557_i6 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_557_i6 j) (childrenD_557_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 7 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_392 7 (5, 4)).mono (by decide +kernel)

theorem finite_row_works_557_i6 : FiniteTemplate HasSnaky 7 required_557_i6 envelope_557_i6 := by
  refine finite_compose HasSnaky 6 childrenC_557_i6 childrenD_557_i6 finite_children_work_557_i6 (3, 4)
    required_557_i6 envelope_557_i6 pivot_mem_557_i6 child_required_sub_557_i6 child_envelope_sub_557_i6 ?_
  intro b hb
  exact common_sub_557_i6 (mem_commonEnvelope childrenD_557_i6 b hb)

theorem finite_children_work_557_i5 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_557_i5 j) (childrenD_557_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_557_i6.mono (by decide +kernel)

theorem finite_row_works_557_i5 : FiniteTemplate HasSnaky 8 required_557_i5 envelope_557_i5 := by
  refine finite_compose HasSnaky 7 childrenC_557_i5 childrenD_557_i5 finite_children_work_557_i5 (3, 3)
    required_557_i5 envelope_557_i5 pivot_mem_557_i5 child_required_sub_557_i5 child_envelope_sub_557_i5 ?_
  intro b hb
  exact common_sub_557_i5 (mem_commonEnvelope childrenD_557_i5 b hb)

theorem finite_children_work_557_i3 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_557_i3 j) (childrenD_557_i3 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_557_i4.mono (by decide +kernel)
  · exact finite_row_works_557_i5.mono (by decide +kernel)

theorem finite_row_works_557_i3 : FiniteTemplate HasSnaky 9 required_557_i3 envelope_557_i3 := by
  refine finite_compose HasSnaky 8 childrenC_557_i3 childrenD_557_i3 finite_children_work_557_i3 (2, 2)
    required_557_i3 envelope_557_i3 pivot_mem_557_i3 child_required_sub_557_i3 child_envelope_sub_557_i3 ?_
  intro b hb
  exact common_sub_557_i3 (mem_commonEnvelope childrenD_557_i3 b hb)

theorem finite_children_work_557_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_557_i2 j) (childrenD_557_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_42 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_152 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_557_i3.mono (by decide +kernel)

theorem finite_row_works_557_i2 : FiniteTemplate HasSnaky 10 required_557_i2 envelope_557_i2 := by
  refine finite_compose HasSnaky 9 childrenC_557_i2 childrenD_557_i2 finite_children_work_557_i2 (4, 3)
    required_557_i2 envelope_557_i2 pivot_mem_557_i2 child_required_sub_557_i2 child_envelope_sub_557_i2 ?_
  intro b hb
  exact common_sub_557_i2 (mem_commonEnvelope childrenD_557_i2 b hb)

theorem finite_children_work_557_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_557_i1 j) (childrenD_557_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_557_i2.mono (by decide +kernel)

theorem finite_row_works_557_i1 : FiniteTemplate HasSnaky 11 required_557_i1 envelope_557_i1 := by
  refine finite_compose HasSnaky 10 childrenC_557_i1 childrenD_557_i1 finite_children_work_557_i1 (3, 6)
    required_557_i1 envelope_557_i1 pivot_mem_557_i1 child_required_sub_557_i1 child_envelope_sub_557_i1 ?_
  intro b hb
  exact common_sub_557_i1 (mem_commonEnvelope childrenD_557_i1 b hb)

theorem finite_children_work_557 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_557 j) (childrenD_557 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_110 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_119 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_430 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_461 0 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_555 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_557_i0.mono (by decide +kernel)
  · exact finite_row_works_557_i1.mono (by decide +kernel)

theorem finite_row_works_557 : FiniteTemplate HasSnaky 14 required_557 envelope_557 := by
  refine finite_compose HasSnaky 13 childrenC_557 childrenD_557 finite_children_work_557 (4, 6)
    required_557 envelope_557 pivot_mem_557 child_required_sub_557 child_envelope_sub_557 ?_
  intro b hb
  exact common_sub_557 (mem_commonEnvelope childrenD_557 b hb)

theorem finite_children_work_582_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_582_i1 j) (childrenD_582_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_160 3 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_582_i1 : FiniteTemplate HasSnaky 4 required_582_i1 envelope_582_i1 := by
  refine finite_compose HasSnaky 3 childrenC_582_i1 childrenD_582_i1 finite_children_work_582_i1 (5, 6)
    required_582_i1 envelope_582_i1 pivot_mem_582_i1 child_required_sub_582_i1 child_envelope_sub_582_i1 ?_
  intro b hb
  exact common_sub_582_i1 (mem_commonEnvelope childrenD_582_i1 b hb)

theorem finite_children_work_582_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_582_i0 j) (childrenD_582_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_133 1 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_582_i1.mono (by decide +kernel)

theorem finite_row_works_582_i0 : FiniteTemplate HasSnaky 6 required_582_i0 envelope_582_i0 := by
  refine finite_compose HasSnaky 5 childrenC_582_i0 childrenD_582_i0 finite_children_work_582_i0 (4, 5)
    required_582_i0 envelope_582_i0 pivot_mem_582_i0 child_required_sub_582_i0 child_envelope_sub_582_i0 ?_
  intro b hb
  exact common_sub_582_i0 (mem_commonEnvelope childrenD_582_i0 b hb)

theorem finite_children_work_582_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_582_i2 j) (childrenD_582_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 3 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 3 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_109 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_424 1 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_582_i2 : FiniteTemplate HasSnaky 5 required_582_i2 envelope_582_i2 := by
  refine finite_compose HasSnaky 4 childrenC_582_i2 childrenD_582_i2 finite_children_work_582_i2 (3, 6)
    required_582_i2 envelope_582_i2 pivot_mem_582_i2 child_required_sub_582_i2 child_envelope_sub_582_i2 ?_
  intro b hb
  exact common_sub_582_i2 (mem_commonEnvelope childrenD_582_i2 b hb)

theorem finite_children_work_582_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_582_i3 j) (childrenD_582_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_383 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_432 5 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_582_i3 : FiniteTemplate HasSnaky 6 required_582_i3 envelope_582_i3 := by
  refine finite_compose HasSnaky 5 childrenC_582_i3 childrenD_582_i3 finite_children_work_582_i3 (4, 5)
    required_582_i3 envelope_582_i3 pivot_mem_582_i3 child_required_sub_582_i3 child_envelope_sub_582_i3 ?_
  intro b hb
  exact common_sub_582_i3 (mem_commonEnvelope childrenD_582_i3 b hb)

theorem finite_children_work_582 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_582 j) (childrenD_582 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_184 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_423 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_572 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_582_i0.mono (by decide +kernel)
  · exact finite_row_works_582_i2.mono (by decide +kernel)
  · exact finite_row_works_582_i3.mono (by decide +kernel)

theorem finite_row_works_582 : FiniteTemplate HasSnaky 14 required_582 envelope_582 := by
  refine finite_compose HasSnaky 13 childrenC_582 childrenD_582 finite_children_work_582 (4, 6)
    required_582 envelope_582 pivot_mem_582 child_required_sub_582 child_envelope_sub_582 ?_
  intro b hb
  exact common_sub_582 (mem_commonEnvelope childrenD_582 b hb)

end FiniteCongruenceChecks.SnakyFinite
