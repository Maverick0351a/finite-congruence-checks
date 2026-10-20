/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_529_i4 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_529_i4 j) (childrenD_529_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 6 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_4 4 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_529_i4 : FiniteTemplate HasSnaky 2 required_529_i4 envelope_529_i4 := by
  refine finite_compose HasSnaky 1 childrenC_529_i4 childrenD_529_i4 finite_children_work_529_i4 (3, 6)
    required_529_i4 envelope_529_i4 pivot_mem_529_i4 child_required_sub_529_i4 child_envelope_sub_529_i4 ?_
  intro b hb
  exact common_sub_529_i4 (mem_commonEnvelope childrenD_529_i4 b hb)

theorem finite_children_work_529_i5 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_529_i5 j) (childrenD_529_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 3 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_351 4 (4, 7)).mono (by decide +kernel)

theorem finite_row_works_529_i5 : FiniteTemplate HasSnaky 5 required_529_i5 envelope_529_i5 := by
  refine finite_compose HasSnaky 4 childrenC_529_i5 childrenD_529_i5 finite_children_work_529_i5 (7, 3)
    required_529_i5 envelope_529_i5 pivot_mem_529_i5 child_required_sub_529_i5 child_envelope_sub_529_i5 ?_
  intro b hb
  exact common_sub_529_i5 (mem_commonEnvelope childrenD_529_i5 b hb)

theorem finite_children_work_529_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_529_i3 j) (childrenD_529_i3 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_529_i4.mono (by decide +kernel)
  · exact finite_row_works_529_i5.mono (by decide +kernel)

theorem finite_row_works_529_i3 : FiniteTemplate HasSnaky 6 required_529_i3 envelope_529_i3 := by
  refine finite_compose HasSnaky 5 childrenC_529_i3 childrenD_529_i3 finite_children_work_529_i3 (7, 5)
    required_529_i3 envelope_529_i3 pivot_mem_529_i3 child_required_sub_529_i3 child_envelope_sub_529_i3 ?_
  intro b hb
  exact common_sub_529_i3 (mem_commonEnvelope childrenD_529_i3 b hb)

theorem finite_children_work_529_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_529_i2 j) (childrenD_529_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_529_i3.mono (by decide +kernel)

theorem finite_row_works_529_i2 : FiniteTemplate HasSnaky 7 required_529_i2 envelope_529_i2 := by
  refine finite_compose HasSnaky 6 childrenC_529_i2 childrenD_529_i2 finite_children_work_529_i2 (4, 6)
    required_529_i2 envelope_529_i2 pivot_mem_529_i2 child_required_sub_529_i2 child_envelope_sub_529_i2 ?_
  intro b hb
  exact common_sub_529_i2 (mem_commonEnvelope childrenD_529_i2 b hb)

theorem finite_children_work_529_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_529_i1 j) (childrenD_529_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_529_i2.mono (by decide +kernel)

theorem finite_row_works_529_i1 : FiniteTemplate HasSnaky 8 required_529_i1 envelope_529_i1 := by
  refine finite_compose HasSnaky 7 childrenC_529_i1 childrenD_529_i1 finite_children_work_529_i1 (6, 6)
    required_529_i1 envelope_529_i1 pivot_mem_529_i1 child_required_sub_529_i1 child_envelope_sub_529_i1 ?_
  intro b hb
  exact common_sub_529_i1 (mem_commonEnvelope childrenD_529_i1 b hb)

theorem finite_children_work_529_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_529_i0 j) (childrenD_529_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_133 3 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_529_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_505 7 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_529_i0 : FiniteTemplate HasSnaky 9 required_529_i0 envelope_529_i0 := by
  refine finite_compose HasSnaky 8 childrenC_529_i0 childrenD_529_i0 finite_children_work_529_i0 (5, 3)
    required_529_i0 envelope_529_i0 pivot_mem_529_i0 child_required_sub_529_i0 child_envelope_sub_529_i0 ?_
  intro b hb
  exact common_sub_529_i0 (mem_commonEnvelope childrenD_529_i0 b hb)

theorem finite_children_work_529 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_529 j) (childrenD_529 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 2 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_528 0 (4, 0)).mono (by decide +kernel)
  · exact finite_row_works_529_i0.mono (by decide +kernel)

theorem finite_row_works_529 : FiniteTemplate HasSnaky 10 required_529 envelope_529 := by
  refine finite_compose HasSnaky 9 childrenC_529 childrenD_529 finite_children_work_529 (5, 6)
    required_529 envelope_529 pivot_mem_529 child_required_sub_529 child_envelope_sub_529 ?_
  intro b hb
  exact common_sub_529 (mem_commonEnvelope childrenD_529 b hb)

theorem finite_children_work_535 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_535 j) (childrenD_535 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_345 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_421 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_522 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_530 4 (1, 8)).mono (by decide +kernel)
  · exact finite_row_works_532.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_533 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_534 4 (0, 8)).mono (by decide +kernel)

theorem finite_row_works_535 : FiniteTemplate HasSnaky 10 required_535 envelope_535 := by
  refine finite_compose HasSnaky 9 childrenC_535 childrenD_535 finite_children_work_535 (3, 5)
    required_535 envelope_535 pivot_mem_535 child_required_sub_535 child_envelope_sub_535 ?_
  intro b hb
  exact common_sub_535 (mem_commonEnvelope childrenD_535 b hb)

theorem finite_children_work_540_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_540_i0 j) (childrenD_540_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_237 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_281 5 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_540_i0 : FiniteTemplate HasSnaky 6 required_540_i0 envelope_540_i0 := by
  refine finite_compose HasSnaky 5 childrenC_540_i0 childrenD_540_i0 finite_children_work_540_i0 (2, 3)
    required_540_i0 envelope_540_i0 pivot_mem_540_i0 child_required_sub_540_i0 child_envelope_sub_540_i0 ?_
  intro b hb
  exact common_sub_540_i0 (mem_commonEnvelope childrenD_540_i0 b hb)

theorem finite_children_work_540_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_540_i3 j) (childrenD_540_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_164 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_199 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_283 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_540_i3 : FiniteTemplate HasSnaky 7 required_540_i3 envelope_540_i3 := by
  refine finite_compose HasSnaky 6 childrenC_540_i3 childrenD_540_i3 finite_children_work_540_i3 (4, 4)
    required_540_i3 envelope_540_i3 pivot_mem_540_i3 child_required_sub_540_i3 child_envelope_sub_540_i3 ?_
  intro b hb
  exact common_sub_540_i3 (mem_commonEnvelope childrenD_540_i3 b hb)

theorem finite_children_work_540_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_540_i2 j) (childrenD_540_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_170 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_540_i3.mono (by decide +kernel)

theorem finite_row_works_540_i2 : FiniteTemplate HasSnaky 8 required_540_i2 envelope_540_i2 := by
  refine finite_compose HasSnaky 7 childrenC_540_i2 childrenD_540_i2 finite_children_work_540_i2 (4, 5)
    required_540_i2 envelope_540_i2 pivot_mem_540_i2 child_required_sub_540_i2 child_envelope_sub_540_i2 ?_
  intro b hb
  exact common_sub_540_i2 (mem_commonEnvelope childrenD_540_i2 b hb)

theorem finite_children_work_540_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_540_i1 j) (childrenD_540_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 2 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_540_i2.mono (by decide +kernel)

theorem finite_row_works_540_i1 : FiniteTemplate HasSnaky 9 required_540_i1 envelope_540_i1 := by
  refine finite_compose HasSnaky 8 childrenC_540_i1 childrenD_540_i1 finite_children_work_540_i1 (0, 6)
    required_540_i1 envelope_540_i1 pivot_mem_540_i1 child_required_sub_540_i1 child_envelope_sub_540_i1 ?_
  intro b hb
  exact common_sub_540_i1 (mem_commonEnvelope childrenD_540_i1 b hb)

theorem finite_children_work_540 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_540 j) (childrenD_540 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 4 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_540_i0.mono (by decide +kernel)
  · exact finite_row_works_540_i1.mono (by decide +kernel)

theorem finite_row_works_540 : FiniteTemplate HasSnaky 10 required_540 envelope_540 := by
  refine finite_compose HasSnaky 9 childrenC_540 childrenD_540 finite_children_work_540 (4, 3)
    required_540 envelope_540 pivot_mem_540 child_required_sub_540 child_envelope_sub_540 ?_
  intro b hb
  exact common_sub_540 (mem_commonEnvelope childrenD_540 b hb)

theorem finite_children_work_541_i6 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_541_i6 j) (childrenD_541_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_541_i6 : FiniteTemplate HasSnaky 3 required_541_i6 envelope_541_i6 := by
  refine finite_compose HasSnaky 2 childrenC_541_i6 childrenD_541_i6 finite_children_work_541_i6 (4, 2)
    required_541_i6 envelope_541_i6 pivot_mem_541_i6 child_required_sub_541_i6 child_envelope_sub_541_i6 ?_
  intro b hb
  exact common_sub_541_i6 (mem_commonEnvelope childrenD_541_i6 b hb)

theorem finite_children_work_541_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_541_i5 j) (childrenD_541_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_170 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_541_i6.mono (by decide +kernel)

theorem finite_row_works_541_i5 : FiniteTemplate HasSnaky 4 required_541_i5 envelope_541_i5 := by
  refine finite_compose HasSnaky 3 childrenC_541_i5 childrenD_541_i5 finite_children_work_541_i5 (4, 3)
    required_541_i5 envelope_541_i5 pivot_mem_541_i5 child_required_sub_541_i5 child_envelope_sub_541_i5 ?_
  intro b hb
  exact common_sub_541_i5 (mem_commonEnvelope childrenD_541_i5 b hb)

theorem finite_children_work_541_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_541_i4 j) (childrenD_541_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 4 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_86.mono (by decide +kernel)
  · exact finite_row_works_541_i5.mono (by decide +kernel)

theorem finite_row_works_541_i4 : FiniteTemplate HasSnaky 5 required_541_i4 envelope_541_i4 := by
  refine finite_compose HasSnaky 4 childrenC_541_i4 childrenD_541_i4 finite_children_work_541_i4 (3, 4)
    required_541_i4 envelope_541_i4 pivot_mem_541_i4 child_required_sub_541_i4 child_envelope_sub_541_i4 ?_
  intro b hb
  exact common_sub_541_i4 (mem_commonEnvelope childrenD_541_i4 b hb)

theorem finite_children_work_541_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_541_i3 j) (childrenD_541_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 5)).mono (by decide +kernel)
  · exact finite_row_works_541_i4.mono (by decide +kernel)

theorem finite_row_works_541_i3 : FiniteTemplate HasSnaky 6 required_541_i3 envelope_541_i3 := by
  refine finite_compose HasSnaky 5 childrenC_541_i3 childrenD_541_i3 finite_children_work_541_i3 (3, 5)
    required_541_i3 envelope_541_i3 pivot_mem_541_i3 child_required_sub_541_i3 child_envelope_sub_541_i3 ?_
  intro b hb
  exact common_sub_541_i3 (mem_commonEnvelope childrenD_541_i3 b hb)

theorem finite_children_work_541_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_541_i2 j) (childrenD_541_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 3 (1, 9)).mono (by decide +kernel)
  · exact finite_row_works_541_i3.mono (by decide +kernel)

theorem finite_row_works_541_i2 : FiniteTemplate HasSnaky 7 required_541_i2 envelope_541_i2 := by
  refine finite_compose HasSnaky 6 childrenC_541_i2 childrenD_541_i2 finite_children_work_541_i2 (2, 5)
    required_541_i2 envelope_541_i2 pivot_mem_541_i2 child_required_sub_541_i2 child_envelope_sub_541_i2 ?_
  intro b hb
  exact common_sub_541_i2 (mem_commonEnvelope childrenD_541_i2 b hb)

theorem finite_children_work_541_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_541_i1 j) (childrenD_541_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 8)).mono (by decide +kernel)
  · exact finite_row_works_541_i2.mono (by decide +kernel)

theorem finite_row_works_541_i1 : FiniteTemplate HasSnaky 8 required_541_i1 envelope_541_i1 := by
  refine finite_compose HasSnaky 7 childrenC_541_i1 childrenD_541_i1 finite_children_work_541_i1 (0, 4)
    required_541_i1 envelope_541_i1 pivot_mem_541_i1 child_required_sub_541_i1 child_envelope_sub_541_i1 ?_
  intro b hb
  exact common_sub_541_i1 (mem_commonEnvelope childrenD_541_i1 b hb)

theorem finite_children_work_541_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_541_i0 j) (childrenD_541_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_541_i1.mono (by decide +kernel)

theorem finite_row_works_541_i0 : FiniteTemplate HasSnaky 9 required_541_i0 envelope_541_i0 := by
  refine finite_compose HasSnaky 8 childrenC_541_i0 childrenD_541_i0 finite_children_work_541_i0 (1, 9)
    required_541_i0 envelope_541_i0 pivot_mem_541_i0 child_required_sub_541_i0 child_envelope_sub_541_i0 ?_
  intro b hb
  exact common_sub_541_i0 (mem_commonEnvelope childrenD_541_i0 b hb)

theorem finite_children_work_541 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_541 j) (childrenD_541 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_541_i0.mono (by decide +kernel)

theorem finite_row_works_541 : FiniteTemplate HasSnaky 10 required_541 envelope_541 := by
  refine finite_compose HasSnaky 9 childrenC_541 childrenD_541 finite_children_work_541 (1, 8)
    required_541 envelope_541 pivot_mem_541 child_required_sub_541 child_envelope_sub_541 ?_
  intro b hb
  exact common_sub_541 (mem_commonEnvelope childrenD_541 b hb)

theorem finite_children_work_545_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_545_i0 j) (childrenD_545_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_84 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 5 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_419 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_545_i0 : FiniteTemplate HasSnaky 9 required_545_i0 envelope_545_i0 := by
  refine finite_compose HasSnaky 8 childrenC_545_i0 childrenD_545_i0 finite_children_work_545_i0 (1, 6)
    required_545_i0 envelope_545_i0 pivot_mem_545_i0 child_required_sub_545_i0 child_envelope_sub_545_i0 ?_
  intro b hb
  exact common_sub_545_i0 (mem_commonEnvelope childrenD_545_i0 b hb)

theorem finite_children_work_545 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_545 j) (childrenD_545 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_284 6 (2, 9)).mono (by decide +kernel)
  · exact finite_row_works_545_i0.mono (by decide +kernel)

theorem finite_row_works_545 : FiniteTemplate HasSnaky 10 required_545 envelope_545 := by
  refine finite_compose HasSnaky 9 childrenC_545 childrenD_545 finite_children_work_545 (1, 3)
    required_545 envelope_545 pivot_mem_545 child_required_sub_545 child_envelope_sub_545 ?_
  intro b hb
  exact common_sub_545 (mem_commonEnvelope childrenD_545 b hb)

end FiniteCongruenceChecks.SnakyFinite
