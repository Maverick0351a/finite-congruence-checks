/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06
import FiniteCards.Height06Part06

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_511_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_511_i1 j) (childrenD_511_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 0 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_511_i1 : FiniteTemplate HasSnaky 4 required_511_i1 envelope_511_i1 := by
  refine finite_compose HasSnaky 3 childrenC_511_i1 childrenD_511_i1 finite_children_work_511_i1 (4, 4)
    required_511_i1 envelope_511_i1 pivot_mem_511_i1 child_required_sub_511_i1 child_envelope_sub_511_i1 ?_
  intro b hb
  exact common_sub_511_i1 (mem_commonEnvelope childrenD_511_i1 b hb)

theorem finite_children_work_511_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_511_i3 j) (childrenD_511_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_221 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_511_i3 : FiniteTemplate HasSnaky 4 required_511_i3 envelope_511_i3 := by
  refine finite_compose HasSnaky 3 childrenC_511_i3 childrenD_511_i3 finite_children_work_511_i3 (3, 5)
    required_511_i3 envelope_511_i3 pivot_mem_511_i3 child_required_sub_511_i3 child_envelope_sub_511_i3 ?_
  intro b hb
  exact common_sub_511_i3 (mem_commonEnvelope childrenD_511_i3 b hb)

theorem finite_children_work_511_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_511_i2 j) (childrenD_511_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 4)).mono (by decide +kernel)
  · exact finite_row_works_511_i3.mono (by decide +kernel)

theorem finite_row_works_511_i2 : FiniteTemplate HasSnaky 5 required_511_i2 envelope_511_i2 := by
  refine finite_compose HasSnaky 4 childrenC_511_i2 childrenD_511_i2 finite_children_work_511_i2 (2, 4)
    required_511_i2 envelope_511_i2 pivot_mem_511_i2 child_required_sub_511_i2 child_envelope_sub_511_i2 ?_
  intro b hb
  exact common_sub_511_i2 (mem_commonEnvelope childrenD_511_i2 b hb)

theorem finite_children_work_511_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_511_i0 j) (childrenD_511_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_240 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_511_i1.mono (by decide +kernel)
  · exact finite_row_works_511_i2.mono (by decide +kernel)

theorem finite_row_works_511_i0 : FiniteTemplate HasSnaky 6 required_511_i0 envelope_511_i0 := by
  refine finite_compose HasSnaky 5 childrenC_511_i0 childrenD_511_i0 finite_children_work_511_i0 (3, 4)
    required_511_i0 envelope_511_i0 pivot_mem_511_i0 child_required_sub_511_i0 child_envelope_sub_511_i0 ?_
  intro b hb
  exact common_sub_511_i0 (mem_commonEnvelope childrenD_511_i0 b hb)

theorem finite_children_work_511 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_511 j) (childrenD_511 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 6 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_511_i0.mono (by decide +kernel)

theorem finite_row_works_511 : FiniteTemplate HasSnaky 7 required_511 envelope_511 := by
  refine finite_compose HasSnaky 6 childrenC_511 childrenD_511 finite_children_work_511 (1, 4)
    required_511 envelope_511 pivot_mem_511 child_required_sub_511 child_envelope_sub_511 ?_
  intro b hb
  exact common_sub_511 (mem_commonEnvelope childrenD_511 b hb)

theorem finite_children_work_522_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_522_i0 j) (childrenD_522_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_416 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_522_i0 : FiniteTemplate HasSnaky 6 required_522_i0 envelope_522_i0 := by
  refine finite_compose HasSnaky 5 childrenC_522_i0 childrenD_522_i0 finite_children_work_522_i0 (1, 3)
    required_522_i0 envelope_522_i0 pivot_mem_522_i0 child_required_sub_522_i0 child_envelope_sub_522_i0 ?_
  intro b hb
  exact common_sub_522_i0 (mem_commonEnvelope childrenD_522_i0 b hb)

theorem finite_children_work_522 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_522 j) (childrenD_522 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_522_i0.mono (by decide +kernel)

theorem finite_row_works_522 : FiniteTemplate HasSnaky 7 required_522 envelope_522 := by
  refine finite_compose HasSnaky 6 childrenC_522 childrenD_522 finite_children_work_522 (4, 2)
    required_522 envelope_522 pivot_mem_522 child_required_sub_522 child_envelope_sub_522 ?_
  intro b hb
  exact common_sub_522 (mem_commonEnvelope childrenD_522 b hb)

theorem finite_children_work_526 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_526 j) (childrenD_526 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_525.mono (by decide +kernel)

theorem finite_row_works_526 : FiniteTemplate HasSnaky 7 required_526 envelope_526 := by
  refine finite_compose HasSnaky 6 childrenC_526 childrenD_526 finite_children_work_526 (3, 1)
    required_526 envelope_526 pivot_mem_526 child_required_sub_526 child_envelope_sub_526 ?_
  intro b hb
  exact common_sub_526 (mem_commonEnvelope childrenD_526 b hb)

theorem finite_children_work_542_i3 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_542_i3 j) (childrenD_542_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_1 4 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_542_i3 : FiniteTemplate HasSnaky 2 required_542_i3 envelope_542_i3 := by
  refine finite_compose HasSnaky 1 childrenC_542_i3 childrenD_542_i3 finite_children_work_542_i3 (5, 2)
    required_542_i3 envelope_542_i3 pivot_mem_542_i3 child_required_sub_542_i3 child_envelope_sub_542_i3 ?_
  intro b hb
  exact common_sub_542_i3 (mem_commonEnvelope childrenD_542_i3 b hb)

theorem finite_children_work_542_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_542_i2 j) (childrenD_542_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_29 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_542_i3.mono (by decide +kernel)

theorem finite_row_works_542_i2 : FiniteTemplate HasSnaky 4 required_542_i2 envelope_542_i2 := by
  refine finite_compose HasSnaky 3 childrenC_542_i2 childrenD_542_i2 finite_children_work_542_i2 (4, 3)
    required_542_i2 envelope_542_i2 pivot_mem_542_i2 child_required_sub_542_i2 child_envelope_sub_542_i2 ?_
  intro b hb
  exact common_sub_542_i2 (mem_commonEnvelope childrenD_542_i2 b hb)

theorem finite_children_work_542_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_542_i1 j) (childrenD_542_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_542_i2.mono (by decide +kernel)

theorem finite_row_works_542_i1 : FiniteTemplate HasSnaky 5 required_542_i1 envelope_542_i1 := by
  refine finite_compose HasSnaky 4 childrenC_542_i1 childrenD_542_i1 finite_children_work_542_i1 (4, 2)
    required_542_i1 envelope_542_i1 pivot_mem_542_i1 child_required_sub_542_i1 child_envelope_sub_542_i1 ?_
  intro b hb
  exact common_sub_542_i1 (mem_commonEnvelope childrenD_542_i1 b hb)

theorem finite_children_work_542_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_542_i0 j) (childrenD_542_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_542_i1.mono (by decide +kernel)

theorem finite_row_works_542_i0 : FiniteTemplate HasSnaky 6 required_542_i0 envelope_542_i0 := by
  refine finite_compose HasSnaky 5 childrenC_542_i0 childrenD_542_i0 finite_children_work_542_i0 (2, 1)
    required_542_i0 envelope_542_i0 pivot_mem_542_i0 child_required_sub_542_i0 child_envelope_sub_542_i0 ?_
  intro b hb
  exact common_sub_542_i0 (mem_commonEnvelope childrenD_542_i0 b hb)

theorem finite_children_work_542 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_542 j) (childrenD_542 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 7 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_542_i0.mono (by decide +kernel)

theorem finite_row_works_542 : FiniteTemplate HasSnaky 7 required_542 envelope_542 := by
  refine finite_compose HasSnaky 6 childrenC_542 childrenD_542 finite_children_work_542 (1, 3)
    required_542 envelope_542 pivot_mem_542 child_required_sub_542 child_envelope_sub_542 ?_
  intro b hb
  exact common_sub_542 (mem_commonEnvelope childrenD_542 b hb)

theorem finite_children_work_554_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_554_i0 j) (childrenD_554_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_515 0 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_554_i0 : FiniteTemplate HasSnaky 6 required_554_i0 envelope_554_i0 := by
  refine finite_compose HasSnaky 5 childrenC_554_i0 childrenD_554_i0 finite_children_work_554_i0 (1, 3)
    required_554_i0 envelope_554_i0 pivot_mem_554_i0 child_required_sub_554_i0 child_envelope_sub_554_i0 ?_
  intro b hb
  exact common_sub_554_i0 (mem_commonEnvelope childrenD_554_i0 b hb)

theorem finite_children_work_554 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_554 j) (childrenD_554 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_554_i0.mono (by decide +kernel)

theorem finite_row_works_554 : FiniteTemplate HasSnaky 7 required_554 envelope_554 := by
  refine finite_compose HasSnaky 6 childrenC_554 childrenD_554 finite_children_work_554 (1, 4)
    required_554 envelope_554 pivot_mem_554 child_required_sub_554 child_envelope_sub_554 ?_
  intro b hb
  exact common_sub_554 (mem_commonEnvelope childrenD_554 b hb)

theorem finite_children_work_565_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_565_i0 j) (childrenD_565_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_565_i0 : FiniteTemplate HasSnaky 6 required_565_i0 envelope_565_i0 := by
  refine finite_compose HasSnaky 5 childrenC_565_i0 childrenD_565_i0 finite_children_work_565_i0 (5, 3)
    required_565_i0 envelope_565_i0 pivot_mem_565_i0 child_required_sub_565_i0 child_envelope_sub_565_i0 ?_
  intro b hb
  exact common_sub_565_i0 (mem_commonEnvelope childrenD_565_i0 b hb)

theorem finite_children_work_565_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_565_i1 j) (childrenD_565_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_142.mono (by decide +kernel)

theorem finite_row_works_565_i1 : FiniteTemplate HasSnaky 6 required_565_i1 envelope_565_i1 := by
  refine finite_compose HasSnaky 5 childrenC_565_i1 childrenD_565_i1 finite_children_work_565_i1 (1, 3)
    required_565_i1 envelope_565_i1 pivot_mem_565_i1 child_required_sub_565_i1 child_envelope_sub_565_i1 ?_
  intro b hb
  exact common_sub_565_i1 (mem_commonEnvelope childrenD_565_i1 b hb)

theorem finite_children_work_565 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_565 j) (childrenD_565 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_140 3 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_565_i0.mono (by decide +kernel)
  · exact finite_row_works_565_i1.mono (by decide +kernel)

theorem finite_row_works_565 : FiniteTemplate HasSnaky 7 required_565 envelope_565 := by
  refine finite_compose HasSnaky 6 childrenC_565 childrenD_565 finite_children_work_565 (5, 2)
    required_565 envelope_565 pivot_mem_565 child_required_sub_565 child_envelope_sub_565 ?_
  intro b hb
  exact common_sub_565 (mem_commonEnvelope childrenD_565 b hb)

theorem finite_children_work_576_i2 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_576_i2 j) (childrenD_576_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_576_i2 : FiniteTemplate HasSnaky 2 required_576_i2 envelope_576_i2 := by
  refine finite_compose HasSnaky 1 childrenC_576_i2 childrenD_576_i2 finite_children_work_576_i2 (5, 5)
    required_576_i2 envelope_576_i2 pivot_mem_576_i2 child_required_sub_576_i2 child_envelope_sub_576_i2 ?_
  intro b hb
  exact common_sub_576_i2 (mem_commonEnvelope childrenD_576_i2 b hb)

theorem finite_children_work_576_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_576_i3 j) (childrenD_576_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_87 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_576_i3 : FiniteTemplate HasSnaky 4 required_576_i3 envelope_576_i3 := by
  refine finite_compose HasSnaky 3 childrenC_576_i3 childrenD_576_i3 finite_children_work_576_i3 (3, 2)
    required_576_i3 envelope_576_i3 pivot_mem_576_i3 child_required_sub_576_i3 child_envelope_sub_576_i3 ?_
  intro b hb
  exact common_sub_576_i3 (mem_commonEnvelope childrenD_576_i3 b hb)

theorem finite_children_work_576_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_576_i1 j) (childrenD_576_i1 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_576_i2.mono (by decide +kernel)
  · exact finite_row_works_576_i3.mono (by decide +kernel)

theorem finite_row_works_576_i1 : FiniteTemplate HasSnaky 5 required_576_i1 envelope_576_i1 := by
  refine finite_compose HasSnaky 4 childrenC_576_i1 childrenD_576_i1 finite_children_work_576_i1 (4, 5)
    required_576_i1 envelope_576_i1 pivot_mem_576_i1 child_required_sub_576_i1 child_envelope_sub_576_i1 ?_
  intro b hb
  exact common_sub_576_i1 (mem_commonEnvelope childrenD_576_i1 b hb)

theorem finite_children_work_576_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_576_i4 j) (childrenD_576_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_87 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_215 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_576_i4 : FiniteTemplate HasSnaky 4 required_576_i4 envelope_576_i4 := by
  refine finite_compose HasSnaky 3 childrenC_576_i4 childrenD_576_i4 finite_children_work_576_i4 (3, 2)
    required_576_i4 envelope_576_i4 pivot_mem_576_i4 child_required_sub_576_i4 child_envelope_sub_576_i4 ?_
  intro b hb
  exact common_sub_576_i4 (mem_commonEnvelope childrenD_576_i4 b hb)

theorem finite_children_work_576_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_576_i0 j) (childrenD_576_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_246 6 (5, 5)).mono (by decide +kernel)
  · exact finite_row_works_576_i1.mono (by decide +kernel)
  · exact finite_row_works_576_i4.mono (by decide +kernel)

theorem finite_row_works_576_i0 : FiniteTemplate HasSnaky 6 required_576_i0 envelope_576_i0 := by
  refine finite_compose HasSnaky 5 childrenC_576_i0 childrenD_576_i0 finite_children_work_576_i0 (4, 2)
    required_576_i0 envelope_576_i0 pivot_mem_576_i0 child_required_sub_576_i0 child_envelope_sub_576_i0 ?_
  intro b hb
  exact common_sub_576_i0 (mem_commonEnvelope childrenD_576_i0 b hb)

theorem finite_children_work_576 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_576 j) (childrenD_576 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (7, 4)).mono (by decide +kernel)
  · exact finite_row_works_576_i0.mono (by decide +kernel)

theorem finite_row_works_576 : FiniteTemplate HasSnaky 7 required_576 envelope_576 := by
  refine finite_compose HasSnaky 6 childrenC_576 childrenD_576 finite_children_work_576 (4, 3)
    required_576 envelope_576 pivot_mem_576 child_required_sub_576 child_envelope_sub_576 ?_
  intro b hb
  exact common_sub_576 (mem_commonEnvelope childrenD_576 b hb)

end FiniteCongruenceChecks.SnakyFinite
