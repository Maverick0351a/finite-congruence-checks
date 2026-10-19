/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part03
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part04
import FiniteCards.Height10Part02
import FiniteCards.Height10Part03
import FiniteCards.Height10Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_517_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_517_i0 j) (childrenD_517_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_404 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_517_i0 : FiniteTemplate HasSnaky 8 required_517_i0 envelope_517_i0 := by
  refine finite_compose HasSnaky 7 childrenC_517_i0 childrenD_517_i0 finite_children_work_517_i0 (3, 4)
    required_517_i0 envelope_517_i0 pivot_mem_517_i0 child_required_sub_517_i0 child_envelope_sub_517_i0 ?_
  intro b hb
  exact common_sub_517_i0 (mem_commonEnvelope childrenD_517_i0 b hb)

theorem finite_children_work_517_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_517_i2 j) (childrenD_517_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_513 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_516 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_517_i2 : FiniteTemplate HasSnaky 9 required_517_i2 envelope_517_i2 := by
  refine finite_compose HasSnaky 8 childrenC_517_i2 childrenD_517_i2 finite_children_work_517_i2 (4, 5)
    required_517_i2 envelope_517_i2 pivot_mem_517_i2 child_required_sub_517_i2 child_envelope_sub_517_i2 ?_
  intro b hb
  exact common_sub_517_i2 (mem_commonEnvelope childrenD_517_i2 b hb)

theorem finite_children_work_517_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_517_i1 j) (childrenD_517_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_59 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_346 4 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_517_i2.mono (by decide +kernel)

theorem finite_row_works_517_i1 : FiniteTemplate HasSnaky 10 required_517_i1 envelope_517_i1 := by
  refine finite_compose HasSnaky 9 childrenC_517_i1 childrenD_517_i1 finite_children_work_517_i1 (4, 3)
    required_517_i1 envelope_517_i1 pivot_mem_517_i1 child_required_sub_517_i1 child_envelope_sub_517_i1 ?_
  intro b hb
  exact common_sub_517_i1 (mem_commonEnvelope childrenD_517_i1 b hb)

theorem finite_children_work_517_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_517_i4 j) (childrenD_517_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_429 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_517_i4 : FiniteTemplate HasSnaky 7 required_517_i4 envelope_517_i4 := by
  refine finite_compose HasSnaky 6 childrenC_517_i4 childrenD_517_i4 finite_children_work_517_i4 (4, 5)
    required_517_i4 envelope_517_i4 pivot_mem_517_i4 child_required_sub_517_i4 child_envelope_sub_517_i4 ?_
  intro b hb
  exact common_sub_517_i4 (mem_commonEnvelope childrenD_517_i4 b hb)

theorem finite_children_work_517_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_517_i3 j) (childrenD_517_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_36 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_59 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_346 4 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_517_i4.mono (by decide +kernel)

theorem finite_row_works_517_i3 : FiniteTemplate HasSnaky 8 required_517_i3 envelope_517_i3 := by
  refine finite_compose HasSnaky 7 childrenC_517_i3 childrenD_517_i3 finite_children_work_517_i3 (4, 3)
    required_517_i3 envelope_517_i3 pivot_mem_517_i3 child_required_sub_517_i3 child_envelope_sub_517_i3 ?_
  intro b hb
  exact common_sub_517_i3 (mem_commonEnvelope childrenD_517_i3 b hb)

theorem finite_children_work_517 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_517 j) (childrenD_517 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_74 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_517_i0.mono (by decide +kernel)
  · exact finite_row_works_517_i1.mono (by decide +kernel)
  · exact finite_row_works_517_i3.mono (by decide +kernel)

theorem finite_row_works_517 : FiniteTemplate HasSnaky 11 required_517 envelope_517 := by
  refine finite_compose HasSnaky 10 childrenC_517 childrenD_517 finite_children_work_517 (4, 4)
    required_517 envelope_517 pivot_mem_517 child_required_sub_517 child_envelope_sub_517 ?_
  intro b hb
  exact common_sub_517 (mem_commonEnvelope childrenD_517 b hb)

theorem finite_children_work_527_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_527_i0 j) (childrenD_527_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_198 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_527_i0 : FiniteTemplate HasSnaky 4 required_527_i0 envelope_527_i0 := by
  refine finite_compose HasSnaky 3 childrenC_527_i0 childrenD_527_i0 finite_children_work_527_i0 (2, 5)
    required_527_i0 envelope_527_i0 pivot_mem_527_i0 child_required_sub_527_i0 child_envelope_sub_527_i0 ?_
  intro b hb
  exact common_sub_527_i0 (mem_commonEnvelope childrenD_527_i0 b hb)

theorem finite_children_work_527_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_527_i2 j) (childrenD_527_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_392 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_417 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_420 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_521 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_522 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_526 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_527_i2 : FiniteTemplate HasSnaky 9 required_527_i2 envelope_527_i2 := by
  refine finite_compose HasSnaky 8 childrenC_527_i2 childrenD_527_i2 finite_children_work_527_i2 (3, 3)
    required_527_i2 envelope_527_i2 pivot_mem_527_i2 child_required_sub_527_i2 child_envelope_sub_527_i2 ?_
  intro b hb
  exact common_sub_527_i2 (mem_commonEnvelope childrenD_527_i2 b hb)

theorem finite_children_work_527_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_527_i1 j) (childrenD_527_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 2 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_527_i2.mono (by decide +kernel)

theorem finite_row_works_527_i1 : FiniteTemplate HasSnaky 10 required_527_i1 envelope_527_i1 := by
  refine finite_compose HasSnaky 9 childrenC_527_i1 childrenD_527_i1 finite_children_work_527_i1 (2, 5)
    required_527_i1 envelope_527_i1 pivot_mem_527_i1 child_required_sub_527_i1 child_envelope_sub_527_i1 ?_
  intro b hb
  exact common_sub_527_i1 (mem_commonEnvelope childrenD_527_i1 b hb)

theorem finite_children_work_527 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_527 j) (childrenD_527 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_206 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_527_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_405 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_527_i1.mono (by decide +kernel)

theorem finite_row_works_527 : FiniteTemplate HasSnaky 11 required_527 envelope_527 := by
  refine finite_compose HasSnaky 10 childrenC_527 childrenD_527 finite_children_work_527 (2, 2)
    required_527 envelope_527 pivot_mem_527 child_required_sub_527 child_envelope_sub_527 ?_
  intro b hb
  exact common_sub_527 (mem_commonEnvelope childrenD_527 b hb)

theorem finite_children_work_550 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_550 j) (childrenD_550 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_390 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_544 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 6 (6, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_546 2 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_548 2 (6, 0)).mono (by decide +kernel)

theorem finite_row_works_550 : FiniteTemplate HasSnaky 11 required_550 envelope_550 := by
  refine finite_compose HasSnaky 10 childrenC_550 childrenD_550 finite_children_work_550 (5, 6)
    required_550 envelope_550 pivot_mem_550 child_required_sub_550 child_envelope_sub_550 ?_
  intro b hb
  exact common_sub_550 (mem_commonEnvelope childrenD_550 b hb)

theorem finite_children_work_567_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_567_i4 j) (childrenD_567_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_92 7 (6, 5)).mono (by decide +kernel)

theorem finite_row_works_567_i4 : FiniteTemplate HasSnaky 5 required_567_i4 envelope_567_i4 := by
  refine finite_compose HasSnaky 4 childrenC_567_i4 childrenD_567_i4 finite_children_work_567_i4 (4, 3)
    required_567_i4 envelope_567_i4 pivot_mem_567_i4 child_required_sub_567_i4 child_envelope_sub_567_i4 ?_
  intro b hb
  exact common_sub_567_i4 (mem_commonEnvelope childrenD_567_i4 b hb)

theorem finite_children_work_567_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_567_i3 j) (childrenD_567_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_94 4 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_102 4 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_567_i4.mono (by decide +kernel)

theorem finite_row_works_567_i3 : FiniteTemplate HasSnaky 6 required_567_i3 envelope_567_i3 := by
  refine finite_compose HasSnaky 5 childrenC_567_i3 childrenD_567_i3 finite_children_work_567_i3 (4, 2)
    required_567_i3 envelope_567_i3 pivot_mem_567_i3 child_required_sub_567_i3 child_envelope_sub_567_i3 ?_
  intro b hb
  exact common_sub_567_i3 (mem_commonEnvelope childrenD_567_i3 b hb)

theorem finite_children_work_567_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_567_i2 j) (childrenD_567_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (7, 5)).mono (by decide +kernel)
  · exact finite_row_works_567_i3.mono (by decide +kernel)

theorem finite_row_works_567_i2 : FiniteTemplate HasSnaky 7 required_567_i2 envelope_567_i2 := by
  refine finite_compose HasSnaky 6 childrenC_567_i2 childrenD_567_i2 finite_children_work_567_i2 (4, 4)
    required_567_i2 envelope_567_i2 pivot_mem_567_i2 child_required_sub_567_i2 child_envelope_sub_567_i2 ?_
  intro b hb
  exact common_sub_567_i2 (mem_commonEnvelope childrenD_567_i2 b hb)

theorem finite_children_work_567_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_567_i1 j) (childrenD_567_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 3 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_235 7 (7, 6)).mono (by decide +kernel)
  · exact finite_row_works_567_i2.mono (by decide +kernel)

theorem finite_row_works_567_i1 : FiniteTemplate HasSnaky 8 required_567_i1 envelope_567_i1 := by
  refine finite_compose HasSnaky 7 childrenC_567_i1 childrenD_567_i1 finite_children_work_567_i1 (6, 5)
    required_567_i1 envelope_567_i1 pivot_mem_567_i1 child_required_sub_567_i1 child_envelope_sub_567_i1 ?_
  intro b hb
  exact common_sub_567_i1 (mem_commonEnvelope childrenD_567_i1 b hb)

theorem finite_children_work_567_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_567_i0 j) (childrenD_567_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_67 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_327 6 (6, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_504 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_567_i1.mono (by decide +kernel)

theorem finite_row_works_567_i0 : FiniteTemplate HasSnaky 10 required_567_i0 envelope_567_i0 := by
  refine finite_compose HasSnaky 9 childrenC_567_i0 childrenD_567_i0 finite_children_work_567_i0 (5, 5)
    required_567_i0 envelope_567_i0 pivot_mem_567_i0 child_required_sub_567_i0 child_envelope_sub_567_i0 ?_
  intro b hb
  exact common_sub_567_i0 (mem_commonEnvelope childrenD_567_i0 b hb)

theorem finite_children_work_567 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_567 j) (childrenD_567 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_560 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_563 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_567_i0.mono (by decide +kernel)

theorem finite_row_works_567 : FiniteTemplate HasSnaky 11 required_567 envelope_567 := by
  refine finite_compose HasSnaky 10 childrenC_567 childrenD_567 finite_children_work_567 (4, 5)
    required_567 envelope_567 pivot_mem_567 child_required_sub_567 child_envelope_sub_567 ?_
  intro b hb
  exact common_sub_567 (mem_commonEnvelope childrenD_567 b hb)

theorem finite_children_work_579 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_579 j) (childrenD_579 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_118 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_137 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_172 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_173 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_578 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_578 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_579 : FiniteTemplate HasSnaky 11 required_579 envelope_579 := by
  refine finite_compose HasSnaky 10 childrenC_579 childrenD_579 finite_children_work_579 (3, 4)
    required_579 envelope_579 pivot_mem_579 child_required_sub_579 child_envelope_sub_579 ?_
  intro b hb
  exact common_sub_579 (mem_commonEnvelope childrenD_579 b hb)

theorem finite_children_work_581 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_581 j) (childrenD_581 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_258 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_309 7 (7, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_578 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_578 5 (7, 3)).mono (by decide +kernel)

theorem finite_row_works_581 : FiniteTemplate HasSnaky 11 required_581 envelope_581 := by
  refine finite_compose HasSnaky 10 childrenC_581 childrenD_581 finite_children_work_581 (4, 6)
    required_581 envelope_581 pivot_mem_581 child_required_sub_581 child_envelope_sub_581 ?_
  intro b hb
  exact common_sub_581 (mem_commonEnvelope childrenD_581 b hb)

theorem finite_children_work_586 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_586 j) (childrenD_586 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_179.mono (by decide +kernel)
  · exact finite_row_works_585.mono (by decide +kernel)

theorem finite_row_works_586 : FiniteTemplate HasSnaky 11 required_586 envelope_586 := by
  refine finite_compose HasSnaky 10 childrenC_586 childrenD_586 finite_children_work_586 (4, 2)
    required_586 envelope_586 pivot_mem_586 child_required_sub_586 child_envelope_sub_586 ?_
  intro b hb
  exact common_sub_586 (mem_commonEnvelope childrenD_586 b hb)

theorem finite_children_work_589 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_589 j) (childrenD_589 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_585 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_589 : FiniteTemplate HasSnaky 11 required_589 envelope_589 := by
  refine finite_compose HasSnaky 10 childrenC_589 childrenD_589 finite_children_work_589 (4, 2)
    required_589 envelope_589 pivot_mem_589 child_required_sub_589 child_envelope_sub_589 ?_
  intro b hb
  exact common_sub_589 (mem_commonEnvelope childrenD_589 b hb)

end FiniteCongruenceChecks.SnakyFinite
