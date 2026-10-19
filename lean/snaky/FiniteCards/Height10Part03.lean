/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part04
import FiniteCards.Height07Part03
import FiniteCards.Height08Part01
import FiniteCards.Height08Part04
import FiniteCards.Height09Part03
import FiniteCards.Height09Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_546_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_546_i4 j) (childrenD_546_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 1 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_546_i4 : FiniteTemplate HasSnaky 5 required_546_i4 envelope_546_i4 := by
  refine finite_compose HasSnaky 4 childrenC_546_i4 childrenD_546_i4 finite_children_work_546_i4 (3, 6)
    required_546_i4 envelope_546_i4 pivot_mem_546_i4 child_required_sub_546_i4 child_envelope_sub_546_i4 ?_
  intro b hb
  exact common_sub_546_i4 (mem_commonEnvelope childrenD_546_i4 b hb)

theorem finite_children_work_546_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_546_i3 j) (childrenD_546_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_546_i4.mono (by decide +kernel)

theorem finite_row_works_546_i3 : FiniteTemplate HasSnaky 6 required_546_i3 envelope_546_i3 := by
  refine finite_compose HasSnaky 5 childrenC_546_i3 childrenD_546_i3 finite_children_work_546_i3 (0, 6)
    required_546_i3 envelope_546_i3 pivot_mem_546_i3 child_required_sub_546_i3 child_envelope_sub_546_i3 ?_
  intro b hb
  exact common_sub_546_i3 (mem_commonEnvelope childrenD_546_i3 b hb)

theorem finite_children_work_546_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_546_i2 j) (childrenD_546_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_546_i3.mono (by decide +kernel)

theorem finite_row_works_546_i2 : FiniteTemplate HasSnaky 7 required_546_i2 envelope_546_i2 := by
  refine finite_compose HasSnaky 6 childrenC_546_i2 childrenD_546_i2 finite_children_work_546_i2 (2, 6)
    required_546_i2 envelope_546_i2 pivot_mem_546_i2 child_required_sub_546_i2 child_envelope_sub_546_i2 ?_
  intro b hb
  exact common_sub_546_i2 (mem_commonEnvelope childrenD_546_i2 b hb)

theorem finite_children_work_546_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_546_i1 j) (childrenD_546_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_546_i2.mono (by decide +kernel)

theorem finite_row_works_546_i1 : FiniteTemplate HasSnaky 8 required_546_i1 envelope_546_i1 := by
  refine finite_compose HasSnaky 7 childrenC_546_i1 childrenD_546_i1 finite_children_work_546_i1 (2, 3)
    required_546_i1 envelope_546_i1 pivot_mem_546_i1 child_required_sub_546_i1 child_envelope_sub_546_i1 ?_
  intro b hb
  exact common_sub_546_i1 (mem_commonEnvelope childrenD_546_i1 b hb)

theorem finite_children_work_546_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_546_i0 j) (childrenD_546_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 6 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_62 4 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_546_i1.mono (by decide +kernel)

theorem finite_row_works_546_i0 : FiniteTemplate HasSnaky 9 required_546_i0 envelope_546_i0 := by
  refine finite_compose HasSnaky 8 childrenC_546_i0 childrenD_546_i0 finite_children_work_546_i0 (1, 3)
    required_546_i0 envelope_546_i0 pivot_mem_546_i0 child_required_sub_546_i0 child_envelope_sub_546_i0 ?_
  intro b hb
  exact common_sub_546_i0 (mem_commonEnvelope childrenD_546_i0 b hb)

theorem finite_children_work_546 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_546 j) (childrenD_546 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 2 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_546_i0.mono (by decide +kernel)

theorem finite_row_works_546 : FiniteTemplate HasSnaky 10 required_546 envelope_546 := by
  refine finite_compose HasSnaky 9 childrenC_546 childrenD_546 finite_children_work_546 (1, 6)
    required_546 envelope_546 pivot_mem_546 child_required_sub_546 child_envelope_sub_546 ?_
  intro b hb
  exact common_sub_546 (mem_commonEnvelope childrenD_546 b hb)

theorem finite_children_work_556_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_556_i0 j) (childrenD_556_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_115 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_171 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 4 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 0 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_285 4 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_556_i0 : FiniteTemplate HasSnaky 9 required_556_i0 envelope_556_i0 := by
  refine finite_compose HasSnaky 8 childrenC_556_i0 childrenD_556_i0 finite_children_work_556_i0 (5, 4)
    required_556_i0 envelope_556_i0 pivot_mem_556_i0 child_required_sub_556_i0 child_envelope_sub_556_i0 ?_
  intro b hb
  exact common_sub_556_i0 (mem_commonEnvelope childrenD_556_i0 b hb)

theorem finite_children_work_556 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_556 j) (childrenD_556 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact finite_row_works_556_i0.mono (by decide +kernel)

theorem finite_row_works_556 : FiniteTemplate HasSnaky 10 required_556 envelope_556 := by
  refine finite_compose HasSnaky 9 childrenC_556 childrenD_556 finite_children_work_556 (2, 4)
    required_556 envelope_556 pivot_mem_556 child_required_sub_556 child_envelope_sub_556 ?_
  intro b hb
  exact common_sub_556 (mem_commonEnvelope childrenD_556 b hb)

theorem finite_children_work_560_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_560_i4 j) (childrenD_560_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_156 4 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_560_i4 : FiniteTemplate HasSnaky 4 required_560_i4 envelope_560_i4 := by
  refine finite_compose HasSnaky 3 childrenC_560_i4 childrenD_560_i4 finite_children_work_560_i4 (5, 2)
    required_560_i4 envelope_560_i4 pivot_mem_560_i4 child_required_sub_560_i4 child_envelope_sub_560_i4 ?_
  intro b hb
  exact common_sub_560_i4 (mem_commonEnvelope childrenD_560_i4 b hb)

theorem finite_children_work_560_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_560_i3 j) (childrenD_560_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 5 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 5 (6, 1)).mono (by decide +kernel)
  · exact finite_row_works_560_i4.mono (by decide +kernel)

theorem finite_row_works_560_i3 : FiniteTemplate HasSnaky 5 required_560_i3 envelope_560_i3 := by
  refine finite_compose HasSnaky 4 childrenC_560_i3 childrenD_560_i3 finite_children_work_560_i3 (5, 1)
    required_560_i3 envelope_560_i3 pivot_mem_560_i3 child_required_sub_560_i3 child_envelope_sub_560_i3 ?_
  intro b hb
  exact common_sub_560_i3 (mem_commonEnvelope childrenD_560_i3 b hb)

theorem finite_children_work_560_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_560_i2 j) (childrenD_560_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_560_i3.mono (by decide +kernel)

theorem finite_row_works_560_i2 : FiniteTemplate HasSnaky 6 required_560_i2 envelope_560_i2 := by
  refine finite_compose HasSnaky 5 childrenC_560_i2 childrenD_560_i2 finite_children_work_560_i2 (4, 1)
    required_560_i2 envelope_560_i2 pivot_mem_560_i2 child_required_sub_560_i2 child_envelope_sub_560_i2 ?_
  intro b hb
  exact common_sub_560_i2 (mem_commonEnvelope childrenD_560_i2 b hb)

theorem finite_children_work_560_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_560_i1 j) (childrenD_560_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_153 7 (6, 5)).mono (by decide +kernel)
  · exact finite_row_works_560_i2.mono (by decide +kernel)

theorem finite_row_works_560_i1 : FiniteTemplate HasSnaky 7 required_560_i1 envelope_560_i1 := by
  refine finite_compose HasSnaky 6 childrenC_560_i1 childrenD_560_i1 finite_children_work_560_i1 (6, 5)
    required_560_i1 envelope_560_i1 pivot_mem_560_i1 child_required_sub_560_i1 child_envelope_sub_560_i1 ?_
  intro b hb
  exact common_sub_560_i1 (mem_commonEnvelope childrenD_560_i1 b hb)

theorem finite_children_work_560_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_560_i0 j) (childrenD_560_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_560_i1.mono (by decide +kernel)

theorem finite_row_works_560_i0 : FiniteTemplate HasSnaky 8 required_560_i0 envelope_560_i0 := by
  refine finite_compose HasSnaky 7 childrenC_560_i0 childrenD_560_i0 finite_children_work_560_i0 (3, 1)
    required_560_i0 envelope_560_i0 pivot_mem_560_i0 child_required_sub_560_i0 child_envelope_sub_560_i0 ?_
  intro b hb
  exact common_sub_560_i0 (mem_commonEnvelope childrenD_560_i0 b hb)

theorem finite_children_work_560_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_560_i5 j) (childrenD_560_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_227 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_245 7 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_274 4 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_560_i5 : FiniteTemplate HasSnaky 6 required_560_i5 envelope_560_i5 := by
  refine finite_compose HasSnaky 5 childrenC_560_i5 childrenD_560_i5 finite_children_work_560_i5 (5, 3)
    required_560_i5 envelope_560_i5 pivot_mem_560_i5 child_required_sub_560_i5 child_envelope_sub_560_i5 ?_
  intro b hb
  exact common_sub_560_i5 (mem_commonEnvelope childrenD_560_i5 b hb)

theorem finite_children_work_560 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_560 j) (childrenD_560 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_67 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_228 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_373 4 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_531 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_560_i0.mono (by decide +kernel)
  · exact finite_row_works_560_i5.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_559 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_560 : FiniteTemplate HasSnaky 10 required_560 envelope_560 := by
  refine finite_compose HasSnaky 9 childrenC_560 childrenD_560 finite_children_work_560 (5, 4)
    required_560 envelope_560 pivot_mem_560 child_required_sub_560 child_envelope_sub_560 ?_
  intro b hb
  exact common_sub_560 (mem_commonEnvelope childrenD_560 b hb)

theorem finite_children_work_563_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_563_i2 j) (childrenD_563_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_393 4 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_563_i2 : FiniteTemplate HasSnaky 7 required_563_i2 envelope_563_i2 := by
  refine finite_compose HasSnaky 6 childrenC_563_i2 childrenD_563_i2 finite_children_work_563_i2 (2, 6)
    required_563_i2 envelope_563_i2 pivot_mem_563_i2 child_required_sub_563_i2 child_envelope_sub_563_i2 ?_
  intro b hb
  exact common_sub_563_i2 (mem_commonEnvelope childrenD_563_i2 b hb)

theorem finite_children_work_563_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_563_i1 j) (childrenD_563_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 5)).mono (by decide +kernel)
  · exact finite_row_works_563_i2.mono (by decide +kernel)

theorem finite_row_works_563_i1 : FiniteTemplate HasSnaky 8 required_563_i1 envelope_563_i1 := by
  refine finite_compose HasSnaky 7 childrenC_563_i1 childrenD_563_i1 finite_children_work_563_i1 (2, 4)
    required_563_i1 envelope_563_i1 pivot_mem_563_i1 child_required_sub_563_i1 child_envelope_sub_563_i1 ?_
  intro b hb
  exact common_sub_563_i1 (mem_commonEnvelope childrenD_563_i1 b hb)

theorem finite_children_work_563_i6 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_563_i6 j) (childrenD_563_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 6 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_38 7 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_563_i6 : FiniteTemplate HasSnaky 3 required_563_i6 envelope_563_i6 := by
  refine finite_compose HasSnaky 2 childrenC_563_i6 childrenD_563_i6 finite_children_work_563_i6 (3, 3)
    required_563_i6 envelope_563_i6 pivot_mem_563_i6 child_required_sub_563_i6 child_envelope_sub_563_i6 ?_
  intro b hb
  exact common_sub_563_i6 (mem_commonEnvelope childrenD_563_i6 b hb)

theorem finite_children_work_563_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_563_i5 j) (childrenD_563_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_563_i6.mono (by decide +kernel)

theorem finite_row_works_563_i5 : FiniteTemplate HasSnaky 4 required_563_i5 envelope_563_i5 := by
  refine finite_compose HasSnaky 3 childrenC_563_i5 childrenD_563_i5 finite_children_work_563_i5 (3, 6)
    required_563_i5 envelope_563_i5 pivot_mem_563_i5 child_required_sub_563_i5 child_envelope_sub_563_i5 ?_
  intro b hb
  exact common_sub_563_i5 (mem_commonEnvelope childrenD_563_i5 b hb)

theorem finite_children_work_563_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_563_i4 j) (childrenD_563_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 4 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_563_i5.mono (by decide +kernel)

theorem finite_row_works_563_i4 : FiniteTemplate HasSnaky 5 required_563_i4 envelope_563_i4 := by
  refine finite_compose HasSnaky 4 childrenC_563_i4 childrenD_563_i4 finite_children_work_563_i4 (3, 4)
    required_563_i4 envelope_563_i4 pivot_mem_563_i4 child_required_sub_563_i4 child_envelope_sub_563_i4 ?_
  intro b hb
  exact common_sub_563_i4 (mem_commonEnvelope childrenD_563_i4 b hb)

theorem finite_children_work_563_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_563_i3 j) (childrenD_563_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_563_i4.mono (by decide +kernel)

theorem finite_row_works_563_i3 : FiniteTemplate HasSnaky 6 required_563_i3 envelope_563_i3 := by
  refine finite_compose HasSnaky 5 childrenC_563_i3 childrenD_563_i3 finite_children_work_563_i3 (4, 4)
    required_563_i3 envelope_563_i3 pivot_mem_563_i3 child_required_sub_563_i3 child_envelope_sub_563_i3 ?_
  intro b hb
  exact common_sub_563_i3 (mem_commonEnvelope childrenD_563_i3 b hb)

theorem finite_children_work_563_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_563_i0 j) (childrenD_563_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 1 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_563_i1.mono (by decide +kernel)
  · exact finite_row_works_563_i3.mono (by decide +kernel)

theorem finite_row_works_563_i0 : FiniteTemplate HasSnaky 9 required_563_i0 envelope_563_i0 := by
  refine finite_compose HasSnaky 8 childrenC_563_i0 childrenD_563_i0 finite_children_work_563_i0 (4, 5)
    required_563_i0 envelope_563_i0 pivot_mem_563_i0 child_required_sub_563_i0 child_envelope_sub_563_i0 ?_
  intro b hb
  exact common_sub_563_i0 (mem_commonEnvelope childrenD_563_i0 b hb)

theorem finite_children_work_563 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_563 j) (childrenD_563 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_134 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_258 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_563_i0.mono (by decide +kernel)
  · exact finite_row_works_561.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_562 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_563 : FiniteTemplate HasSnaky 10 required_563 envelope_563 := by
  refine finite_compose HasSnaky 9 childrenC_563 childrenD_563 finite_children_work_563 (3, 5)
    required_563 envelope_563 pivot_mem_563 child_required_sub_563 child_envelope_sub_563 ?_
  intro b hb
  exact common_sub_563 (mem_commonEnvelope childrenD_563 b hb)

end FiniteCongruenceChecks.SnakyFinite
