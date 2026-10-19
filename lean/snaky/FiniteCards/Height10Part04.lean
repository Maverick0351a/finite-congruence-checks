/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part02
import FiniteCards.Height05Part06
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height07Part01
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_569_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_569_i2 j) (childrenD_569_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_54 0 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_569_i2 : FiniteTemplate HasSnaky 4 required_569_i2 envelope_569_i2 := by
  refine finite_compose HasSnaky 3 childrenC_569_i2 childrenD_569_i2 finite_children_work_569_i2 (6, 6)
    required_569_i2 envelope_569_i2 pivot_mem_569_i2 child_required_sub_569_i2 child_envelope_sub_569_i2 ?_
  intro b hb
  exact common_sub_569_i2 (mem_commonEnvelope childrenD_569_i2 b hb)

theorem finite_children_work_569_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_569_i1 j) (childrenD_569_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_68 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_569_i2.mono (by decide +kernel)

theorem finite_row_works_569_i1 : FiniteTemplate HasSnaky 5 required_569_i1 envelope_569_i1 := by
  refine finite_compose HasSnaky 4 childrenC_569_i1 childrenD_569_i1 finite_children_work_569_i1 (5, 3)
    required_569_i1 envelope_569_i1 pivot_mem_569_i1 child_required_sub_569_i1 child_envelope_sub_569_i1 ?_
  intro b hb
  exact common_sub_569_i1 (mem_commonEnvelope childrenD_569_i1 b hb)

theorem finite_children_work_569_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_569_i3 j) (childrenD_569_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_169 7 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_202 4 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_569_i3 : FiniteTemplate HasSnaky 6 required_569_i3 envelope_569_i3 := by
  refine finite_compose HasSnaky 5 childrenC_569_i3 childrenD_569_i3 finite_children_work_569_i3 (6, 3)
    required_569_i3 envelope_569_i3 pivot_mem_569_i3 child_required_sub_569_i3 child_envelope_sub_569_i3 ?_
  intro b hb
  exact common_sub_569_i3 (mem_commonEnvelope childrenD_569_i3 b hb)

theorem finite_children_work_569_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_569_i0 j) (childrenD_569_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_569_i1.mono (by decide +kernel)
  · exact finite_row_works_569_i3.mono (by decide +kernel)

theorem finite_row_works_569_i0 : FiniteTemplate HasSnaky 7 required_569_i0 envelope_569_i0 := by
  refine finite_compose HasSnaky 6 childrenC_569_i0 childrenD_569_i0 finite_children_work_569_i0 (6, 5)
    required_569_i0 envelope_569_i0 pivot_mem_569_i0 child_required_sub_569_i0 child_envelope_sub_569_i0 ?_
  intro b hb
  exact common_sub_569_i0 (mem_commonEnvelope childrenD_569_i0 b hb)

theorem finite_children_work_569_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_569_i4 j) (childrenD_569_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_68 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_495 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_569_i4 : FiniteTemplate HasSnaky 6 required_569_i4 envelope_569_i4 := by
  refine finite_compose HasSnaky 5 childrenC_569_i4 childrenD_569_i4 finite_children_work_569_i4 (5, 3)
    required_569_i4 envelope_569_i4 pivot_mem_569_i4 child_required_sub_569_i4 child_envelope_sub_569_i4 ?_
  intro b hb
  exact common_sub_569_i4 (mem_commonEnvelope childrenD_569_i4 b hb)

theorem finite_children_work_569_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_569_i6 j) (childrenD_569_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_99 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_169 7 (6, 3)).mono (by decide +kernel)

theorem finite_row_works_569_i6 : FiniteTemplate HasSnaky 5 required_569_i6 envelope_569_i6 := by
  refine finite_compose HasSnaky 4 childrenC_569_i6 childrenD_569_i6 finite_children_work_569_i6 (6, 3)
    required_569_i6 envelope_569_i6 pivot_mem_569_i6 child_required_sub_569_i6 child_envelope_sub_569_i6 ?_
  intro b hb
  exact common_sub_569_i6 (mem_commonEnvelope childrenD_569_i6 b hb)

theorem finite_children_work_569_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_569_i7 j) (childrenD_569_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_288 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_569_i7 : FiniteTemplate HasSnaky 5 required_569_i7 envelope_569_i7 := by
  refine finite_compose HasSnaky 4 childrenC_569_i7 childrenD_569_i7 finite_children_work_569_i7 (4, 6)
    required_569_i7 envelope_569_i7 pivot_mem_569_i7 child_required_sub_569_i7 child_envelope_sub_569_i7 ?_
  intro b hb
  exact common_sub_569_i7 (mem_commonEnvelope childrenD_569_i7 b hb)

theorem finite_children_work_569_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_569_i5 j) (childrenD_569_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 3 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_569_i6.mono (by decide +kernel)
  · exact finite_row_works_569_i7.mono (by decide +kernel)

theorem finite_row_works_569_i5 : FiniteTemplate HasSnaky 6 required_569_i5 envelope_569_i5 := by
  refine finite_compose HasSnaky 5 childrenC_569_i5 childrenD_569_i5 finite_children_work_569_i5 (6, 5)
    required_569_i5 envelope_569_i5 pivot_mem_569_i5 child_required_sub_569_i5 child_envelope_sub_569_i5 ?_
  intro b hb
  exact common_sub_569_i5 (mem_commonEnvelope childrenD_569_i5 b hb)

theorem finite_children_work_569 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_569 j) (childrenD_569 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_287 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 4 (2, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 1 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_569_i0.mono (by decide +kernel)
  · exact finite_row_works_569_i4.mono (by decide +kernel)
  · exact finite_row_works_569_i5.mono (by decide +kernel)

theorem finite_row_works_569 : FiniteTemplate HasSnaky 10 required_569 envelope_569 := by
  refine finite_compose HasSnaky 9 childrenC_569 childrenD_569 finite_children_work_569 (5, 5)
    required_569 envelope_569 pivot_mem_569 child_required_sub_569 child_envelope_sub_569 ?_
  intro b hb
  exact common_sub_569 (mem_commonEnvelope childrenD_569 b hb)

theorem finite_children_work_575_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_575_i0 j) (childrenD_575_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (2, 3)).mono (by decide +kernel)

theorem finite_row_works_575_i0 : FiniteTemplate HasSnaky 4 required_575_i0 envelope_575_i0 := by
  refine finite_compose HasSnaky 3 childrenC_575_i0 childrenD_575_i0 finite_children_work_575_i0 (2, 4)
    required_575_i0 envelope_575_i0 pivot_mem_575_i0 child_required_sub_575_i0 child_envelope_sub_575_i0 ?_
  intro b hb
  exact common_sub_575_i0 (mem_commonEnvelope childrenD_575_i0 b hb)

theorem finite_children_work_575_i2 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_575_i2 j) (childrenD_575_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 3 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_575_i2 : FiniteTemplate HasSnaky 3 required_575_i2 envelope_575_i2 := by
  refine finite_compose HasSnaky 2 childrenC_575_i2 childrenD_575_i2 finite_children_work_575_i2 (2, 4)
    required_575_i2 envelope_575_i2 pivot_mem_575_i2 child_required_sub_575_i2 child_envelope_sub_575_i2 ?_
  intro b hb
  exact common_sub_575_i2 (mem_commonEnvelope childrenD_575_i2 b hb)

theorem finite_children_work_575_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_575_i1 j) (childrenD_575_i1 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_575_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_554 5 (7, 4)).mono (by decide +kernel)

theorem finite_row_works_575_i1 : FiniteTemplate HasSnaky 8 required_575_i1 envelope_575_i1 := by
  refine finite_compose HasSnaky 7 childrenC_575_i1 childrenD_575_i1 finite_children_work_575_i1 (6, 4)
    required_575_i1 envelope_575_i1 pivot_mem_575_i1 child_required_sub_575_i1 child_envelope_sub_575_i1 ?_
  intro b hb
  exact common_sub_575_i1 (mem_commonEnvelope childrenD_575_i1 b hb)

theorem finite_children_work_575_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_575_i3 j) (childrenD_575_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_280 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_554 5 (7, 4)).mono (by decide +kernel)

theorem finite_row_works_575_i3 : FiniteTemplate HasSnaky 8 required_575_i3 envelope_575_i3 := by
  refine finite_compose HasSnaky 7 childrenC_575_i3 childrenD_575_i3 finite_children_work_575_i3 (6, 4)
    required_575_i3 envelope_575_i3 pivot_mem_575_i3 child_required_sub_575_i3 child_envelope_sub_575_i3 ?_
  intro b hb
  exact common_sub_575_i3 (mem_commonEnvelope childrenD_575_i3 b hb)

theorem finite_children_work_575 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_575 j) (childrenD_575 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_257 0 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_326.mono (by decide +kernel)
  · exact finite_row_works_575_i0.mono (by decide +kernel)
  · exact finite_row_works_575_i1.mono (by decide +kernel)
  · exact finite_row_works_575_i3.mono (by decide +kernel)

theorem finite_row_works_575 : FiniteTemplate HasSnaky 10 required_575 envelope_575 := by
  refine finite_compose HasSnaky 9 childrenC_575 childrenD_575 finite_children_work_575 (5, 4)
    required_575 envelope_575 pivot_mem_575 child_required_sub_575 child_envelope_sub_575 ?_
  intro b hb
  exact common_sub_575 (mem_commonEnvelope childrenD_575 b hb)

theorem finite_children_work_578 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_578 j) (childrenD_578 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_26 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 4 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_117 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_577 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_578 : FiniteTemplate HasSnaky 10 required_578 envelope_578 := by
  refine finite_compose HasSnaky 9 childrenC_578 childrenD_578 finite_children_work_578 (4, 3)
    required_578 envelope_578 pivot_mem_578 child_required_sub_578 child_envelope_sub_578 ?_
  intro b hb
  exact common_sub_578 (mem_commonEnvelope childrenD_578 b hb)

theorem finite_children_work_580 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_580 j) (childrenD_580 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_24 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 4 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_194 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_577.mono (by decide +kernel)

theorem finite_row_works_580 : FiniteTemplate HasSnaky 10 required_580 envelope_580 := by
  refine finite_compose HasSnaky 9 childrenC_580 childrenD_580 finite_children_work_580 (4, 2)
    required_580 envelope_580 pivot_mem_580 child_required_sub_580 child_envelope_sub_580 ?_
  intro b hb
  exact common_sub_580 (mem_commonEnvelope childrenD_580 b hb)

theorem finite_children_work_585_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_585_i2 j) (childrenD_585_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_358 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_585_i2 : FiniteTemplate HasSnaky 7 required_585_i2 envelope_585_i2 := by
  refine finite_compose HasSnaky 6 childrenC_585_i2 childrenD_585_i2 finite_children_work_585_i2 (1, 4)
    required_585_i2 envelope_585_i2 pivot_mem_585_i2 child_required_sub_585_i2 child_envelope_sub_585_i2 ?_
  intro b hb
  exact common_sub_585_i2 (mem_commonEnvelope childrenD_585_i2 b hb)

theorem finite_children_work_585_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_585_i1 j) (childrenD_585_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_585_i2.mono (by decide +kernel)

theorem finite_row_works_585_i1 : FiniteTemplate HasSnaky 8 required_585_i1 envelope_585_i1 := by
  refine finite_compose HasSnaky 7 childrenC_585_i1 childrenD_585_i1 finite_children_work_585_i1 (4, 1)
    required_585_i1 envelope_585_i1 pivot_mem_585_i1 child_required_sub_585_i1 child_envelope_sub_585_i1 ?_
  intro b hb
  exact common_sub_585_i1 (mem_commonEnvelope childrenD_585_i1 b hb)

theorem finite_children_work_585_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_585_i0 j) (childrenD_585_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_585_i1.mono (by decide +kernel)

theorem finite_row_works_585_i0 : FiniteTemplate HasSnaky 9 required_585_i0 envelope_585_i0 := by
  refine finite_compose HasSnaky 8 childrenC_585_i0 childrenD_585_i0 finite_children_work_585_i0 (1, 1)
    required_585_i0 envelope_585_i0 pivot_mem_585_i0 child_required_sub_585_i0 child_envelope_sub_585_i0 ?_
  intro b hb
  exact common_sub_585_i0 (mem_commonEnvelope childrenD_585_i0 b hb)

theorem finite_children_work_585 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_585 j) (childrenD_585 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_585_i0.mono (by decide +kernel)

theorem finite_row_works_585 : FiniteTemplate HasSnaky 10 required_585 envelope_585 := by
  refine finite_compose HasSnaky 9 childrenC_585 childrenD_585 finite_children_work_585 (1, 3)
    required_585 envelope_585 pivot_mem_585 child_required_sub_585 child_envelope_sub_585 ?_
  intro b hb
  exact common_sub_585 (mem_commonEnvelope childrenD_585 b hb)

end FiniteCongruenceChecks.SnakyFinite
