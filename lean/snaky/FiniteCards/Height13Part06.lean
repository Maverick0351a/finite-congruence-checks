/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part06
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height09Part07
import FiniteCards.Height09Part08
import FiniteCards.Height10Part02
import FiniteCards.Height11Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_695_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_695_i6 j) (childrenD_695_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_75 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_103 4 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_695_i6 : FiniteTemplate HasSnaky 5 required_695_i6 envelope_695_i6 := by
  refine finite_compose HasSnaky 4 childrenC_695_i6 childrenD_695_i6 finite_children_work_695_i6 (1, 6)
    required_695_i6 envelope_695_i6 pivot_mem_695_i6 child_required_sub_695_i6 child_envelope_sub_695_i6 ?_
  intro b hb
  exact common_sub_695_i6 (mem_commonEnvelope childrenD_695_i6 b hb)

theorem finite_children_work_695_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_695_i7 j) (childrenD_695_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 2 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_90 7 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_695_i7 : FiniteTemplate HasSnaky 5 required_695_i7 envelope_695_i7 := by
  refine finite_compose HasSnaky 4 childrenC_695_i7 childrenD_695_i7 finite_children_work_695_i7 (1, 6)
    required_695_i7 envelope_695_i7 pivot_mem_695_i7 child_required_sub_695_i7 child_envelope_sub_695_i7 ?_
  intro b hb
  exact common_sub_695_i7 (mem_commonEnvelope childrenD_695_i7 b hb)

theorem finite_children_work_695_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_695_i5 j) (childrenD_695_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_308 6 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_348 5 (5, 5)).mono (by decide +kernel)
  · exact finite_row_works_695_i6.mono (by decide +kernel)
  · exact finite_row_works_695_i7.mono (by decide +kernel)

theorem finite_row_works_695_i5 : FiniteTemplate HasSnaky 7 required_695_i5 envelope_695_i5 := by
  refine finite_compose HasSnaky 6 childrenC_695_i5 childrenD_695_i5 finite_children_work_695_i5 (1, 7)
    required_695_i5 envelope_695_i5 pivot_mem_695_i5 child_required_sub_695_i5 child_envelope_sub_695_i5 ?_
  intro b hb
  exact common_sub_695_i5 (mem_commonEnvelope childrenD_695_i5 b hb)

theorem finite_children_work_695_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_695_i4 j) (childrenD_695_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact finite_row_works_695_i5.mono (by decide +kernel)

theorem finite_row_works_695_i4 : FiniteTemplate HasSnaky 8 required_695_i4 envelope_695_i4 := by
  refine finite_compose HasSnaky 7 childrenC_695_i4 childrenD_695_i4 finite_children_work_695_i4 (1, 4)
    required_695_i4 envelope_695_i4 pivot_mem_695_i4 child_required_sub_695_i4 child_envelope_sub_695_i4 ?_
  intro b hb
  exact common_sub_695_i4 (mem_commonEnvelope childrenD_695_i4 b hb)

theorem finite_children_work_695_i3 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_695_i3 j) (childrenD_695_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_96 0 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_695_i4.mono (by decide +kernel)

theorem finite_row_works_695_i3 : FiniteTemplate HasSnaky 9 required_695_i3 envelope_695_i3 := by
  refine finite_compose HasSnaky 8 childrenC_695_i3 childrenD_695_i3 finite_children_work_695_i3 (3, 8)
    required_695_i3 envelope_695_i3 pivot_mem_695_i3 child_required_sub_695_i3 child_envelope_sub_695_i3 ?_
  intro b hb
  exact common_sub_695_i3 (mem_commonEnvelope childrenD_695_i3 b hb)

theorem finite_children_work_695_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_695_i2 j) (childrenD_695_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_695_i3.mono (by decide +kernel)

theorem finite_row_works_695_i2 : FiniteTemplate HasSnaky 10 required_695_i2 envelope_695_i2 := by
  refine finite_compose HasSnaky 9 childrenC_695_i2 childrenD_695_i2 finite_children_work_695_i2 (1, 5)
    required_695_i2 envelope_695_i2 pivot_mem_695_i2 child_required_sub_695_i2 child_envelope_sub_695_i2 ?_
  intro b hb
  exact common_sub_695_i2 (mem_commonEnvelope childrenD_695_i2 b hb)

theorem finite_children_work_695_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_695_i1 j) (childrenD_695_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_67 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_175 6 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_228 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_688 1 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_695_i2.mono (by decide +kernel)

theorem finite_row_works_695_i1 : FiniteTemplate HasSnaky 11 required_695_i1 envelope_695_i1 := by
  refine finite_compose HasSnaky 10 childrenC_695_i1 childrenD_695_i1 finite_children_work_695_i1 (4, 7)
    required_695_i1 envelope_695_i1 pivot_mem_695_i1 child_required_sub_695_i1 child_envelope_sub_695_i1 ?_
  intro b hb
  exact common_sub_695_i1 (mem_commonEnvelope childrenD_695_i1 b hb)

theorem finite_children_work_695_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_695_i0 j) (childrenD_695_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_324 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_686 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_695_i1.mono (by decide +kernel)

theorem finite_row_works_695_i0 : FiniteTemplate HasSnaky 12 required_695_i0 envelope_695_i0 := by
  refine finite_compose HasSnaky 11 childrenC_695_i0 childrenD_695_i0 finite_children_work_695_i0 (4, 6)
    required_695_i0 envelope_695_i0 pivot_mem_695_i0 child_required_sub_695_i0 child_envelope_sub_695_i0 ?_
  intro b hb
  exact common_sub_695_i0 (mem_commonEnvelope childrenD_695_i0 b hb)

theorem finite_children_work_695 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_695 j) (childrenD_695 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_118 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_182 3 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_695_i0.mono (by decide +kernel)

theorem finite_row_works_695 : FiniteTemplate HasSnaky 13 required_695 envelope_695 := by
  refine finite_compose HasSnaky 12 childrenC_695 childrenD_695 finite_children_work_695 (4, 5)
    required_695 envelope_695 pivot_mem_695 child_required_sub_695 child_envelope_sub_695 ?_
  intro b hb
  exact common_sub_695 (mem_commonEnvelope childrenD_695 b hb)

theorem finite_children_work_696_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_696_i1 j) (childrenD_696_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 5 (6, 4)).mono (by decide +kernel)

theorem finite_row_works_696_i1 : FiniteTemplate HasSnaky 6 required_696_i1 envelope_696_i1 := by
  refine finite_compose HasSnaky 5 childrenC_696_i1 childrenD_696_i1 finite_children_work_696_i1 (5, 7)
    required_696_i1 envelope_696_i1 pivot_mem_696_i1 child_required_sub_696_i1 child_envelope_sub_696_i1 ?_
  intro b hb
  exact common_sub_696_i1 (mem_commonEnvelope childrenD_696_i1 b hb)

theorem finite_children_work_696_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_696_i0 j) (childrenD_696_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_317 3 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_696_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_436 7 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_685 6 (8, 9)).mono (by decide +kernel)

theorem finite_row_works_696_i0 : FiniteTemplate HasSnaky 12 required_696_i0 envelope_696_i0 := by
  refine finite_compose HasSnaky 11 childrenC_696_i0 childrenD_696_i0 finite_children_work_696_i0 (4, 4)
    required_696_i0 envelope_696_i0 pivot_mem_696_i0 child_required_sub_696_i0 child_envelope_sub_696_i0 ?_
  intro b hb
  exact common_sub_696_i0 (mem_commonEnvelope childrenD_696_i0 b hb)

theorem finite_children_work_696 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_696 j) (childrenD_696 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 7 (9, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 2 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 7 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_622 0 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_696_i0.mono (by decide +kernel)

theorem finite_row_works_696 : FiniteTemplate HasSnaky 13 required_696 envelope_696 := by
  refine finite_compose HasSnaky 12 childrenC_696 childrenD_696 finite_children_work_696 (5, 4)
    required_696 envelope_696 pivot_mem_696 child_required_sub_696 child_envelope_sub_696 ?_
  intro b hb
  exact common_sub_696 (mem_commonEnvelope childrenD_696 b hb)

theorem finite_children_work_709_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_709_i2 j) (childrenD_709_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_392 0 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_709_i2 : FiniteTemplate HasSnaky 7 required_709_i2 envelope_709_i2 := by
  refine finite_compose HasSnaky 6 childrenC_709_i2 childrenD_709_i2 finite_children_work_709_i2 (4, 5)
    required_709_i2 envelope_709_i2 pivot_mem_709_i2 child_required_sub_709_i2 child_envelope_sub_709_i2 ?_
  intro b hb
  exact common_sub_709_i2 (mem_commonEnvelope childrenD_709_i2 b hb)

theorem finite_children_work_709_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_709_i1 j) (childrenD_709_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 4 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_253 7 (8, 7)).mono (by decide +kernel)
  · exact finite_row_works_709_i2.mono (by decide +kernel)

theorem finite_row_works_709_i1 : FiniteTemplate HasSnaky 8 required_709_i1 envelope_709_i1 := by
  refine finite_compose HasSnaky 7 childrenC_709_i1 childrenD_709_i1 finite_children_work_709_i1 (5, 4)
    required_709_i1 envelope_709_i1 pivot_mem_709_i1 child_required_sub_709_i1 child_envelope_sub_709_i1 ?_
  intro b hb
  exact common_sub_709_i1 (mem_commonEnvelope childrenD_709_i1 b hb)

theorem finite_children_work_709_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_709_i4 j) (childrenD_709_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 4 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_89 6 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_709_i4 : FiniteTemplate HasSnaky 5 required_709_i4 envelope_709_i4 := by
  refine finite_compose HasSnaky 4 childrenC_709_i4 childrenD_709_i4 finite_children_work_709_i4 (5, 3)
    required_709_i4 envelope_709_i4 pivot_mem_709_i4 child_required_sub_709_i4 child_envelope_sub_709_i4 ?_
  intro b hb
  exact common_sub_709_i4 (mem_commonEnvelope childrenD_709_i4 b hb)

theorem finite_children_work_709_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_709_i3 j) (childrenD_709_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 4 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_521 4 (4, 8)).mono (by decide +kernel)
  · exact finite_row_works_709_i4.mono (by decide +kernel)

theorem finite_row_works_709_i3 : FiniteTemplate HasSnaky 7 required_709_i3 envelope_709_i3 := by
  refine finite_compose HasSnaky 6 childrenC_709_i3 childrenD_709_i3 finite_children_work_709_i3 (5, 4)
    required_709_i3 envelope_709_i3 pivot_mem_709_i3 child_required_sub_709_i3 child_envelope_sub_709_i3 ?_
  intro b hb
  exact common_sub_709_i3 (mem_commonEnvelope childrenD_709_i3 b hb)

theorem finite_children_work_709_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_709_i0 j) (childrenD_709_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_524 5 (9, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_536 7 (9, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 7 (10, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_655 5 (10, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_664 4 (1, 11)).mono (by decide +kernel)
  · exact finite_row_works_709_i1.mono (by decide +kernel)
  · exact finite_row_works_709_i3.mono (by decide +kernel)

theorem finite_row_works_709_i0 : FiniteTemplate HasSnaky 12 required_709_i0 envelope_709_i0 := by
  refine finite_compose HasSnaky 11 childrenC_709_i0 childrenD_709_i0 finite_children_work_709_i0 (6, 6)
    required_709_i0 envelope_709_i0 pivot_mem_709_i0 child_required_sub_709_i0 child_envelope_sub_709_i0 ?_
  intro b hb
  exact common_sub_709_i0 (mem_commonEnvelope childrenD_709_i0 b hb)

theorem finite_children_work_709 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_709 j) (childrenD_709 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_116 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 5 (7, 4)).mono (by decide +kernel)
  · exact finite_row_works_709_i0.mono (by decide +kernel)

theorem finite_row_works_709 : FiniteTemplate HasSnaky 13 required_709 envelope_709 := by
  refine finite_compose HasSnaky 12 childrenC_709 childrenD_709 finite_children_work_709 (5, 7)
    required_709 envelope_709 pivot_mem_709 child_required_sub_709 child_envelope_sub_709 ?_
  intro b hb
  exact common_sub_709 (mem_commonEnvelope childrenD_709 b hb)

end FiniteCongruenceChecks.SnakyFinite
