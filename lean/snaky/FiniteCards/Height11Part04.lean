/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03
import FiniteCards.Height09Part04
import FiniteCards.Height09Part06
import FiniteCards.Height10Part02
import FiniteCards.Height10Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_615_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_615_i5 j) (childrenD_615_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 4 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_20 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_402 0 (3, 2)).mono (by decide +kernel)

theorem finite_row_works_615_i5 : FiniteTemplate HasSnaky 4 required_615_i5 envelope_615_i5 := by
  refine finite_compose HasSnaky 3 childrenC_615_i5 childrenD_615_i5 finite_children_work_615_i5 (4, 3)
    required_615_i5 envelope_615_i5 pivot_mem_615_i5 child_required_sub_615_i5 child_envelope_sub_615_i5 ?_
  intro b hb
  exact common_sub_615_i5 (mem_commonEnvelope childrenD_615_i5 b hb)

theorem finite_children_work_615_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_615_i4 j) (childrenD_615_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (7, 5)).mono (by decide +kernel)
  · exact finite_row_works_615_i5.mono (by decide +kernel)

theorem finite_row_works_615_i4 : FiniteTemplate HasSnaky 5 required_615_i4 envelope_615_i4 := by
  refine finite_compose HasSnaky 4 childrenC_615_i4 childrenD_615_i4 finite_children_work_615_i4 (4, 4)
    required_615_i4 envelope_615_i4 pivot_mem_615_i4 child_required_sub_615_i4 child_envelope_sub_615_i4 ?_
  intro b hb
  exact common_sub_615_i4 (mem_commonEnvelope childrenD_615_i4 b hb)

theorem finite_children_work_615_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_615_i3 j) (childrenD_615_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_615_i4.mono (by decide +kernel)

theorem finite_row_works_615_i3 : FiniteTemplate HasSnaky 6 required_615_i3 envelope_615_i3 := by
  refine finite_compose HasSnaky 5 childrenC_615_i3 childrenD_615_i3 finite_children_work_615_i3 (6, 5)
    required_615_i3 envelope_615_i3 pivot_mem_615_i3 child_required_sub_615_i3 child_envelope_sub_615_i3 ?_
  intro b hb
  exact common_sub_615_i3 (mem_commonEnvelope childrenD_615_i3 b hb)

theorem finite_children_work_615_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_615_i2 j) (childrenD_615_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_139 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_148 5 (6, 4)).mono (by decide +kernel)
  · exact finite_row_works_615_i3.mono (by decide +kernel)

theorem finite_row_works_615_i2 : FiniteTemplate HasSnaky 7 required_615_i2 envelope_615_i2 := by
  refine finite_compose HasSnaky 6 childrenC_615_i2 childrenD_615_i2 finite_children_work_615_i2 (6, 4)
    required_615_i2 envelope_615_i2 pivot_mem_615_i2 child_required_sub_615_i2 child_envelope_sub_615_i2 ?_
  intro b hb
  exact common_sub_615_i2 (mem_commonEnvelope childrenD_615_i2 b hb)

theorem finite_children_work_615_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_615_i1 j) (childrenD_615_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_43 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_57 4 (2, 8)).mono (by decide +kernel)
  · exact finite_row_works_615_i2.mono (by decide +kernel)

theorem finite_row_works_615_i1 : FiniteTemplate HasSnaky 8 required_615_i1 envelope_615_i1 := by
  refine finite_compose HasSnaky 7 childrenC_615_i1 childrenD_615_i1 finite_children_work_615_i1 (4, 6)
    required_615_i1 envelope_615_i1 pivot_mem_615_i1 child_required_sub_615_i1 child_envelope_sub_615_i1 ?_
  intro b hb
  exact common_sub_615_i1 (mem_commonEnvelope childrenD_615_i1 b hb)

theorem finite_children_work_615_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_615_i0 j) (childrenD_615_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_561 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_615_i1.mono (by decide +kernel)

theorem finite_row_works_615_i0 : FiniteTemplate HasSnaky 10 required_615_i0 envelope_615_i0 := by
  refine finite_compose HasSnaky 9 childrenC_615_i0 childrenD_615_i0 finite_children_work_615_i0 (5, 5)
    required_615_i0 envelope_615_i0 pivot_mem_615_i0 child_required_sub_615_i0 child_envelope_sub_615_i0 ?_
  intro b hb
  exact common_sub_615_i0 (mem_commonEnvelope childrenD_615_i0 b hb)

theorem finite_children_work_615 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_615 j) (childrenD_615 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_362 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_614.mono (by decide +kernel)
  · exact finite_row_works_615_i0.mono (by decide +kernel)

theorem finite_row_works_615 : FiniteTemplate HasSnaky 11 required_615 envelope_615 := by
  refine finite_compose HasSnaky 10 childrenC_615 childrenD_615 finite_children_work_615 (4, 5)
    required_615 envelope_615 pivot_mem_615 child_required_sub_615 child_envelope_sub_615 ?_
  intro b hb
  exact common_sub_615 (mem_commonEnvelope childrenD_615 b hb)

theorem finite_children_work_617 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_617 j) (childrenD_617 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_136 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_332 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_616 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_617 : FiniteTemplate HasSnaky 11 required_617 envelope_617 := by
  refine finite_compose HasSnaky 10 childrenC_617 childrenD_617 finite_children_work_617 (4, 3)
    required_617 envelope_617 pivot_mem_617 child_required_sub_617 child_envelope_sub_617 ?_
  intro b hb
  exact common_sub_617 (mem_commonEnvelope childrenD_617 b hb)

theorem finite_children_work_624_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_624_i1 j) (childrenD_624_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_64 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_315 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_624_i1 : FiniteTemplate HasSnaky 7 required_624_i1 envelope_624_i1 := by
  refine finite_compose HasSnaky 6 childrenC_624_i1 childrenD_624_i1 finite_children_work_624_i1 (4, 3)
    required_624_i1 envelope_624_i1 pivot_mem_624_i1 child_required_sub_624_i1 child_envelope_sub_624_i1 ?_
  intro b hb
  exact common_sub_624_i1 (mem_commonEnvelope childrenD_624_i1 b hb)

theorem finite_children_work_624_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_624_i0 j) (childrenD_624_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_82 4 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_624_i1.mono (by decide +kernel)

theorem finite_row_works_624_i0 : FiniteTemplate HasSnaky 8 required_624_i0 envelope_624_i0 := by
  refine finite_compose HasSnaky 7 childrenC_624_i0 childrenD_624_i0 finite_children_work_624_i0 (3, 3)
    required_624_i0 envelope_624_i0 pivot_mem_624_i0 child_required_sub_624_i0 child_envelope_sub_624_i0 ?_
  intro b hb
  exact common_sub_624_i0 (mem_commonEnvelope childrenD_624_i0 b hb)

theorem finite_children_work_624 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_624 j) (childrenD_624 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_624_i0.mono (by decide +kernel)

theorem finite_row_works_624 : FiniteTemplate HasSnaky 11 required_624 envelope_624 := by
  refine finite_compose HasSnaky 10 childrenC_624 childrenD_624 finite_children_work_624 (3, 4)
    required_624 envelope_624 pivot_mem_624 child_required_sub_624 child_envelope_sub_624 ?_
  intro b hb
  exact common_sub_624 (mem_commonEnvelope childrenD_624 b hb)

theorem finite_children_work_625_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_625_i2 j) (childrenD_625_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_56 7 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_73 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_625_i2 : FiniteTemplate HasSnaky 5 required_625_i2 envelope_625_i2 := by
  refine finite_compose HasSnaky 4 childrenC_625_i2 childrenD_625_i2 finite_children_work_625_i2 (3, 1)
    required_625_i2 envelope_625_i2 pivot_mem_625_i2 child_required_sub_625_i2 child_envelope_sub_625_i2 ?_
  intro b hb
  exact common_sub_625_i2 (mem_commonEnvelope childrenD_625_i2 b hb)

theorem finite_children_work_625_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_625_i1 j) (childrenD_625_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_82 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_625_i2.mono (by decide +kernel)

theorem finite_row_works_625_i1 : FiniteTemplate HasSnaky 6 required_625_i1 envelope_625_i1 := by
  refine finite_compose HasSnaky 5 childrenC_625_i1 childrenD_625_i1 finite_children_work_625_i1 (3, 4)
    required_625_i1 envelope_625_i1 pivot_mem_625_i1 child_required_sub_625_i1 child_envelope_sub_625_i1 ?_
  intro b hb
  exact common_sub_625_i1 (mem_commonEnvelope childrenD_625_i1 b hb)

theorem finite_children_work_625_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_625_i0 j) (childrenD_625_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_294 5 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_449 1 (0, 0)).mono (by decide +kernel)
  · exact finite_row_works_625_i1.mono (by decide +kernel)

theorem finite_row_works_625_i0 : FiniteTemplate HasSnaky 10 required_625_i0 envelope_625_i0 := by
  refine finite_compose HasSnaky 9 childrenC_625_i0 childrenD_625_i0 finite_children_work_625_i0 (3, 3)
    required_625_i0 envelope_625_i0 pivot_mem_625_i0 child_required_sub_625_i0 child_envelope_sub_625_i0 ?_
  intro b hb
  exact common_sub_625_i0 (mem_commonEnvelope childrenD_625_i0 b hb)

theorem finite_children_work_625 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_625 j) (childrenD_625 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_454 5 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_455 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_625_i0.mono (by decide +kernel)

theorem finite_row_works_625 : FiniteTemplate HasSnaky 11 required_625 envelope_625 := by
  refine finite_compose HasSnaky 10 childrenC_625 childrenD_625 finite_children_work_625 (3, 2)
    required_625 envelope_625 pivot_mem_625 child_required_sub_625 child_envelope_sub_625 ?_
  intro b hb
  exact common_sub_625 (mem_commonEnvelope childrenD_625 b hb)

theorem finite_children_work_626_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_626_i1 j) (childrenD_626_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_38 6 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_626_i1 : FiniteTemplate HasSnaky 3 required_626_i1 envelope_626_i1 := by
  refine finite_compose HasSnaky 2 childrenC_626_i1 childrenD_626_i1 finite_children_work_626_i1 (2, 5)
    required_626_i1 envelope_626_i1 pivot_mem_626_i1 child_required_sub_626_i1 child_envelope_sub_626_i1 ?_
  intro b hb
  exact common_sub_626_i1 (mem_commonEnvelope childrenD_626_i1 b hb)

theorem finite_children_work_626_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_626_i0 j) (childrenD_626_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_317 4 (2, 9)).mono (by decide +kernel)
  · exact finite_row_works_626_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_519 0 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_626_i0 : FiniteTemplate HasSnaky 10 required_626_i0 envelope_626_i0 := by
  refine finite_compose HasSnaky 9 childrenC_626_i0 childrenD_626_i0 finite_children_work_626_i0 (4, 5)
    required_626_i0 envelope_626_i0 pivot_mem_626_i0 child_required_sub_626_i0 child_envelope_sub_626_i0 ?_
  intro b hb
  exact common_sub_626_i0 (mem_commonEnvelope childrenD_626_i0 b hb)

theorem finite_children_work_626_i3 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_626_i3 j) (childrenD_626_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_412 1 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_626_i3 : FiniteTemplate HasSnaky 9 required_626_i3 envelope_626_i3 := by
  refine finite_compose HasSnaky 8 childrenC_626_i3 childrenD_626_i3 finite_children_work_626_i3 (2, 5)
    required_626_i3 envelope_626_i3 pivot_mem_626_i3 child_required_sub_626_i3 child_envelope_sub_626_i3 ?_
  intro b hb
  exact common_sub_626_i3 (mem_commonEnvelope childrenD_626_i3 b hb)

theorem finite_children_work_626_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_626_i2 j) (childrenD_626_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_336 1 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_626_i3.mono (by decide +kernel)

theorem finite_row_works_626_i2 : FiniteTemplate HasSnaky 10 required_626_i2 envelope_626_i2 := by
  refine finite_compose HasSnaky 9 childrenC_626_i2 childrenD_626_i2 finite_children_work_626_i2 (4, 6)
    required_626_i2 envelope_626_i2 pivot_mem_626_i2 child_required_sub_626_i2 child_envelope_sub_626_i2 ?_
  intro b hb
  exact common_sub_626_i2 (mem_commonEnvelope childrenD_626_i2 b hb)

theorem finite_children_work_626 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_626 j) (childrenD_626 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_323 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_430 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_592 7 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_626_i0.mono (by decide +kernel)
  · exact finite_row_works_626_i2.mono (by decide +kernel)

theorem finite_row_works_626 : FiniteTemplate HasSnaky 11 required_626 envelope_626 := by
  refine finite_compose HasSnaky 10 childrenC_626 childrenD_626 finite_children_work_626 (5, 6)
    required_626 envelope_626 pivot_mem_626 child_required_sub_626 child_envelope_sub_626 ?_
  intro b hb
  exact common_sub_626 (mem_commonEnvelope childrenD_626 b hb)

end FiniteCongruenceChecks.SnakyFinite
