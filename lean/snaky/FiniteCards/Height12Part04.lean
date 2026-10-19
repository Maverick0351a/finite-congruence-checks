/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height08Part04
import FiniteCards.Height09Part02
import FiniteCards.Height09Part08
import FiniteCards.Height10Part01
import FiniteCards.Height10Part05
import FiniteCards.Height11Part02
import FiniteCards.Height11Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_632_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_632_i2 j) (childrenD_632_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_92 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_378 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_632_i2 : FiniteTemplate HasSnaky 7 required_632_i2 envelope_632_i2 := by
  refine finite_compose HasSnaky 6 childrenC_632_i2 childrenD_632_i2 finite_children_work_632_i2 (3, 2)
    required_632_i2 envelope_632_i2 pivot_mem_632_i2 child_required_sub_632_i2 child_envelope_sub_632_i2 ?_
  intro b hb
  exact common_sub_632_i2 (mem_commonEnvelope childrenD_632_i2 b hb)

theorem finite_children_work_632_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_632_i1 j) (childrenD_632_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_82 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_632_i2.mono (by decide +kernel)

theorem finite_row_works_632_i1 : FiniteTemplate HasSnaky 8 required_632_i1 envelope_632_i1 := by
  refine finite_compose HasSnaky 7 childrenC_632_i1 childrenD_632_i1 finite_children_work_632_i1 (3, 5)
    required_632_i1 envelope_632_i1 pivot_mem_632_i1 child_required_sub_632_i1 child_envelope_sub_632_i1 ?_
  intro b hb
  exact common_sub_632_i1 (mem_commonEnvelope childrenD_632_i1 b hb)

theorem finite_children_work_632_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_632_i0 j) (childrenD_632_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_294 5 (6, 2)).mono (by decide +kernel)
  · exact finite_row_works_632_i1.mono (by decide +kernel)
  · exact finite_row_works_631.mono (by decide +kernel)

theorem finite_row_works_632_i0 : FiniteTemplate HasSnaky 11 required_632_i0 envelope_632_i0 := by
  refine finite_compose HasSnaky 10 childrenC_632_i0 childrenD_632_i0 finite_children_work_632_i0 (3, 4)
    required_632_i0 envelope_632_i0 pivot_mem_632_i0 child_required_sub_632_i0 child_envelope_sub_632_i0 ?_
  intro b hb
  exact common_sub_632_i0 (mem_commonEnvelope childrenD_632_i0 b hb)

theorem finite_children_work_632 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_632 j) (childrenD_632 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_454 5 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_455 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_632_i0.mono (by decide +kernel)

theorem finite_row_works_632 : FiniteTemplate HasSnaky 12 required_632 envelope_632 := by
  refine finite_compose HasSnaky 11 childrenC_632 childrenD_632 finite_children_work_632 (3, 3)
    required_632 envelope_632 pivot_mem_632 child_required_sub_632 child_envelope_sub_632 ?_
  intro b hb
  exact common_sub_632 (mem_commonEnvelope childrenD_632 b hb)

theorem finite_children_work_635_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_635_i0 j) (childrenD_635_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_395 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_635_i0 : FiniteTemplate HasSnaky 9 required_635_i0 envelope_635_i0 := by
  refine finite_compose HasSnaky 8 childrenC_635_i0 childrenD_635_i0 finite_children_work_635_i0 (2, 6)
    required_635_i0 envelope_635_i0 pivot_mem_635_i0 child_required_sub_635_i0 child_envelope_sub_635_i0 ?_
  intro b hb
  exact common_sub_635_i0 (mem_commonEnvelope childrenD_635_i0 b hb)

theorem finite_children_work_635 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_635 j) (childrenD_635 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 6 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_589 3 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_635_i0.mono (by decide +kernel)

theorem finite_row_works_635 : FiniteTemplate HasSnaky 12 required_635 envelope_635 := by
  refine finite_compose HasSnaky 11 childrenC_635 childrenD_635 finite_children_work_635 (2, 3)
    required_635 envelope_635 pivot_mem_635 child_required_sub_635 child_envelope_sub_635 ?_
  intro b hb
  exact common_sub_635 (mem_commonEnvelope childrenD_635 b hb)

theorem finite_children_work_649_i7 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_649_i7 j) (childrenD_649_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_649_i7 : FiniteTemplate HasSnaky 4 required_649_i7 envelope_649_i7 := by
  refine finite_compose HasSnaky 3 childrenC_649_i7 childrenD_649_i7 finite_children_work_649_i7 (1, 3)
    required_649_i7 envelope_649_i7 pivot_mem_649_i7 child_required_sub_649_i7 child_envelope_sub_649_i7 ?_
  intro b hb
  exact common_sub_649_i7 (mem_commonEnvelope childrenD_649_i7 b hb)

theorem finite_children_work_649_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_649_i6 j) (childrenD_649_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_649_i7.mono (by decide +kernel)

theorem finite_row_works_649_i6 : FiniteTemplate HasSnaky 5 required_649_i6 envelope_649_i6 := by
  refine finite_compose HasSnaky 4 childrenC_649_i6 childrenD_649_i6 finite_children_work_649_i6 (2, 3)
    required_649_i6 envelope_649_i6 pivot_mem_649_i6 child_required_sub_649_i6 child_envelope_sub_649_i6 ?_
  intro b hb
  exact common_sub_649_i6 (mem_commonEnvelope childrenD_649_i6 b hb)

theorem finite_children_work_649_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_649_i5 j) (childrenD_649_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 3)).mono (by decide +kernel)
  · exact finite_row_works_649_i6.mono (by decide +kernel)

theorem finite_row_works_649_i5 : FiniteTemplate HasSnaky 6 required_649_i5 envelope_649_i5 := by
  refine finite_compose HasSnaky 5 childrenC_649_i5 childrenD_649_i5 finite_children_work_649_i5 (3, 4)
    required_649_i5 envelope_649_i5 pivot_mem_649_i5 child_required_sub_649_i5 child_envelope_sub_649_i5 ?_
  intro b hb
  exact common_sub_649_i5 (mem_commonEnvelope childrenD_649_i5 b hb)

theorem finite_children_work_649_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_649_i4 j) (childrenD_649_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 5 (5, 5)).mono (by decide +kernel)
  · exact finite_row_works_649_i5.mono (by decide +kernel)

theorem finite_row_works_649_i4 : FiniteTemplate HasSnaky 7 required_649_i4 envelope_649_i4 := by
  refine finite_compose HasSnaky 6 childrenC_649_i4 childrenD_649_i4 finite_children_work_649_i4 (2, 6)
    required_649_i4 envelope_649_i4 pivot_mem_649_i4 child_required_sub_649_i4 child_envelope_sub_649_i4 ?_
  intro b hb
  exact common_sub_649_i4 (mem_commonEnvelope childrenD_649_i4 b hb)

theorem finite_children_work_649_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_649_i3 j) (childrenD_649_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_649_i4.mono (by decide +kernel)

theorem finite_row_works_649_i3 : FiniteTemplate HasSnaky 8 required_649_i3 envelope_649_i3 := by
  refine finite_compose HasSnaky 7 childrenC_649_i3 childrenD_649_i3 finite_children_work_649_i3 (3, 3)
    required_649_i3 envelope_649_i3 pivot_mem_649_i3 child_required_sub_649_i3 child_envelope_sub_649_i3 ?_
  intro b hb
  exact common_sub_649_i3 (mem_commonEnvelope childrenD_649_i3 b hb)

theorem finite_children_work_649_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_649_i2 j) (childrenD_649_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_649_i3.mono (by decide +kernel)

theorem finite_row_works_649_i2 : FiniteTemplate HasSnaky 9 required_649_i2 envelope_649_i2 := by
  refine finite_compose HasSnaky 8 childrenC_649_i2 childrenD_649_i2 finite_children_work_649_i2 (3, 6)
    required_649_i2 envelope_649_i2 pivot_mem_649_i2 child_required_sub_649_i2 child_envelope_sub_649_i2 ?_
  intro b hb
  exact common_sub_649_i2 (mem_commonEnvelope childrenD_649_i2 b hb)

theorem finite_children_work_649_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_649_i1 j) (childrenD_649_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_84 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 1 (3, 3)).mono (by decide +kernel)
  · exact finite_row_works_649_i2.mono (by decide +kernel)

theorem finite_row_works_649_i1 : FiniteTemplate HasSnaky 10 required_649_i1 envelope_649_i1 := by
  refine finite_compose HasSnaky 9 childrenC_649_i1 childrenD_649_i1 finite_children_work_649_i1 (4, 6)
    required_649_i1 envelope_649_i1 pivot_mem_649_i1 child_required_sub_649_i1 child_envelope_sub_649_i1 ?_
  intro b hb
  exact common_sub_649_i1 (mem_commonEnvelope childrenD_649_i1 b hb)

theorem finite_children_work_649_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_649_i0 j) (childrenD_649_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 4 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_649_i1.mono (by decide +kernel)

theorem finite_row_works_649_i0 : FiniteTemplate HasSnaky 11 required_649_i0 envelope_649_i0 := by
  refine finite_compose HasSnaky 10 childrenC_649_i0 childrenD_649_i0 finite_children_work_649_i0 (4, 3)
    required_649_i0 envelope_649_i0 pivot_mem_649_i0 child_required_sub_649_i0 child_envelope_sub_649_i0 ?_
  intro b hb
  exact common_sub_649_i0 (mem_commonEnvelope childrenD_649_i0 b hb)

theorem finite_children_work_649 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_649 j) (childrenD_649 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_523 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_649_i0.mono (by decide +kernel)

theorem finite_row_works_649 : FiniteTemplate HasSnaky 12 required_649 envelope_649 := by
  refine finite_compose HasSnaky 11 childrenC_649 childrenD_649 finite_children_work_649 (4, 4)
    required_649 envelope_649 pivot_mem_649 child_required_sub_649 child_envelope_sub_649 ?_
  intro b hb
  exact common_sub_649 (mem_commonEnvelope childrenD_649 b hb)

theorem finite_children_work_654_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_654_i1 j) (childrenD_654_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_502 3 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_654_i1 : FiniteTemplate HasSnaky 6 required_654_i1 envelope_654_i1 := by
  refine finite_compose HasSnaky 5 childrenC_654_i1 childrenD_654_i1 finite_children_work_654_i1 (4, 6)
    required_654_i1 envelope_654_i1 pivot_mem_654_i1 child_required_sub_654_i1 child_envelope_sub_654_i1 ?_
  intro b hb
  exact common_sub_654_i1 (mem_commonEnvelope childrenD_654_i1 b hb)

theorem finite_children_work_654_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_654_i0 j) (childrenD_654_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_651 6 (7, 8)).mono (by decide +kernel)
  · exact finite_row_works_654_i1.mono (by decide +kernel)

theorem finite_row_works_654_i0 : FiniteTemplate HasSnaky 9 required_654_i0 envelope_654_i0 := by
  refine finite_compose HasSnaky 8 childrenC_654_i0 childrenD_654_i0 finite_children_work_654_i0 (4, 5)
    required_654_i0 envelope_654_i0 pivot_mem_654_i0 child_required_sub_654_i0 child_envelope_sub_654_i0 ?_
  intro b hb
  exact common_sub_654_i0 (mem_commonEnvelope childrenD_654_i0 b hb)

theorem finite_children_work_654 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_654 j) (childrenD_654 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_248 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_300 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_436 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_449 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_509 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_510 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_653 3 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_654_i0.mono (by decide +kernel)

theorem finite_row_works_654 : FiniteTemplate HasSnaky 12 required_654 envelope_654 := by
  refine finite_compose HasSnaky 11 childrenC_654 childrenD_654 finite_children_work_654 (4, 4)
    required_654 envelope_654 pivot_mem_654 child_required_sub_654 child_envelope_sub_654 ?_
  intro b hb
  exact common_sub_654 (mem_commonEnvelope childrenD_654 b hb)

theorem finite_children_work_677 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_677 j) (childrenD_677 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_589 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_676 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_677 : FiniteTemplate HasSnaky 12 required_677 envelope_677 := by
  refine finite_compose HasSnaky 11 childrenC_677 childrenD_677 finite_children_work_677 (3, 3)
    required_677 envelope_677 pivot_mem_677 child_required_sub_677 child_envelope_sub_677 ?_
  intro b hb
  exact common_sub_677 (mem_commonEnvelope childrenD_677 b hb)

theorem finite_children_work_687 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_687 j) (childrenD_687 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_324 2 (6, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_685 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_686 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_687 : FiniteTemplate HasSnaky 12 required_687 envelope_687 := by
  refine finite_compose HasSnaky 11 childrenC_687 childrenD_687 finite_children_work_687 (5, 5)
    required_687 envelope_687 pivot_mem_687 child_required_sub_687 child_envelope_sub_687 ?_
  intro b hb
  exact common_sub_687 (mem_commonEnvelope childrenD_687 b hb)

end FiniteCongruenceChecks.SnakyFinite
