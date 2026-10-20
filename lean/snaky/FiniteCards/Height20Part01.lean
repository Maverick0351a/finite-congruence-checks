/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height20Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height08Part05
import FiniteCards.Height10Part01
import FiniteCards.Height11Part02
import FiniteCards.Height11Part06
import FiniteCards.Height12Part02
import FiniteCards.Height12Part03
import FiniteCards.Height12Part04
import FiniteCards.Height12Part05
import FiniteCards.Height13Part01
import FiniteCards.Height13Part03
import FiniteCards.Height13Part04
import FiniteCards.Height13Part06
import FiniteCards.Height15Part02
import FiniteCards.Height15Part03
import FiniteCards.Height16Part03
import FiniteCards.Height17Part02
import FiniteCards.Height18Part01
import FiniteCards.Height18Part02
import FiniteCards.Height19Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_708_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_708_i2 j) (childrenD_708_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 5 (9, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_234 1 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_241 5 (9, 7)).mono (by decide +kernel)

theorem finite_row_works_708_i2 : FiniteTemplate HasSnaky 6 required_708_i2 envelope_708_i2 := by
  refine finite_compose HasSnaky 5 childrenC_708_i2 childrenD_708_i2 finite_children_work_708_i2 (5, 8)
    required_708_i2 envelope_708_i2 pivot_mem_708_i2 child_required_sub_708_i2 child_envelope_sub_708_i2 ?_
  intro b hb
  exact common_sub_708_i2 (mem_commonEnvelope childrenD_708_i2 b hb)

theorem finite_children_work_708_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_708_i4 j) (childrenD_708_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_92 5 (9, 6)).mono (by decide +kernel)

theorem finite_row_works_708_i4 : FiniteTemplate HasSnaky 5 required_708_i4 envelope_708_i4 := by
  refine finite_compose HasSnaky 4 childrenC_708_i4 childrenD_708_i4 finite_children_work_708_i4 (7, 9)
    required_708_i4 envelope_708_i4 pivot_mem_708_i4 child_required_sub_708_i4 child_envelope_sub_708_i4 ?_
  intro b hb
  exact common_sub_708_i4 (mem_commonEnvelope childrenD_708_i4 b hb)

theorem finite_children_work_708_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_708_i3 j) (childrenD_708_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (7, 5)).mono (by decide +kernel)
  · exact finite_row_works_708_i4.mono (by decide +kernel)

theorem finite_row_works_708_i3 : FiniteTemplate HasSnaky 6 required_708_i3 envelope_708_i3 := by
  refine finite_compose HasSnaky 5 childrenC_708_i3 childrenD_708_i3 finite_children_work_708_i3 (7, 6)
    required_708_i3 envelope_708_i3 pivot_mem_708_i3 child_required_sub_708_i3 child_envelope_sub_708_i3 ?_
  intro b hb
  exact common_sub_708_i3 (mem_commonEnvelope childrenD_708_i3 b hb)

theorem finite_children_work_708_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_708_i1 j) (childrenD_708_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_57 2 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_88 2 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_111 2 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_213 0 (5, 5)).mono (by decide +kernel)
  · exact finite_row_works_708_i2.mono (by decide +kernel)
  · exact finite_row_works_708_i3.mono (by decide +kernel)

theorem finite_row_works_708_i1 : FiniteTemplate HasSnaky 7 required_708_i1 envelope_708_i1 := by
  refine finite_compose HasSnaky 6 childrenC_708_i1 childrenD_708_i1 finite_children_work_708_i1 (7, 7)
    required_708_i1 envelope_708_i1 pivot_mem_708_i1 child_required_sub_708_i1 child_envelope_sub_708_i1 ?_
  intro b hb
  exact common_sub_708_i1 (mem_commonEnvelope childrenD_708_i1 b hb)

theorem finite_children_work_708_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_708_i5 j) (childrenD_708_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 5 (11, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_292 6 (9, 11)).mono (by decide +kernel)

theorem finite_row_works_708_i5 : FiniteTemplate HasSnaky 7 required_708_i5 envelope_708_i5 := by
  refine finite_compose HasSnaky 6 childrenC_708_i5 childrenD_708_i5 finite_children_work_708_i5 (9, 8)
    required_708_i5 envelope_708_i5 pivot_mem_708_i5 child_required_sub_708_i5 child_envelope_sub_708_i5 ?_
  intro b hb
  exact common_sub_708_i5 (mem_commonEnvelope childrenD_708_i5 b hb)

theorem finite_children_work_708_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_708_i0 j) (childrenD_708_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_117 0 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_137 2 (9, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 2 (9, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_257 2 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 2 (9, 5)).mono (by decide +kernel)
  · exact finite_row_works_708_i1.mono (by decide +kernel)
  · exact finite_row_works_708_i5.mono (by decide +kernel)

theorem finite_row_works_708_i0 : FiniteTemplate HasSnaky 9 required_708_i0 envelope_708_i0 := by
  refine finite_compose HasSnaky 8 childrenC_708_i0 childrenD_708_i0 finite_children_work_708_i0 (6, 8)
    required_708_i0 envelope_708_i0 pivot_mem_708_i0 child_required_sub_708_i0 child_envelope_sub_708_i0 ?_
  intro b hb
  exact common_sub_708_i0 (mem_commonEnvelope childrenD_708_i0 b hb)

theorem finite_children_work_708_i6 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_708_i6 j) (childrenD_708_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 3 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 5 (11, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 0 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (6, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_565 4 (5, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_687 2 (12, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_689 0 (5, 4)).mono (by decide +kernel)

theorem finite_row_works_708_i6 : FiniteTemplate HasSnaky 13 required_708_i6 envelope_708_i6 := by
  refine finite_compose HasSnaky 12 childrenC_708_i6 childrenD_708_i6 finite_children_work_708_i6 (9, 8)
    required_708_i6 envelope_708_i6 pivot_mem_708_i6 child_required_sub_708_i6 child_envelope_sub_708_i6 ?_
  intro b hb
  exact common_sub_708_i6 (mem_commonEnvelope childrenD_708_i6 b hb)

theorem finite_children_work_708_i7 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_708_i7 j) (childrenD_708_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 1 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 3 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 5 (11, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 7 (11, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_490 0 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_490 2 (11, 1)).mono (by decide +kernel)

theorem finite_row_works_708_i7 : FiniteTemplate HasSnaky 14 required_708_i7 envelope_708_i7 := by
  refine finite_compose HasSnaky 13 childrenC_708_i7 childrenD_708_i7 finite_children_work_708_i7 (9, 8)
    required_708_i7 envelope_708_i7 pivot_mem_708_i7 child_required_sub_708_i7 child_envelope_sub_708_i7 ?_
  intro b hb
  exact common_sub_708_i7 (mem_commonEnvelope childrenD_708_i7 b hb)

theorem finite_children_work_708 : ∀ j, FiniteTemplate HasSnaky 19 (childrenC_708 j) (childrenD_708 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 5 (12, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 5 (11, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 3 (4, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_603 1 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 0 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 6 (11, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_684 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_708_i0.mono (by decide +kernel)
  · exact finite_row_works_708_i6.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_694 7 (13, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_695 0 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_696 5 (13, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_698 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_701 2 (13, 1)).mono (by decide +kernel)
  · exact finite_row_works_708_i7.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_707 2 (12, 3)).mono (by decide +kernel)

theorem finite_row_works_708 : FiniteTemplate HasSnaky 20 required_708 envelope_708 := by
  refine finite_compose HasSnaky 19 childrenC_708 childrenD_708 finite_children_work_708 (7, 8)
    required_708 envelope_708 pivot_mem_708 child_required_sub_708 child_envelope_sub_708 ?_
  intro b hb
  exact common_sub_708 (mem_commonEnvelope childrenD_708 b hb)

theorem finite_children_work_725 : ∀ j, FiniteTemplate HasSnaky 19 (childrenC_725 j) (childrenD_725 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 4 (6, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_579 7 (11, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_581 6 (11, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_654 4 (4, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_661 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_677 6 (10, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_682 7 (12, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_694 4 (2, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_696 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_698 6 (11, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_709 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_710 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_715 3 (2, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_717 7 (13, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_718 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_724 6 (12, 15)).mono (by decide +kernel)

theorem finite_row_works_725 : FiniteTemplate HasSnaky 20 required_725 envelope_725 := by
  refine finite_compose HasSnaky 19 childrenC_725 childrenD_725 finite_children_work_725 (7, 8)
    required_725 envelope_725 pivot_mem_725 child_required_sub_725 child_envelope_sub_725 ?_
  intro b hb
  exact common_sub_725 (mem_commonEnvelope childrenD_725 b hb)

theorem finite_children_work_726 : ∀ j, FiniteTemplate HasSnaky 19 (childrenC_726 j) (childrenD_726 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 1 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_579 4 (6, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_581 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_654 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_661 5 (12, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_677 3 (3, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_682 4 (4, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_694 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_696 5 (13, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_698 3 (3, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_709 5 (13, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_710 5 (12, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_715 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_717 4 (3, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_718 5 (13, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_724 5 (15, 2)).mono (by decide +kernel)

theorem finite_row_works_726 : FiniteTemplate HasSnaky 20 required_726 envelope_726 := by
  refine finite_compose HasSnaky 19 childrenC_726 childrenD_726 finite_children_work_726 (8, 7)
    required_726 envelope_726 pivot_mem_726 child_required_sub_726 child_envelope_sub_726 ?_
  intro b hb
  exact common_sub_726 (mem_commonEnvelope childrenD_726 b hb)

end FiniteCongruenceChecks.SnakyFinite
