/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height07Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_658_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_658_i0 j) (childrenD_658_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_314 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_378 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_658_i0 : FiniteTemplate HasSnaky 7 required_658_i0 envelope_658_i0 := by
  refine finite_compose HasSnaky 6 childrenC_658_i0 childrenD_658_i0 finite_children_work_658_i0 (2, 6)
    required_658_i0 envelope_658_i0 pivot_mem_658_i0 child_required_sub_658_i0 child_envelope_sub_658_i0 ?_
  intro b hb
  exact common_sub_658_i0 (mem_commonEnvelope childrenD_658_i0 b hb)

theorem finite_children_work_658 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_658 j) (childrenD_658 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_284 4 (1, 9)).mono (by decide +kernel)
  · exact finite_row_works_658_i0.mono (by decide +kernel)

theorem finite_row_works_658 : FiniteTemplate HasSnaky 8 required_658 envelope_658 := by
  refine finite_compose HasSnaky 7 childrenC_658 childrenD_658 finite_children_work_658 (2, 3)
    required_658 envelope_658 pivot_mem_658 child_required_sub_658 child_envelope_sub_658 ?_
  intro b hb
  exact common_sub_658 (mem_commonEnvelope childrenD_658 b hb)

theorem finite_children_work_661_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_661_i0 j) (childrenD_661_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_302 7 (7, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_303 7 (7, 7)).mono (by decide +kernel)

theorem finite_row_works_661_i0 : FiniteTemplate HasSnaky 7 required_661_i0 envelope_661_i0 := by
  refine finite_compose HasSnaky 6 childrenC_661_i0 childrenD_661_i0 finite_children_work_661_i0 (4, 3)
    required_661_i0 envelope_661_i0 pivot_mem_661_i0 child_required_sub_661_i0 child_envelope_sub_661_i0 ?_
  intro b hb
  exact common_sub_661_i0 (mem_commonEnvelope childrenD_661_i0 b hb)

theorem finite_children_work_661 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_661 j) (childrenD_661 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_116 1 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_661_i0.mono (by decide +kernel)

theorem finite_row_works_661 : FiniteTemplate HasSnaky 8 required_661 envelope_661 := by
  refine finite_compose HasSnaky 7 childrenC_661 childrenD_661 finite_children_work_661 (4, 6)
    required_661 envelope_661 pivot_mem_661 child_required_sub_661 child_envelope_sub_661 ?_
  intro b hb
  exact common_sub_661 (mem_commonEnvelope childrenD_661 b hb)

theorem finite_children_work_666_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_666_i1 j) (childrenD_666_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_666_i1 : FiniteTemplate HasSnaky 6 required_666_i1 envelope_666_i1 := by
  refine finite_compose HasSnaky 5 childrenC_666_i1 childrenD_666_i1 finite_children_work_666_i1 (1, 3)
    required_666_i1 envelope_666_i1 pivot_mem_666_i1 child_required_sub_666_i1 child_envelope_sub_666_i1 ?_
  intro b hb
  exact common_sub_666_i1 (mem_commonEnvelope childrenD_666_i1 b hb)

theorem finite_children_work_666_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_666_i0 j) (childrenD_666_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_666_i1.mono (by decide +kernel)

theorem finite_row_works_666_i0 : FiniteTemplate HasSnaky 7 required_666_i0 envelope_666_i0 := by
  refine finite_compose HasSnaky 6 childrenC_666_i0 childrenD_666_i0 finite_children_work_666_i0 (4, 3)
    required_666_i0 envelope_666_i0 pivot_mem_666_i0 child_required_sub_666_i0 child_envelope_sub_666_i0 ?_
  intro b hb
  exact common_sub_666_i0 (mem_commonEnvelope childrenD_666_i0 b hb)

theorem finite_children_work_666 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_666 j) (childrenD_666 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_666_i0.mono (by decide +kernel)

theorem finite_row_works_666 : FiniteTemplate HasSnaky 8 required_666 envelope_666 := by
  refine finite_compose HasSnaky 7 childrenC_666 childrenD_666 finite_children_work_666 (2, 3)
    required_666 envelope_666 pivot_mem_666 child_required_sub_666 child_envelope_sub_666 ?_
  intro b hb
  exact common_sub_666 (mem_commonEnvelope childrenD_666 b hb)

theorem finite_children_work_678_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_678_i1 j) (childrenD_678_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_382 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_678_i1 : FiniteTemplate HasSnaky 6 required_678_i1 envelope_678_i1 := by
  refine finite_compose HasSnaky 5 childrenC_678_i1 childrenD_678_i1 finite_children_work_678_i1 (4, 3)
    required_678_i1 envelope_678_i1 pivot_mem_678_i1 child_required_sub_678_i1 child_envelope_sub_678_i1 ?_
  intro b hb
  exact common_sub_678_i1 (mem_commonEnvelope childrenD_678_i1 b hb)

theorem finite_children_work_678_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_678_i0 j) (childrenD_678_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 6 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_678_i1.mono (by decide +kernel)

theorem finite_row_works_678_i0 : FiniteTemplate HasSnaky 7 required_678_i0 envelope_678_i0 := by
  refine finite_compose HasSnaky 6 childrenC_678_i0 childrenD_678_i0 finite_children_work_678_i0 (2, 6)
    required_678_i0 envelope_678_i0 pivot_mem_678_i0 child_required_sub_678_i0 child_envelope_sub_678_i0 ?_
  intro b hb
  exact common_sub_678_i0 (mem_commonEnvelope childrenD_678_i0 b hb)

theorem finite_children_work_678 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_678 j) (childrenD_678 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_31 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_160 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_678_i0.mono (by decide +kernel)

theorem finite_row_works_678 : FiniteTemplate HasSnaky 8 required_678 envelope_678 := by
  refine finite_compose HasSnaky 7 childrenC_678 childrenD_678 finite_children_work_678 (1, 5)
    required_678 envelope_678 pivot_mem_678 child_required_sub_678 child_envelope_sub_678 ?_
  intro b hb
  exact common_sub_678 (mem_commonEnvelope childrenD_678 b hb)

theorem finite_children_work_703_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_703_i1 j) (childrenD_703_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 0 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_703_i1 : FiniteTemplate HasSnaky 5 required_703_i1 envelope_703_i1 := by
  refine finite_compose HasSnaky 4 childrenC_703_i1 childrenD_703_i1 finite_children_work_703_i1 (5, 3)
    required_703_i1 envelope_703_i1 pivot_mem_703_i1 child_required_sub_703_i1 child_envelope_sub_703_i1 ?_
  intro b hb
  exact common_sub_703_i1 (mem_commonEnvelope childrenD_703_i1 b hb)

theorem finite_children_work_703_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_703_i2 j) (childrenD_703_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 4 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_703_i2 : FiniteTemplate HasSnaky 4 required_703_i2 envelope_703_i2 := by
  refine finite_compose HasSnaky 3 childrenC_703_i2 childrenD_703_i2 finite_children_work_703_i2 (2, 3)
    required_703_i2 envelope_703_i2 pivot_mem_703_i2 child_required_sub_703_i2 child_envelope_sub_703_i2 ?_
  intro b hb
  exact common_sub_703_i2 (mem_commonEnvelope childrenD_703_i2 b hb)

theorem finite_children_work_703_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_703_i3 j) (childrenD_703_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_101 4 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_703_i3 : FiniteTemplate HasSnaky 4 required_703_i3 envelope_703_i3 := by
  refine finite_compose HasSnaky 3 childrenC_703_i3 childrenD_703_i3 finite_children_work_703_i3 (3, 2)
    required_703_i3 envelope_703_i3 pivot_mem_703_i3 child_required_sub_703_i3 child_envelope_sub_703_i3 ?_
  intro b hb
  exact common_sub_703_i3 (mem_commonEnvelope childrenD_703_i3 b hb)

theorem finite_children_work_703_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_703_i0 j) (childrenD_703_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_195 0 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_703_i1.mono (by decide +kernel)
  · exact finite_row_works_703_i2.mono (by decide +kernel)
  · exact finite_row_works_703_i3.mono (by decide +kernel)

theorem finite_row_works_703_i0 : FiniteTemplate HasSnaky 6 required_703_i0 envelope_703_i0 := by
  refine finite_compose HasSnaky 5 childrenC_703_i0 childrenD_703_i0 finite_children_work_703_i0 (3, 3)
    required_703_i0 envelope_703_i0 pivot_mem_703_i0 child_required_sub_703_i0 child_envelope_sub_703_i0 ?_
  intro b hb
  exact common_sub_703_i0 (mem_commonEnvelope childrenD_703_i0 b hb)

theorem finite_children_work_703_i7 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_703_i7 j) (childrenD_703_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_103 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_157 2 (5, 1)).mono (by decide +kernel)

theorem finite_row_works_703_i7 : FiniteTemplate HasSnaky 4 required_703_i7 envelope_703_i7 := by
  refine finite_compose HasSnaky 3 childrenC_703_i7 childrenD_703_i7 finite_children_work_703_i7 (2, 2)
    required_703_i7 envelope_703_i7 pivot_mem_703_i7 child_required_sub_703_i7 child_envelope_sub_703_i7 ?_
  intro b hb
  exact common_sub_703_i7 (mem_commonEnvelope childrenD_703_i7 b hb)

theorem finite_children_work_703_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_703_i6 j) (childrenD_703_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (4, 5)).mono (by decide +kernel)
  · exact finite_row_works_703_i7.mono (by decide +kernel)

theorem finite_row_works_703_i6 : FiniteTemplate HasSnaky 5 required_703_i6 envelope_703_i6 := by
  refine finite_compose HasSnaky 4 childrenC_703_i6 childrenD_703_i6 finite_children_work_703_i6 (5, 2)
    required_703_i6 envelope_703_i6 pivot_mem_703_i6 child_required_sub_703_i6 child_envelope_sub_703_i6 ?_
  intro b hb
  exact common_sub_703_i6 (mem_commonEnvelope childrenD_703_i6 b hb)

theorem finite_children_work_703_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_703_i5 j) (childrenD_703_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact finite_row_works_703_i6.mono (by decide +kernel)

theorem finite_row_works_703_i5 : FiniteTemplate HasSnaky 6 required_703_i5 envelope_703_i5 := by
  refine finite_compose HasSnaky 5 childrenC_703_i5 childrenD_703_i5 finite_children_work_703_i5 (3, 2)
    required_703_i5 envelope_703_i5 pivot_mem_703_i5 child_required_sub_703_i5 child_envelope_sub_703_i5 ?_
  intro b hb
  exact common_sub_703_i5 (mem_commonEnvelope childrenD_703_i5 b hb)

theorem finite_children_work_703_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_703_i4 j) (childrenD_703_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_703_i5.mono (by decide +kernel)

theorem finite_row_works_703_i4 : FiniteTemplate HasSnaky 7 required_703_i4 envelope_703_i4 := by
  refine finite_compose HasSnaky 6 childrenC_703_i4 childrenD_703_i4 finite_children_work_703_i4 (4, 2)
    required_703_i4 envelope_703_i4 pivot_mem_703_i4 child_required_sub_703_i4 child_envelope_sub_703_i4 ?_
  intro b hb
  exact common_sub_703_i4 (mem_commonEnvelope childrenD_703_i4 b hb)

theorem finite_children_work_703_i9 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_703_i9 j) (childrenD_703_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_77 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_703_i9 : FiniteTemplate HasSnaky 5 required_703_i9 envelope_703_i9 := by
  refine finite_compose HasSnaky 4 childrenC_703_i9 childrenD_703_i9 finite_children_work_703_i9 (5, 3)
    required_703_i9 envelope_703_i9 pivot_mem_703_i9 child_required_sub_703_i9 child_envelope_sub_703_i9 ?_
  intro b hb
  exact common_sub_703_i9 (mem_commonEnvelope childrenD_703_i9 b hb)

theorem finite_children_work_703_i8 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_703_i8 j) (childrenD_703_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_703_i9.mono (by decide +kernel)

theorem finite_row_works_703_i8 : FiniteTemplate HasSnaky 6 required_703_i8 envelope_703_i8 := by
  refine finite_compose HasSnaky 5 childrenC_703_i8 childrenD_703_i8 finite_children_work_703_i8 (4, 6)
    required_703_i8 envelope_703_i8 pivot_mem_703_i8 child_required_sub_703_i8 child_envelope_sub_703_i8 ?_
  intro b hb
  exact common_sub_703_i8 (mem_commonEnvelope childrenD_703_i8 b hb)

theorem finite_children_work_703 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_703 j) (childrenD_703 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 2 (5, 0)).mono (by decide +kernel)
  · exact finite_row_works_703_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_516 4 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_703_i4.mono (by decide +kernel)
  · exact finite_row_works_703_i8.mono (by decide +kernel)

theorem finite_row_works_703 : FiniteTemplate HasSnaky 8 required_703 envelope_703 := by
  refine finite_compose HasSnaky 7 childrenC_703 childrenD_703 finite_children_work_703 (4, 3)
    required_703 envelope_703 pivot_mem_703 child_required_sub_703 child_envelope_sub_703 ?_
  intro b hb
  exact common_sub_703 (mem_commonEnvelope childrenD_703 b hb)

end FiniteCongruenceChecks.SnakyFinite
