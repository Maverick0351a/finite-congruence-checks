/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height16Part03
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height08Part04
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height10Part06
import FiniteCards.Height12Part04
import FiniteCards.Height12Part05
import FiniteCards.Height13Part07
import FiniteCards.Height15Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_724_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_724_i0 j) (childrenD_724_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_57 0 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_111 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_390 5 (10, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_397 0 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_724_i0 : FiniteTemplate HasSnaky 10 required_724_i0 envelope_724_i0 := by
  refine finite_compose HasSnaky 9 childrenC_724_i0 childrenD_724_i0 finite_children_work_724_i0 (4, 8)
    required_724_i0 envelope_724_i0 pivot_mem_724_i0 child_required_sub_724_i0 child_envelope_sub_724_i0 ?_
  intro b hb
  exact common_sub_724_i0 (mem_commonEnvelope childrenD_724_i0 b hb)

theorem finite_children_work_724_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_724_i2 j) (childrenD_724_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 5 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 7 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_395 0 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_724_i2 : FiniteTemplate HasSnaky 9 required_724_i2 envelope_724_i2 := by
  refine finite_compose HasSnaky 8 childrenC_724_i2 childrenD_724_i2 finite_children_work_724_i2 (4, 8)
    required_724_i2 envelope_724_i2 pivot_mem_724_i2 child_required_sub_724_i2 child_envelope_sub_724_i2 ?_
  intro b hb
  exact common_sub_724_i2 (mem_commonEnvelope childrenD_724_i2 b hb)

theorem finite_children_work_724_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_724_i3 j) (childrenD_724_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 5 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_231 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_279 0 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_724_i3 : FiniteTemplate HasSnaky 6 required_724_i3 envelope_724_i3 := by
  refine finite_compose HasSnaky 5 childrenC_724_i3 childrenD_724_i3 finite_children_work_724_i3 (4, 8)
    required_724_i3 envelope_724_i3 pivot_mem_724_i3 child_required_sub_724_i3 child_envelope_sub_724_i3 ?_
  intro b hb
  exact common_sub_724_i3 (mem_commonEnvelope childrenD_724_i3 b hb)

theorem finite_children_work_724_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_724_i4 j) (childrenD_724_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 6 (6, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_637 0 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_724_i4 : FiniteTemplate HasSnaky 8 required_724_i4 envelope_724_i4 := by
  refine finite_compose HasSnaky 7 childrenC_724_i4 childrenD_724_i4 finite_children_work_724_i4 (6, 9)
    required_724_i4 envelope_724_i4 pivot_mem_724_i4 child_required_sub_724_i4 child_envelope_sub_724_i4 ?_
  intro b hb
  exact common_sub_724_i4 (mem_commonEnvelope childrenD_724_i4 b hb)

theorem finite_children_work_724_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_724_i1 j) (childrenD_724_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 1 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 3 (3, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_258 0 (5, 5)).mono (by decide +kernel)
  · exact finite_row_works_724_i2.mono (by decide +kernel)
  · exact finite_row_works_724_i3.mono (by decide +kernel)
  · exact finite_row_works_724_i4.mono (by decide +kernel)

theorem finite_row_works_724_i1 : FiniteTemplate HasSnaky 10 required_724_i1 envelope_724_i1 := by
  refine finite_compose HasSnaky 9 childrenC_724_i1 childrenD_724_i1 finite_children_work_724_i1 (7, 8)
    required_724_i1 envelope_724_i1 pivot_mem_724_i1 child_required_sub_724_i1 child_envelope_sub_724_i1 ?_
  intro b hb
  exact common_sub_724_i1 (mem_commonEnvelope childrenD_724_i1 b hb)

theorem finite_children_work_724_i5 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_724_i5 j) (childrenD_724_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 7 (8, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 1 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_720 7 (10, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_720 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_724_i5 : FiniteTemplate HasSnaky 14 required_724_i5 envelope_724_i5 := by
  refine finite_compose HasSnaky 13 childrenC_724_i5 childrenD_724_i5 finite_children_work_724_i5 (4, 7)
    required_724_i5 envelope_724_i5 pivot_mem_724_i5 child_required_sub_724_i5 child_envelope_sub_724_i5 ?_
  intro b hb
  exact common_sub_724_i5 (mem_commonEnvelope childrenD_724_i5 b hb)

theorem finite_children_work_724_i6 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_724_i6 j) (childrenD_724_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_512 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_600 3 (2, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_621 6 (9, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_702 1 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_714 2 (8, 3)).mono (by decide +kernel)

theorem finite_row_works_724_i6 : FiniteTemplate HasSnaky 11 required_724_i6 envelope_724_i6 := by
  refine finite_compose HasSnaky 10 childrenC_724_i6 childrenD_724_i6 finite_children_work_724_i6 (6, 7)
    required_724_i6 envelope_724_i6 pivot_mem_724_i6 child_required_sub_724_i6 child_envelope_sub_724_i6 ?_
  intro b hb
  exact common_sub_724_i6 (mem_commonEnvelope childrenD_724_i6 b hb)

theorem finite_children_work_724_i8 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_724_i8 j) (childrenD_724_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_604 0 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_724_i8 : FiniteTemplate HasSnaky 9 required_724_i8 envelope_724_i8 := by
  refine finite_compose HasSnaky 8 childrenC_724_i8 childrenD_724_i8 finite_children_work_724_i8 (7, 8)
    required_724_i8 envelope_724_i8 pivot_mem_724_i8 child_required_sub_724_i8 child_envelope_sub_724_i8 ?_
  intro b hb
  exact common_sub_724_i8 (mem_commonEnvelope childrenD_724_i8 b hb)

theorem finite_children_work_724_i7 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_724_i7 j) (childrenD_724_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_88 0 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_231 2 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_267 5 (8, 6)).mono (by decide +kernel)
  · exact finite_row_works_724_i8.mono (by decide +kernel)

theorem finite_row_works_724_i7 : FiniteTemplate HasSnaky 10 required_724_i7 envelope_724_i7 := by
  refine finite_compose HasSnaky 9 childrenC_724_i7 childrenD_724_i7 finite_children_work_724_i7 (4, 8)
    required_724_i7 envelope_724_i7 pivot_mem_724_i7 child_required_sub_724_i7 child_envelope_sub_724_i7 ?_
  intro b hb
  exact common_sub_724_i7 (mem_commonEnvelope childrenD_724_i7 b hb)

theorem finite_children_work_724 : ∀ j, FiniteTemplate HasSnaky 15 (childrenC_724 j) (childrenD_724 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_523 5 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_524 5 (9, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_677 1 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_724_i0.mono (by decide +kernel)
  · exact finite_row_works_724_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_719 7 (10, 10)).mono (by decide +kernel)
  · exact finite_row_works_724_i5.mono (by decide +kernel)
  · exact finite_row_works_724_i6.mono (by decide +kernel)
  · exact finite_row_works_724_i7.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_723 6 (8, 13)).mono (by decide +kernel)

theorem finite_row_works_724 : FiniteTemplate HasSnaky 16 required_724 envelope_724 := by
  refine finite_compose HasSnaky 15 childrenC_724 childrenD_724 finite_children_work_724 (6, 8)
    required_724 envelope_724 pivot_mem_724 child_required_sub_724 child_envelope_sub_724 ?_
  intro b hb
  exact common_sub_724 (mem_commonEnvelope childrenD_724 b hb)

end FiniteCongruenceChecks.SnakyFinite
