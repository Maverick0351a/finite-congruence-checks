/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height08Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_719_i5 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_719_i5 j) (childrenD_719_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_412 0 (3, 4)).mono (by decide +kernel)

theorem finite_row_works_719_i5 : FiniteTemplate HasSnaky 9 required_719_i5 envelope_719_i5 := by
  refine finite_compose HasSnaky 8 childrenC_719_i5 childrenD_719_i5 finite_children_work_719_i5 (3, 8)
    required_719_i5 envelope_719_i5 pivot_mem_719_i5 child_required_sub_719_i5 child_envelope_sub_719_i5 ?_
  intro b hb
  exact common_sub_719_i5 (mem_commonEnvelope childrenD_719_i5 b hb)

theorem finite_children_work_719_i4 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_719_i4 j) (childrenD_719_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_45 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_343 5 (6, 5)).mono (by decide +kernel)
  · exact finite_row_works_719_i5.mono (by decide +kernel)

theorem finite_row_works_719_i4 : FiniteTemplate HasSnaky 10 required_719_i4 envelope_719_i4 := by
  refine finite_compose HasSnaky 9 childrenC_719_i4 childrenD_719_i4 finite_children_work_719_i4 (4, 5)
    required_719_i4 envelope_719_i4 pivot_mem_719_i4 child_required_sub_719_i4 child_envelope_sub_719_i4 ?_
  intro b hb
  exact common_sub_719_i4 (mem_commonEnvelope childrenD_719_i4 b hb)

theorem finite_children_work_719_i3 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_719_i3 j) (childrenD_719_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 9)).mono (by decide +kernel)
  · exact finite_row_works_719_i4.mono (by decide +kernel)

theorem finite_row_works_719_i3 : FiniteTemplate HasSnaky 11 required_719_i3 envelope_719_i3 := by
  refine finite_compose HasSnaky 10 childrenC_719_i3 childrenD_719_i3 finite_children_work_719_i3 (4, 8)
    required_719_i3 envelope_719_i3 pivot_mem_719_i3 child_required_sub_719_i3 child_envelope_sub_719_i3 ?_
  intro b hb
  exact common_sub_719_i3 (mem_commonEnvelope childrenD_719_i3 b hb)

theorem finite_children_work_719_i2 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_719_i2 j) (childrenD_719_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 1 (3, 3)).mono (by decide +kernel)
  · exact finite_row_works_719_i3.mono (by decide +kernel)

theorem finite_row_works_719_i2 : FiniteTemplate HasSnaky 12 required_719_i2 envelope_719_i2 := by
  refine finite_compose HasSnaky 11 childrenC_719_i2 childrenD_719_i2 finite_children_work_719_i2 (4, 7)
    required_719_i2 envelope_719_i2 pivot_mem_719_i2 child_required_sub_719_i2 child_envelope_sub_719_i2 ?_
  intro b hb
  exact common_sub_719_i2 (mem_commonEnvelope childrenD_719_i2 b hb)

theorem finite_children_work_719_i1 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_719_i1 j) (childrenD_719_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 1 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_209 7 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_719_i2.mono (by decide +kernel)

theorem finite_row_works_719_i1 : FiniteTemplate HasSnaky 13 required_719_i1 envelope_719_i1 := by
  refine finite_compose HasSnaky 12 childrenC_719_i1 childrenD_719_i1 finite_children_work_719_i1 (4, 6)
    required_719_i1 envelope_719_i1 pivot_mem_719_i1 child_required_sub_719_i1 child_envelope_sub_719_i1 ?_
  intro b hb
  exact common_sub_719_i1 (mem_commonEnvelope childrenD_719_i1 b hb)

theorem finite_children_work_719_i0 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_719_i0 j) (childrenD_719_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 6 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_209 6 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_719_i1.mono (by decide +kernel)

theorem finite_row_works_719_i0 : FiniteTemplate HasSnaky 14 required_719_i0 envelope_719_i0 := by
  refine finite_compose HasSnaky 13 childrenC_719_i0 childrenD_719_i0 finite_children_work_719_i0 (3, 6)
    required_719_i0 envelope_719_i0 pivot_mem_719_i0 child_required_sub_719_i0 child_envelope_sub_719_i0 ?_
  intro b hb
  exact common_sub_719_i0 (mem_commonEnvelope childrenD_719_i0 b hb)

theorem finite_children_work_719_i6 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_719_i6 j) (childrenD_719_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_65 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_301 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_417 7 (5, 5)).mono (by decide +kernel)

theorem finite_row_works_719_i6 : FiniteTemplate HasSnaky 7 required_719_i6 envelope_719_i6 := by
  refine finite_compose HasSnaky 6 childrenC_719_i6 childrenD_719_i6 finite_children_work_719_i6 (3, 4)
    required_719_i6 envelope_719_i6 pivot_mem_719_i6 child_required_sub_719_i6 child_envelope_sub_719_i6 ?_
  intro b hb
  exact common_sub_719_i6 (mem_commonEnvelope childrenD_719_i6 b hb)

theorem finite_children_work_719_i7 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_719_i7 j) (childrenD_719_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_65 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_72 1 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_719_i7 : FiniteTemplate HasSnaky 6 required_719_i7 envelope_719_i7 := by
  refine finite_compose HasSnaky 5 childrenC_719_i7 childrenD_719_i7 finite_children_work_719_i7 (3, 4)
    required_719_i7 envelope_719_i7 pivot_mem_719_i7 child_required_sub_719_i7 child_envelope_sub_719_i7 ?_
  intro b hb
  exact common_sub_719_i7 (mem_commonEnvelope childrenD_719_i7 b hb)

theorem finite_children_work_719 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_719 j) (childrenD_719 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_318 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_334 4 (2, 7)).mono (by decide +kernel)
  · exact finite_row_works_719_i0.mono (by decide +kernel)
  · exact finite_row_works_719_i6.mono (by decide +kernel)
  · exact finite_row_works_719_i7.mono (by decide +kernel)

theorem finite_row_works_719 : FiniteTemplate HasSnaky 15 required_719 envelope_719 := by
  refine finite_compose HasSnaky 14 childrenC_719 childrenD_719 finite_children_work_719 (3, 3)
    required_719 envelope_719 pivot_mem_719 child_required_sub_719 child_envelope_sub_719 ?_
  intro b hb
  exact common_sub_719 (mem_commonEnvelope childrenD_719 b hb)

end FiniteCongruenceChecks.SnakyFinite
