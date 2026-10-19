/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part06
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height08Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_595_i6 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_595_i6 j) (childrenD_595_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_595_i6 : FiniteTemplate HasSnaky 2 required_595_i6 envelope_595_i6 := by
  refine finite_compose HasSnaky 1 childrenC_595_i6 childrenD_595_i6 finite_children_work_595_i6 (4, 1)
    required_595_i6 envelope_595_i6 pivot_mem_595_i6 child_required_sub_595_i6 child_envelope_sub_595_i6 ?_
  intro b hb
  exact common_sub_595_i6 (mem_commonEnvelope childrenD_595_i6 b hb)

theorem finite_children_work_595_i5 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_595_i5 j) (childrenD_595_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 7 (6, 4)).mono (by decide +kernel)
  · exact finite_row_works_595_i6.mono (by decide +kernel)

theorem finite_row_works_595_i5 : FiniteTemplate HasSnaky 3 required_595_i5 envelope_595_i5 := by
  refine finite_compose HasSnaky 2 childrenC_595_i5 childrenD_595_i5 finite_children_work_595_i5 (5, 0)
    required_595_i5 envelope_595_i5 pivot_mem_595_i5 child_required_sub_595_i5 child_envelope_sub_595_i5 ?_
  intro b hb
  exact common_sub_595_i5 (mem_commonEnvelope childrenD_595_i5 b hb)

theorem finite_children_work_595_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_595_i4 j) (childrenD_595_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (6, 5)).mono (by decide +kernel)
  · exact finite_row_works_595_i5.mono (by decide +kernel)

theorem finite_row_works_595_i4 : FiniteTemplate HasSnaky 4 required_595_i4 envelope_595_i4 := by
  refine finite_compose HasSnaky 3 childrenC_595_i4 childrenD_595_i4 finite_children_work_595_i4 (5, 1)
    required_595_i4 envelope_595_i4 pivot_mem_595_i4 child_required_sub_595_i4 child_envelope_sub_595_i4 ?_
  intro b hb
  exact common_sub_595_i4 (mem_commonEnvelope childrenD_595_i4 b hb)

theorem finite_children_work_595_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_595_i3 j) (childrenD_595_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_595_i4.mono (by decide +kernel)

theorem finite_row_works_595_i3 : FiniteTemplate HasSnaky 5 required_595_i3 envelope_595_i3 := by
  refine finite_compose HasSnaky 4 childrenC_595_i3 childrenD_595_i3 finite_children_work_595_i3 (2, 1)
    required_595_i3 envelope_595_i3 pivot_mem_595_i3 child_required_sub_595_i3 child_envelope_sub_595_i3 ?_
  intro b hb
  exact common_sub_595_i3 (mem_commonEnvelope childrenD_595_i3 b hb)

theorem finite_children_work_595_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_595_i7 j) (childrenD_595_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_208 7 (7, 5)).mono (by decide +kernel)

theorem finite_row_works_595_i7 : FiniteTemplate HasSnaky 5 required_595_i7 envelope_595_i7 := by
  refine finite_compose HasSnaky 4 childrenC_595_i7 childrenD_595_i7 finite_children_work_595_i7 (4, 2)
    required_595_i7 envelope_595_i7 pivot_mem_595_i7 child_required_sub_595_i7 child_envelope_sub_595_i7 ?_
  intro b hb
  exact common_sub_595_i7 (mem_commonEnvelope childrenD_595_i7 b hb)

theorem finite_children_work_595_i9 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_595_i9 j) (childrenD_595_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_153 1 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_595_i9 : FiniteTemplate HasSnaky 3 required_595_i9 envelope_595_i9 := by
  refine finite_compose HasSnaky 2 childrenC_595_i9 childrenD_595_i9 finite_children_work_595_i9 (4, 2)
    required_595_i9 envelope_595_i9 pivot_mem_595_i9 child_required_sub_595_i9 child_envelope_sub_595_i9 ?_
  intro b hb
  exact common_sub_595_i9 (mem_commonEnvelope childrenD_595_i9 b hb)

theorem finite_children_work_595_i8 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_595_i8 j) (childrenD_595_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (6, 5)).mono (by decide +kernel)
  · exact finite_row_works_595_i9.mono (by decide +kernel)

theorem finite_row_works_595_i8 : FiniteTemplate HasSnaky 4 required_595_i8 envelope_595_i8 := by
  refine finite_compose HasSnaky 3 childrenC_595_i8 childrenD_595_i8 finite_children_work_595_i8 (5, 2)
    required_595_i8 envelope_595_i8 pivot_mem_595_i8 child_required_sub_595_i8 child_envelope_sub_595_i8 ?_
  intro b hb
  exact common_sub_595_i8 (mem_commonEnvelope childrenD_595_i8 b hb)

theorem finite_children_work_595_i10 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_595_i10 j) (childrenD_595_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_157 7 (7, 5)).mono (by decide +kernel)

theorem finite_row_works_595_i10 : FiniteTemplate HasSnaky 4 required_595_i10 envelope_595_i10 := by
  refine finite_compose HasSnaky 3 childrenC_595_i10 childrenD_595_i10 finite_children_work_595_i10 (4, 2)
    required_595_i10 envelope_595_i10 pivot_mem_595_i10 child_required_sub_595_i10 child_envelope_sub_595_i10 ?_
  intro b hb
  exact common_sub_595_i10 (mem_commonEnvelope childrenD_595_i10 b hb)

theorem finite_children_work_595_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_595_i2 j) (childrenD_595_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 7 (7, 5)).mono (by decide +kernel)
  · exact finite_row_works_595_i3.mono (by decide +kernel)
  · exact finite_row_works_595_i7.mono (by decide +kernel)
  · exact finite_row_works_595_i8.mono (by decide +kernel)
  · exact finite_row_works_595_i10.mono (by decide +kernel)

theorem finite_row_works_595_i2 : FiniteTemplate HasSnaky 6 required_595_i2 envelope_595_i2 := by
  refine finite_compose HasSnaky 5 childrenC_595_i2 childrenD_595_i2 finite_children_work_595_i2 (6, 2)
    required_595_i2 envelope_595_i2 pivot_mem_595_i2 child_required_sub_595_i2 child_envelope_sub_595_i2 ?_
  intro b hb
  exact common_sub_595_i2 (mem_commonEnvelope childrenD_595_i2 b hb)

theorem finite_children_work_595_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_595_i1 j) (childrenD_595_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_595_i2.mono (by decide +kernel)

theorem finite_row_works_595_i1 : FiniteTemplate HasSnaky 7 required_595_i1 envelope_595_i1 := by
  refine finite_compose HasSnaky 6 childrenC_595_i1 childrenD_595_i1 finite_children_work_595_i1 (6, 3)
    required_595_i1 envelope_595_i1 pivot_mem_595_i1 child_required_sub_595_i1 child_envelope_sub_595_i1 ?_
  intro b hb
  exact common_sub_595_i1 (mem_commonEnvelope childrenD_595_i1 b hb)

theorem finite_children_work_595_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_595_i0 j) (childrenD_595_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_595_i1.mono (by decide +kernel)

theorem finite_row_works_595_i0 : FiniteTemplate HasSnaky 8 required_595_i0 envelope_595_i0 := by
  refine finite_compose HasSnaky 7 childrenC_595_i0 childrenD_595_i0 finite_children_work_595_i0 (6, 4)
    required_595_i0 envelope_595_i0 pivot_mem_595_i0 child_required_sub_595_i0 child_envelope_sub_595_i0 ?_
  intro b hb
  exact common_sub_595_i0 (mem_commonEnvelope childrenD_595_i0 b hb)

theorem finite_children_work_595 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_595 j) (childrenD_595 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_595_i0.mono (by decide +kernel)

theorem finite_row_works_595 : FiniteTemplate HasSnaky 9 required_595 envelope_595 := by
  refine finite_compose HasSnaky 8 childrenC_595 childrenD_595 finite_children_work_595 (6, 5)
    required_595 envelope_595 pivot_mem_595 child_required_sub_595 child_envelope_sub_595 ?_
  intro b hb
  exact common_sub_595 (mem_commonEnvelope childrenD_595 b hb)

theorem finite_children_work_614_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_614_i1 j) (childrenD_614_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_425 4 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_614_i1 : FiniteTemplate HasSnaky 6 required_614_i1 envelope_614_i1 := by
  refine finite_compose HasSnaky 5 childrenC_614_i1 childrenD_614_i1 finite_children_work_614_i1 (2, 4)
    required_614_i1 envelope_614_i1 pivot_mem_614_i1 child_required_sub_614_i1 child_envelope_sub_614_i1 ?_
  intro b hb
  exact common_sub_614_i1 (mem_commonEnvelope childrenD_614_i1 b hb)

theorem finite_children_work_614_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_614_i2 j) (childrenD_614_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_68 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_495 4 (3, 8)).mono (by decide +kernel)

theorem finite_row_works_614_i2 : FiniteTemplate HasSnaky 6 required_614_i2 envelope_614_i2 := by
  refine finite_compose HasSnaky 5 childrenC_614_i2 childrenD_614_i2 finite_children_work_614_i2 (4, 3)
    required_614_i2 envelope_614_i2 pivot_mem_614_i2 child_required_sub_614_i2 child_envelope_sub_614_i2 ?_
  intro b hb
  exact common_sub_614_i2 (mem_commonEnvelope childrenD_614_i2 b hb)

theorem finite_children_work_614_i4 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_614_i4 j) (childrenD_614_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_66 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_66 0 (3, 2)).mono (by decide +kernel)

theorem finite_row_works_614_i4 : FiniteTemplate HasSnaky 3 required_614_i4 envelope_614_i4 := by
  refine finite_compose HasSnaky 2 childrenC_614_i4 childrenD_614_i4 finite_children_work_614_i4 (4, 4)
    required_614_i4 envelope_614_i4 pivot_mem_614_i4 child_required_sub_614_i4 child_envelope_sub_614_i4 ?_
  intro b hb
  exact common_sub_614_i4 (mem_commonEnvelope childrenD_614_i4 b hb)

theorem finite_children_work_614_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_614_i3 j) (childrenD_614_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_68 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_614_i4.mono (by decide +kernel)

theorem finite_row_works_614_i3 : FiniteTemplate HasSnaky 4 required_614_i3 envelope_614_i3 := by
  refine finite_compose HasSnaky 3 childrenC_614_i3 childrenD_614_i3 finite_children_work_614_i3 (4, 3)
    required_614_i3 envelope_614_i3 pivot_mem_614_i3 child_required_sub_614_i3 child_envelope_sub_614_i3 ?_
  intro b hb
  exact common_sub_614_i3 (mem_commonEnvelope childrenD_614_i3 b hb)

theorem finite_children_work_614_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_614_i5 j) (childrenD_614_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_68 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 4 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_614_i5 : FiniteTemplate HasSnaky 6 required_614_i5 envelope_614_i5 := by
  refine finite_compose HasSnaky 5 childrenC_614_i5 childrenD_614_i5 finite_children_work_614_i5 (4, 3)
    required_614_i5 envelope_614_i5 pivot_mem_614_i5 child_required_sub_614_i5 child_envelope_sub_614_i5 ?_
  intro b hb
  exact common_sub_614_i5 (mem_commonEnvelope childrenD_614_i5 b hb)

theorem finite_children_work_614_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_614_i0 j) (childrenD_614_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_276 4 (3, 8)).mono (by decide +kernel)
  · exact finite_row_works_614_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_611 4 (3, 9)).mono (by decide +kernel)
  · exact finite_row_works_614_i2.mono (by decide +kernel)
  · exact finite_row_works_614_i3.mono (by decide +kernel)
  · exact finite_row_works_614_i5.mono (by decide +kernel)

theorem finite_row_works_614_i0 : FiniteTemplate HasSnaky 8 required_614_i0 envelope_614_i0 := by
  refine finite_compose HasSnaky 7 childrenC_614_i0 childrenD_614_i0 finite_children_work_614_i0 (5, 3)
    required_614_i0 envelope_614_i0 pivot_mem_614_i0 child_required_sub_614_i0 child_envelope_sub_614_i0 ?_
  intro b hb
  exact common_sub_614_i0 (mem_commonEnvelope childrenD_614_i0 b hb)

theorem finite_children_work_614 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_614 j) (childrenD_614 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_68 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_614_i0.mono (by decide +kernel)

theorem finite_row_works_614 : FiniteTemplate HasSnaky 9 required_614 envelope_614 := by
  refine finite_compose HasSnaky 8 childrenC_614 childrenD_614 finite_children_work_614 (5, 5)
    required_614 envelope_614 pivot_mem_614 child_required_sub_614 child_envelope_sub_614 ?_
  intro b hb
  exact common_sub_614 (mem_commonEnvelope childrenD_614 b hb)

end FiniteCongruenceChecks.SnakyFinite
