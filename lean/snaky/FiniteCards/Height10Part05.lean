/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part03
import FiniteCards.Height06Part03
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part04
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_594_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_594_i0 j) (childrenD_594_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_91 0 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_594_i0 : FiniteTemplate HasSnaky 5 required_594_i0 envelope_594_i0 := by
  refine finite_compose HasSnaky 4 childrenC_594_i0 childrenD_594_i0 finite_children_work_594_i0 (5, 5)
    required_594_i0 envelope_594_i0 pivot_mem_594_i0 child_required_sub_594_i0 child_envelope_sub_594_i0 ?_
  intro b hb
  exact common_sub_594_i0 (mem_commonEnvelope childrenD_594_i0 b hb)

theorem finite_children_work_594_i7 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_594_i7 j) (childrenD_594_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 4 (5, 5)).mono (by decide +kernel)

theorem finite_row_works_594_i7 : FiniteTemplate HasSnaky 3 required_594_i7 envelope_594_i7 := by
  refine finite_compose HasSnaky 2 childrenC_594_i7 childrenD_594_i7 finite_children_work_594_i7 (5, 2)
    required_594_i7 envelope_594_i7 pivot_mem_594_i7 child_required_sub_594_i7 child_envelope_sub_594_i7 ?_
  intro b hb
  exact common_sub_594_i7 (mem_commonEnvelope childrenD_594_i7 b hb)

theorem finite_children_work_594_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_594_i6 j) (childrenD_594_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_594_i7.mono (by decide +kernel)

theorem finite_row_works_594_i6 : FiniteTemplate HasSnaky 4 required_594_i6 envelope_594_i6 := by
  refine finite_compose HasSnaky 3 childrenC_594_i6 childrenD_594_i6 finite_children_work_594_i6 (5, 5)
    required_594_i6 envelope_594_i6 pivot_mem_594_i6 child_required_sub_594_i6 child_envelope_sub_594_i6 ?_
  intro b hb
  exact common_sub_594_i6 (mem_commonEnvelope childrenD_594_i6 b hb)

theorem finite_children_work_594_i5 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_594_i5 j) (childrenD_594_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_375 3 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_594_i6.mono (by decide +kernel)

theorem finite_row_works_594_i5 : FiniteTemplate HasSnaky 5 required_594_i5 envelope_594_i5 := by
  refine finite_compose HasSnaky 4 childrenC_594_i5 childrenD_594_i5 finite_children_work_594_i5 (5, 1)
    required_594_i5 envelope_594_i5 pivot_mem_594_i5 child_required_sub_594_i5 child_envelope_sub_594_i5 ?_
  intro b hb
  exact common_sub_594_i5 (mem_commonEnvelope childrenD_594_i5 b hb)

theorem finite_children_work_594_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_594_i4 j) (childrenD_594_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_594_i5.mono (by decide +kernel)

theorem finite_row_works_594_i4 : FiniteTemplate HasSnaky 6 required_594_i4 envelope_594_i4 := by
  refine finite_compose HasSnaky 5 childrenC_594_i4 childrenD_594_i4 finite_children_work_594_i4 (1, 2)
    required_594_i4 envelope_594_i4 pivot_mem_594_i4 child_required_sub_594_i4 child_envelope_sub_594_i4 ?_
  intro b hb
  exact common_sub_594_i4 (mem_commonEnvelope childrenD_594_i4 b hb)

theorem finite_children_work_594_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_594_i3 j) (childrenD_594_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_208 1 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_594_i4.mono (by decide +kernel)

theorem finite_row_works_594_i3 : FiniteTemplate HasSnaky 7 required_594_i3 envelope_594_i3 := by
  refine finite_compose HasSnaky 6 childrenC_594_i3 childrenD_594_i3 finite_children_work_594_i3 (2, 5)
    required_594_i3 envelope_594_i3 pivot_mem_594_i3 child_required_sub_594_i3 child_envelope_sub_594_i3 ?_
  intro b hb
  exact common_sub_594_i3 (mem_commonEnvelope childrenD_594_i3 b hb)

theorem finite_children_work_594_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_594_i2 j) (childrenD_594_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_594_i3.mono (by decide +kernel)

theorem finite_row_works_594_i2 : FiniteTemplate HasSnaky 8 required_594_i2 envelope_594_i2 := by
  refine finite_compose HasSnaky 7 childrenC_594_i2 childrenD_594_i2 finite_children_work_594_i2 (2, 3)
    required_594_i2 envelope_594_i2 pivot_mem_594_i2 child_required_sub_594_i2 child_envelope_sub_594_i2 ?_
  intro b hb
  exact common_sub_594_i2 (mem_commonEnvelope childrenD_594_i2 b hb)

theorem finite_children_work_594_i8 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_594_i8 j) (childrenD_594_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_268 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_594_i8 : FiniteTemplate HasSnaky 5 required_594_i8 envelope_594_i8 := by
  refine finite_compose HasSnaky 4 childrenC_594_i8 childrenD_594_i8 finite_children_work_594_i8 (2, 3)
    required_594_i8 envelope_594_i8 pivot_mem_594_i8 child_required_sub_594_i8 child_envelope_sub_594_i8 ?_
  intro b hb
  exact common_sub_594_i8 (mem_commonEnvelope childrenD_594_i8 b hb)

theorem finite_children_work_594_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_594_i1 j) (childrenD_594_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_272 5 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_290 7 (6, 7)).mono (by decide +kernel)
  · exact finite_row_works_594_i2.mono (by decide +kernel)
  · exact finite_row_works_594_i8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_593 5 (7, 3)).mono (by decide +kernel)

theorem finite_row_works_594_i1 : FiniteTemplate HasSnaky 9 required_594_i1 envelope_594_i1 := by
  refine finite_compose HasSnaky 8 childrenC_594_i1 childrenD_594_i1 finite_children_work_594_i1 (2, 6)
    required_594_i1 envelope_594_i1 pivot_mem_594_i1 child_required_sub_594_i1 child_envelope_sub_594_i1 ?_
  intro b hb
  exact common_sub_594_i1 (mem_commonEnvelope childrenD_594_i1 b hb)

theorem finite_children_work_594 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_594 j) (childrenD_594 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 7 (8, 4)).mono (by decide +kernel)
  · exact finite_row_works_594_i0.mono (by decide +kernel)
  · exact finite_row_works_594_i1.mono (by decide +kernel)

theorem finite_row_works_594 : FiniteTemplate HasSnaky 10 required_594 envelope_594 := by
  refine finite_compose HasSnaky 9 childrenC_594 childrenD_594 finite_children_work_594 (6, 4)
    required_594 envelope_594 pivot_mem_594 child_required_sub_594 child_envelope_sub_594 ?_
  intro b hb
  exact common_sub_594 (mem_commonEnvelope childrenD_594 b hb)

theorem finite_children_work_608_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_608_i1 j) (childrenD_608_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_375 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_608_i1 : FiniteTemplate HasSnaky 5 required_608_i1 envelope_608_i1 := by
  refine finite_compose HasSnaky 4 childrenC_608_i1 childrenD_608_i1 finite_children_work_608_i1 (5, 3)
    required_608_i1 envelope_608_i1 pivot_mem_608_i1 child_required_sub_608_i1 child_envelope_sub_608_i1 ?_
  intro b hb
  exact common_sub_608_i1 (mem_commonEnvelope childrenD_608_i1 b hb)

theorem finite_children_work_608_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_608_i2 j) (childrenD_608_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 7 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_42 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_608_i2 : FiniteTemplate HasSnaky 5 required_608_i2 envelope_608_i2 := by
  refine finite_compose HasSnaky 4 childrenC_608_i2 childrenD_608_i2 finite_children_work_608_i2 (2, 5)
    required_608_i2 envelope_608_i2 pivot_mem_608_i2 child_required_sub_608_i2 child_envelope_sub_608_i2 ?_
  intro b hb
  exact common_sub_608_i2 (mem_commonEnvelope childrenD_608_i2 b hb)

theorem finite_children_work_608_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_608_i3 j) (childrenD_608_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_42 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_608_i3 : FiniteTemplate HasSnaky 5 required_608_i3 envelope_608_i3 := by
  refine finite_compose HasSnaky 4 childrenC_608_i3 childrenD_608_i3 finite_children_work_608_i3 (2, 5)
    required_608_i3 envelope_608_i3 pivot_mem_608_i3 child_required_sub_608_i3 child_envelope_sub_608_i3 ?_
  intro b hb
  exact common_sub_608_i3 (mem_commonEnvelope childrenD_608_i3 b hb)

theorem finite_children_work_608_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_608_i0 j) (childrenD_608_i0 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_608_i1.mono (by decide +kernel)
  · exact finite_row_works_608_i2.mono (by decide +kernel)
  · exact finite_row_works_608_i3.mono (by decide +kernel)

theorem finite_row_works_608_i0 : FiniteTemplate HasSnaky 6 required_608_i0 envelope_608_i0 := by
  refine finite_compose HasSnaky 5 childrenC_608_i0 childrenD_608_i0 finite_children_work_608_i0 (1, 2)
    required_608_i0 envelope_608_i0 pivot_mem_608_i0 child_required_sub_608_i0 child_envelope_sub_608_i0 ?_
  intro b hb
  exact common_sub_608_i0 (mem_commonEnvelope childrenD_608_i0 b hb)

theorem finite_children_work_608 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_608 j) (childrenD_608 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_355 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_364 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_434 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_608_i0.mono (by decide +kernel)

theorem finite_row_works_608 : FiniteTemplate HasSnaky 10 required_608 envelope_608 := by
  refine finite_compose HasSnaky 9 childrenC_608 childrenD_608 finite_children_work_608 (4, 6)
    required_608 envelope_608 pivot_mem_608 child_required_sub_608 child_envelope_sub_608 ?_
  intro b hb
  exact common_sub_608 (mem_commonEnvelope childrenD_608 b hb)

theorem finite_children_work_616_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_616_i1 j) (childrenD_616_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_123 5 (3, 3)).mono (by decide +kernel)

theorem finite_row_works_616_i1 : FiniteTemplate HasSnaky 3 required_616_i1 envelope_616_i1 := by
  refine finite_compose HasSnaky 2 childrenC_616_i1 childrenD_616_i1 finite_children_work_616_i1 (2, 6)
    required_616_i1 envelope_616_i1 pivot_mem_616_i1 child_required_sub_616_i1 child_envelope_sub_616_i1 ?_
  intro b hb
  exact common_sub_616_i1 (mem_commonEnvelope childrenD_616_i1 b hb)

theorem finite_children_work_616_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_616_i0 j) (childrenD_616_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_616_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_521 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_616_i0 : FiniteTemplate HasSnaky 7 required_616_i0 envelope_616_i0 := by
  refine finite_compose HasSnaky 6 childrenC_616_i0 childrenD_616_i0 finite_children_work_616_i0 (2, 5)
    required_616_i0 envelope_616_i0 pivot_mem_616_i0 child_required_sub_616_i0 child_envelope_sub_616_i0 ?_
  intro b hb
  exact common_sub_616_i0 (mem_commonEnvelope childrenD_616_i0 b hb)

theorem finite_children_work_616 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_616 j) (childrenD_616 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_345 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_421 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_522 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_530 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_533 4 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_534.mono (by decide +kernel)
  · exact finite_row_works_616_i0.mono (by decide +kernel)

theorem finite_row_works_616 : FiniteTemplate HasSnaky 10 required_616 envelope_616 := by
  refine finite_compose HasSnaky 9 childrenC_616 childrenD_616 finite_children_work_616 (3, 3)
    required_616 envelope_616 pivot_mem_616 child_required_sub_616 child_envelope_sub_616 ?_
  intro b hb
  exact common_sub_616 (mem_commonEnvelope childrenD_616 b hb)

theorem finite_children_work_631_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_631_i1 j) (childrenD_631_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_45 7 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_418 1 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_631_i1 : FiniteTemplate HasSnaky 8 required_631_i1 envelope_631_i1 := by
  refine finite_compose HasSnaky 7 childrenC_631_i1 childrenD_631_i1 finite_children_work_631_i1 (3, 2)
    required_631_i1 envelope_631_i1 pivot_mem_631_i1 child_required_sub_631_i1 child_envelope_sub_631_i1 ?_
  intro b hb
  exact common_sub_631_i1 (mem_commonEnvelope childrenD_631_i1 b hb)

theorem finite_children_work_631_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_631_i0 j) (childrenD_631_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_43 4 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_51 4 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_631_i1.mono (by decide +kernel)

theorem finite_row_works_631_i0 : FiniteTemplate HasSnaky 9 required_631_i0 envelope_631_i0 := by
  refine finite_compose HasSnaky 8 childrenC_631_i0 childrenD_631_i0 finite_children_work_631_i0 (4, 2)
    required_631_i0 envelope_631_i0 pivot_mem_631_i0 child_required_sub_631_i0 child_envelope_sub_631_i0 ?_
  intro b hb
  exact common_sub_631_i0 (mem_commonEnvelope childrenD_631_i0 b hb)

theorem finite_children_work_631 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_631 j) (childrenD_631 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_631_i0.mono (by decide +kernel)

theorem finite_row_works_631 : FiniteTemplate HasSnaky 10 required_631 envelope_631 := by
  refine finite_compose HasSnaky 9 childrenC_631 childrenD_631 finite_children_work_631 (3, 5)
    required_631 envelope_631 pivot_mem_631 child_required_sub_631 child_envelope_sub_631 ?_
  intro b hb
  exact common_sub_631 (mem_commonEnvelope childrenD_631 b hb)

end FiniteCongruenceChecks.SnakyFinite
