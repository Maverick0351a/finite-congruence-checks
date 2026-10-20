/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part06
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part06
import FiniteCards.Height10Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_596_i1 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_596_i1 j) (childrenD_596_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 0 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_596_i1 : FiniteTemplate HasSnaky 2 required_596_i1 envelope_596_i1 := by
  refine finite_compose HasSnaky 1 childrenC_596_i1 childrenD_596_i1 finite_children_work_596_i1 (4, 5)
    required_596_i1 envelope_596_i1 pivot_mem_596_i1 child_required_sub_596_i1 child_envelope_sub_596_i1 ?_
  intro b hb
  exact common_sub_596_i1 (mem_commonEnvelope childrenD_596_i1 b hb)

theorem finite_children_work_596_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_596_i0 j) (childrenD_596_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_596_i1.mono (by decide +kernel)

theorem finite_row_works_596_i0 : FiniteTemplate HasSnaky 3 required_596_i0 envelope_596_i0 := by
  refine finite_compose HasSnaky 2 childrenC_596_i0 childrenD_596_i0 finite_children_work_596_i0 (4, 2)
    required_596_i0 envelope_596_i0 pivot_mem_596_i0 child_required_sub_596_i0 child_envelope_sub_596_i0 ?_
  intro b hb
  exact common_sub_596_i0 (mem_commonEnvelope childrenD_596_i0 b hb)

theorem finite_children_work_596_i3 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_596_i3 j) (childrenD_596_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_596_i3 : FiniteTemplate HasSnaky 2 required_596_i3 envelope_596_i3 := by
  refine finite_compose HasSnaky 1 childrenC_596_i3 childrenD_596_i3 finite_children_work_596_i3 (4, 3)
    required_596_i3 envelope_596_i3 pivot_mem_596_i3 child_required_sub_596_i3 child_envelope_sub_596_i3 ?_
  intro b hb
  exact common_sub_596_i3 (mem_commonEnvelope childrenD_596_i3 b hb)

theorem finite_children_work_596_i2 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_596_i2 j) (childrenD_596_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_596_i3.mono (by decide +kernel)

theorem finite_row_works_596_i2 : FiniteTemplate HasSnaky 3 required_596_i2 envelope_596_i2 := by
  refine finite_compose HasSnaky 2 childrenC_596_i2 childrenD_596_i2 finite_children_work_596_i2 (4, 2)
    required_596_i2 envelope_596_i2 pivot_mem_596_i2 child_required_sub_596_i2 child_envelope_sub_596_i2 ?_
  intro b hb
  exact common_sub_596_i2 (mem_commonEnvelope childrenD_596_i2 b hb)

theorem finite_children_work_596_i5 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_596_i5 j) (childrenD_596_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_82 1 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_596_i5 : FiniteTemplate HasSnaky 5 required_596_i5 envelope_596_i5 := by
  refine finite_compose HasSnaky 4 childrenC_596_i5 childrenD_596_i5 finite_children_work_596_i5 (4, 2)
    required_596_i5 envelope_596_i5 pivot_mem_596_i5 child_required_sub_596_i5 child_envelope_sub_596_i5 ?_
  intro b hb
  exact common_sub_596_i5 (mem_commonEnvelope childrenD_596_i5 b hb)

theorem finite_children_work_596_i4 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_596_i4 j) (childrenD_596_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_595.mono (by decide +kernel)
  · exact finite_row_works_596_i5.mono (by decide +kernel)

theorem finite_row_works_596_i4 : FiniteTemplate HasSnaky 10 required_596_i4 envelope_596_i4 := by
  refine finite_compose HasSnaky 9 childrenC_596_i4 childrenD_596_i4 finite_children_work_596_i4 (5, 4)
    required_596_i4 envelope_596_i4 pivot_mem_596_i4 child_required_sub_596_i4 child_envelope_sub_596_i4 ?_
  intro b hb
  exact common_sub_596_i4 (mem_commonEnvelope childrenD_596_i4 b hb)

theorem finite_children_work_596 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_596 j) (childrenD_596 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_197 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_596_i0.mono (by decide +kernel)
  · exact finite_row_works_596_i2.mono (by decide +kernel)
  · exact finite_row_works_596_i4.mono (by decide +kernel)

theorem finite_row_works_596 : FiniteTemplate HasSnaky 11 required_596 envelope_596 := by
  refine finite_compose HasSnaky 10 childrenC_596 childrenD_596 finite_children_work_596 (4, 4)
    required_596 envelope_596 pivot_mem_596 child_required_sub_596 child_envelope_sub_596 ?_
  intro b hb
  exact common_sub_596 (mem_commonEnvelope childrenD_596 b hb)

theorem finite_children_work_601_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_601_i1 j) (childrenD_601_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_29 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 7 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_601_i1 : FiniteTemplate HasSnaky 4 required_601_i1 envelope_601_i1 := by
  refine finite_compose HasSnaky 3 childrenC_601_i1 childrenD_601_i1 finite_children_work_601_i1 (3, 5)
    required_601_i1 envelope_601_i1 pivot_mem_601_i1 child_required_sub_601_i1 child_envelope_sub_601_i1 ?_
  intro b hb
  exact common_sub_601_i1 (mem_commonEnvelope childrenD_601_i1 b hb)

theorem finite_children_work_601_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_601_i0 j) (childrenD_601_i0 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_601_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_499 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_501 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_601_i0 : FiniteTemplate HasSnaky 8 required_601_i0 envelope_601_i0 := by
  refine finite_compose HasSnaky 7 childrenC_601_i0 childrenD_601_i0 finite_children_work_601_i0 (4, 4)
    required_601_i0 envelope_601_i0 pivot_mem_601_i0 child_required_sub_601_i0 child_envelope_sub_601_i0 ?_
  intro b hb
  exact common_sub_601_i0 (mem_commonEnvelope childrenD_601_i0 b hb)

theorem finite_children_work_601_i6 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_601_i6 j) (childrenD_601_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_66 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_94 1 (3, 2)).mono (by decide +kernel)

theorem finite_row_works_601_i6 : FiniteTemplate HasSnaky 3 required_601_i6 envelope_601_i6 := by
  refine finite_compose HasSnaky 2 childrenC_601_i6 childrenD_601_i6 finite_children_work_601_i6 (5, 2)
    required_601_i6 envelope_601_i6 pivot_mem_601_i6 child_required_sub_601_i6 child_envelope_sub_601_i6 ?_
  intro b hb
  exact common_sub_601_i6 (mem_commonEnvelope childrenD_601_i6 b hb)

theorem finite_children_work_601_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_601_i5 j) (childrenD_601_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 4 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_601_i6.mono (by decide +kernel)

theorem finite_row_works_601_i5 : FiniteTemplate HasSnaky 4 required_601_i5 envelope_601_i5 := by
  refine finite_compose HasSnaky 3 childrenC_601_i5 childrenD_601_i5 finite_children_work_601_i5 (4, 2)
    required_601_i5 envelope_601_i5 pivot_mem_601_i5 child_required_sub_601_i5 child_envelope_sub_601_i5 ?_
  intro b hb
  exact common_sub_601_i5 (mem_commonEnvelope childrenD_601_i5 b hb)

theorem finite_children_work_601_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_601_i4 j) (childrenD_601_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 2 (6, 3)).mono (by decide +kernel)
  · exact finite_row_works_601_i5.mono (by decide +kernel)

theorem finite_row_works_601_i4 : FiniteTemplate HasSnaky 5 required_601_i4 envelope_601_i4 := by
  refine finite_compose HasSnaky 4 childrenC_601_i4 childrenD_601_i4 finite_children_work_601_i4 (6, 3)
    required_601_i4 envelope_601_i4 pivot_mem_601_i4 child_required_sub_601_i4 child_envelope_sub_601_i4 ?_
  intro b hb
  exact common_sub_601_i4 (mem_commonEnvelope childrenD_601_i4 b hb)

theorem finite_children_work_601_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_601_i3 j) (childrenD_601_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (4, 4)).mono (by decide +kernel)
  · exact finite_row_works_601_i4.mono (by decide +kernel)

theorem finite_row_works_601_i3 : FiniteTemplate HasSnaky 6 required_601_i3 envelope_601_i3 := by
  refine finite_compose HasSnaky 5 childrenC_601_i3 childrenD_601_i3 finite_children_work_601_i3 (2, 4)
    required_601_i3 envelope_601_i3 pivot_mem_601_i3 child_required_sub_601_i3 child_envelope_sub_601_i3 ?_
  intro b hb
  exact common_sub_601_i3 (mem_commonEnvelope childrenD_601_i3 b hb)

theorem finite_children_work_601_i7 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_601_i7 j) (childrenD_601_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 2 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_72 0 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_601_i7 : FiniteTemplate HasSnaky 6 required_601_i7 envelope_601_i7 := by
  refine finite_compose HasSnaky 5 childrenC_601_i7 childrenD_601_i7 finite_children_work_601_i7 (2, 4)
    required_601_i7 envelope_601_i7 pivot_mem_601_i7 child_required_sub_601_i7 child_envelope_sub_601_i7 ?_
  intro b hb
  exact common_sub_601_i7 (mem_commonEnvelope childrenD_601_i7 b hb)

theorem finite_children_work_601_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_601_i2 j) (childrenD_601_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_406 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_499 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_601_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_600 4 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_601_i7.mono (by decide +kernel)

theorem finite_row_works_601_i2 : FiniteTemplate HasSnaky 10 required_601_i2 envelope_601_i2 := by
  refine finite_compose HasSnaky 9 childrenC_601_i2 childrenD_601_i2 finite_children_work_601_i2 (4, 4)
    required_601_i2 envelope_601_i2 pivot_mem_601_i2 child_required_sub_601_i2 child_envelope_sub_601_i2 ?_
  intro b hb
  exact common_sub_601_i2 (mem_commonEnvelope childrenD_601_i2 b hb)

theorem finite_children_work_601_i8 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_601_i8 j) (childrenD_601_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_406 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_501 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_601_i8 : FiniteTemplate HasSnaky 10 required_601_i8 envelope_601_i8 := by
  refine finite_compose HasSnaky 9 childrenC_601_i8 childrenD_601_i8 finite_children_work_601_i8 (4, 4)
    required_601_i8 envelope_601_i8 pivot_mem_601_i8 child_required_sub_601_i8 child_envelope_sub_601_i8 ?_
  intro b hb
  exact common_sub_601_i8 (mem_commonEnvelope childrenD_601_i8 b hb)

theorem finite_children_work_601 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_601 j) (childrenD_601 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_247 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_601_i0.mono (by decide +kernel)
  · exact finite_row_works_601_i2.mono (by decide +kernel)
  · exact finite_row_works_601_i8.mono (by decide +kernel)

theorem finite_row_works_601 : FiniteTemplate HasSnaky 11 required_601 envelope_601 := by
  refine finite_compose HasSnaky 10 childrenC_601 childrenD_601 finite_children_work_601 (4, 3)
    required_601 envelope_601 pivot_mem_601 child_required_sub_601 child_envelope_sub_601 ?_
  intro b hb
  exact common_sub_601 (mem_commonEnvelope childrenD_601 b hb)

theorem finite_children_work_613 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_613 j) (childrenD_613 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_104 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_329 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_409 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_613 : FiniteTemplate HasSnaky 11 required_613 envelope_613 := by
  refine finite_compose HasSnaky 10 childrenC_613 childrenD_613 finite_children_work_613 (2, 5)
    required_613 envelope_613 pivot_mem_613 child_required_sub_613 child_envelope_sub_613 ?_
  intro b hb
  exact common_sub_613 (mem_commonEnvelope childrenD_613 b hb)

end FiniteCongruenceChecks.SnakyFinite
