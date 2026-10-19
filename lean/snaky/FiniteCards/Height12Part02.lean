/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part02
import FiniteCards.Height07Part02
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height09Part02
import FiniteCards.Height09Part04
import FiniteCards.Height10Part04
import FiniteCards.Height11Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_551_i7 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_551_i7 j) (childrenD_551_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 7 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_551_i7 : FiniteTemplate HasSnaky 4 required_551_i7 envelope_551_i7 := by
  refine finite_compose HasSnaky 3 childrenC_551_i7 childrenD_551_i7 finite_children_work_551_i7 (3, 3)
    required_551_i7 envelope_551_i7 pivot_mem_551_i7 child_required_sub_551_i7 child_envelope_sub_551_i7 ?_
  intro b hb
  exact common_sub_551_i7 (mem_commonEnvelope childrenD_551_i7 b hb)

theorem finite_children_work_551_i8 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_551_i8 j) (childrenD_551_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 7 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_551_i8 : FiniteTemplate HasSnaky 3 required_551_i8 envelope_551_i8 := by
  refine finite_compose HasSnaky 2 childrenC_551_i8 childrenD_551_i8 finite_children_work_551_i8 (3, 3)
    required_551_i8 envelope_551_i8 pivot_mem_551_i8 child_required_sub_551_i8 child_envelope_sub_551_i8 ?_
  intro b hb
  exact common_sub_551_i8 (mem_commonEnvelope childrenD_551_i8 b hb)

theorem finite_children_work_551_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_551_i6 j) (childrenD_551_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 2 (7, 2)).mono (by decide +kernel)
  · exact finite_row_works_551_i7.mono (by decide +kernel)
  · exact finite_row_works_551_i8.mono (by decide +kernel)

theorem finite_row_works_551_i6 : FiniteTemplate HasSnaky 5 required_551_i6 envelope_551_i6 := by
  refine finite_compose HasSnaky 4 childrenC_551_i6 childrenD_551_i6 finite_children_work_551_i6 (4, 3)
    required_551_i6 envelope_551_i6 pivot_mem_551_i6 child_required_sub_551_i6 child_envelope_sub_551_i6 ?_
  intro b hb
  exact common_sub_551_i6 (mem_commonEnvelope childrenD_551_i6 b hb)

theorem finite_children_work_551_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_551_i5 j) (childrenD_551_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_551_i6.mono (by decide +kernel)

theorem finite_row_works_551_i5 : FiniteTemplate HasSnaky 6 required_551_i5 envelope_551_i5 := by
  refine finite_compose HasSnaky 5 childrenC_551_i5 childrenD_551_i5 finite_children_work_551_i5 (7, 3)
    required_551_i5 envelope_551_i5 pivot_mem_551_i5 child_required_sub_551_i5 child_envelope_sub_551_i5 ?_
  intro b hb
  exact common_sub_551_i5 (mem_commonEnvelope childrenD_551_i5 b hb)

theorem finite_children_work_551_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_551_i4 j) (childrenD_551_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_551_i5.mono (by decide +kernel)

theorem finite_row_works_551_i4 : FiniteTemplate HasSnaky 7 required_551_i4 envelope_551_i4 := by
  refine finite_compose HasSnaky 6 childrenC_551_i4 childrenD_551_i4 finite_children_work_551_i4 (5, 3)
    required_551_i4 envelope_551_i4 pivot_mem_551_i4 child_required_sub_551_i4 child_envelope_sub_551_i4 ?_
  intro b hb
  exact common_sub_551_i4 (mem_commonEnvelope childrenD_551_i4 b hb)

theorem finite_children_work_551_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_551_i3 j) (childrenD_551_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_551_i4.mono (by decide +kernel)

theorem finite_row_works_551_i3 : FiniteTemplate HasSnaky 8 required_551_i3 envelope_551_i3 := by
  refine finite_compose HasSnaky 7 childrenC_551_i3 childrenD_551_i3 finite_children_work_551_i3 (2, 5)
    required_551_i3 envelope_551_i3 pivot_mem_551_i3 child_required_sub_551_i3 child_envelope_sub_551_i3 ?_
  intro b hb
  exact common_sub_551_i3 (mem_commonEnvelope childrenD_551_i3 b hb)

theorem finite_children_work_551_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_551_i2 j) (childrenD_551_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (6, 3)).mono (by decide +kernel)
  · exact finite_row_works_551_i3.mono (by decide +kernel)

theorem finite_row_works_551_i2 : FiniteTemplate HasSnaky 9 required_551_i2 envelope_551_i2 := by
  refine finite_compose HasSnaky 8 childrenC_551_i2 childrenD_551_i2 finite_children_work_551_i2 (5, 6)
    required_551_i2 envelope_551_i2 pivot_mem_551_i2 child_required_sub_551_i2 child_envelope_sub_551_i2 ?_
  intro b hb
  exact common_sub_551_i2 (mem_commonEnvelope childrenD_551_i2 b hb)

theorem finite_children_work_551_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_551_i1 j) (childrenD_551_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 0 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_84 0 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 1 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_551_i2.mono (by decide +kernel)

theorem finite_row_works_551_i1 : FiniteTemplate HasSnaky 10 required_551_i1 envelope_551_i1 := by
  refine finite_compose HasSnaky 9 childrenC_551_i1 childrenD_551_i1 finite_children_work_551_i1 (6, 6)
    required_551_i1 envelope_551_i1 pivot_mem_551_i1 child_required_sub_551_i1 child_envelope_sub_551_i1 ?_
  intro b hb
  exact common_sub_551_i1 (mem_commonEnvelope childrenD_551_i1 b hb)

theorem finite_children_work_551_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_551_i0 j) (childrenD_551_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 4 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 4 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_551_i1.mono (by decide +kernel)

theorem finite_row_works_551_i0 : FiniteTemplate HasSnaky 11 required_551_i0 envelope_551_i0 := by
  refine finite_compose HasSnaky 10 childrenC_551_i0 childrenD_551_i0 finite_children_work_551_i0 (6, 3)
    required_551_i0 envelope_551_i0 pivot_mem_551_i0 child_required_sub_551_i0 child_envelope_sub_551_i0 ?_
  intro b hb
  exact common_sub_551_i0 (mem_commonEnvelope childrenD_551_i0 b hb)

theorem finite_children_work_551 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_551 j) (childrenD_551 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_523 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_551_i0.mono (by decide +kernel)

theorem finite_row_works_551 : FiniteTemplate HasSnaky 12 required_551 envelope_551 := by
  refine finite_compose HasSnaky 11 childrenC_551 childrenD_551 finite_children_work_551 (6, 4)
    required_551 envelope_551 pivot_mem_551 child_required_sub_551 child_envelope_sub_551 ?_
  intro b hb
  exact common_sub_551 (mem_commonEnvelope childrenD_551 b hb)

theorem finite_children_work_571_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_571_i1 j) (childrenD_571_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_287 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_288 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_345 0 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 1 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_571_i1 : FiniteTemplate HasSnaky 10 required_571_i1 envelope_571_i1 := by
  refine finite_compose HasSnaky 9 childrenC_571_i1 childrenD_571_i1 finite_children_work_571_i1 (5, 6)
    required_571_i1 envelope_571_i1 pivot_mem_571_i1 child_required_sub_571_i1 child_envelope_sub_571_i1 ?_
  intro b hb
  exact common_sub_571_i1 (mem_commonEnvelope childrenD_571_i1 b hb)

theorem finite_children_work_571_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_571_i0 j) (childrenD_571_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 7 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_571_i1.mono (by decide +kernel)

theorem finite_row_works_571_i0 : FiniteTemplate HasSnaky 11 required_571_i0 envelope_571_i0 := by
  refine finite_compose HasSnaky 10 childrenC_571_i0 childrenD_571_i0 finite_children_work_571_i0 (4, 7)
    required_571_i0 envelope_571_i0 pivot_mem_571_i0 child_required_sub_571_i0 child_envelope_sub_571_i0 ?_
  intro b hb
  exact common_sub_571_i0 (mem_commonEnvelope childrenD_571_i0 b hb)

theorem finite_children_work_571_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_571_i3 j) (childrenD_571_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_446 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_571_i3 : FiniteTemplate HasSnaky 8 required_571_i3 envelope_571_i3 := by
  refine finite_compose HasSnaky 7 childrenC_571_i3 childrenD_571_i3 finite_children_work_571_i3 (4, 3)
    required_571_i3 envelope_571_i3 pivot_mem_571_i3 child_required_sub_571_i3 child_envelope_sub_571_i3 ?_
  intro b hb
  exact common_sub_571_i3 (mem_commonEnvelope childrenD_571_i3 b hb)

theorem finite_children_work_571_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_571_i2 j) (childrenD_571_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_571_i3.mono (by decide +kernel)

theorem finite_row_works_571_i2 : FiniteTemplate HasSnaky 9 required_571_i2 envelope_571_i2 := by
  refine finite_compose HasSnaky 8 childrenC_571_i2 childrenD_571_i2 finite_children_work_571_i2 (4, 5)
    required_571_i2 envelope_571_i2 pivot_mem_571_i2 child_required_sub_571_i2 child_envelope_sub_571_i2 ?_
  intro b hb
  exact common_sub_571_i2 (mem_commonEnvelope childrenD_571_i2 b hb)

theorem finite_children_work_571_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_571_i5 j) (childrenD_571_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_283 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_571_i5 : FiniteTemplate HasSnaky 7 required_571_i5 envelope_571_i5 := by
  refine finite_compose HasSnaky 6 childrenC_571_i5 childrenD_571_i5 finite_children_work_571_i5 (4, 3)
    required_571_i5 envelope_571_i5 pivot_mem_571_i5 child_required_sub_571_i5 child_envelope_sub_571_i5 ?_
  intro b hb
  exact common_sub_571_i5 (mem_commonEnvelope childrenD_571_i5 b hb)

theorem finite_children_work_571_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_571_i4 j) (childrenD_571_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_571_i5.mono (by decide +kernel)

theorem finite_row_works_571_i4 : FiniteTemplate HasSnaky 8 required_571_i4 envelope_571_i4 := by
  refine finite_compose HasSnaky 7 childrenC_571_i4 childrenD_571_i4 finite_children_work_571_i4 (4, 5)
    required_571_i4 envelope_571_i4 pivot_mem_571_i4 child_required_sub_571_i4 child_envelope_sub_571_i4 ?_
  intro b hb
  exact common_sub_571_i4 (mem_commonEnvelope childrenD_571_i4 b hb)

theorem finite_children_work_571_i9 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_571_i9 j) (childrenD_571_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 1 (2, 3)).mono (by decide +kernel)

theorem finite_row_works_571_i9 : FiniteTemplate HasSnaky 4 required_571_i9 envelope_571_i9 := by
  refine finite_compose HasSnaky 3 childrenC_571_i9 childrenD_571_i9 finite_children_work_571_i9 (5, 3)
    required_571_i9 envelope_571_i9 pivot_mem_571_i9 child_required_sub_571_i9 child_envelope_sub_571_i9 ?_
  intro b hb
  exact common_sub_571_i9 (mem_commonEnvelope childrenD_571_i9 b hb)

theorem finite_children_work_571_i8 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_571_i8 j) (childrenD_571_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_571_i9.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_446 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_571_i8 : FiniteTemplate HasSnaky 8 required_571_i8 envelope_571_i8 := by
  refine finite_compose HasSnaky 7 childrenC_571_i8 childrenD_571_i8 finite_children_work_571_i8 (4, 3)
    required_571_i8 envelope_571_i8 pivot_mem_571_i8 child_required_sub_571_i8 child_envelope_sub_571_i8 ?_
  intro b hb
  exact common_sub_571_i8 (mem_commonEnvelope childrenD_571_i8 b hb)

theorem finite_children_work_571_i7 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_571_i7 j) (childrenD_571_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_571_i8.mono (by decide +kernel)

theorem finite_row_works_571_i7 : FiniteTemplate HasSnaky 9 required_571_i7 envelope_571_i7 := by
  refine finite_compose HasSnaky 8 childrenC_571_i7 childrenD_571_i7 finite_children_work_571_i7 (4, 5)
    required_571_i7 envelope_571_i7 pivot_mem_571_i7 child_required_sub_571_i7 child_envelope_sub_571_i7 ?_
  intro b hb
  exact common_sub_571_i7 (mem_commonEnvelope childrenD_571_i7 b hb)

theorem finite_children_work_571_i6 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_571_i6 j) (childrenD_571_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_571_i7.mono (by decide +kernel)

theorem finite_row_works_571_i6 : FiniteTemplate HasSnaky 10 required_571_i6 envelope_571_i6 := by
  refine finite_compose HasSnaky 9 childrenC_571_i6 childrenD_571_i6 finite_children_work_571_i6 (2, 3)
    required_571_i6 envelope_571_i6 pivot_mem_571_i6 child_required_sub_571_i6 child_envelope_sub_571_i6 ?_
  intro b hb
  exact common_sub_571_i6 (mem_commonEnvelope childrenD_571_i6 b hb)

theorem finite_children_work_571 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_571 j) (childrenD_571 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_250 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_569 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_571_i0.mono (by decide +kernel)
  · exact finite_row_works_571_i2.mono (by decide +kernel)
  · exact finite_row_works_571_i4.mono (by decide +kernel)
  · exact finite_row_works_570.mono (by decide +kernel)
  · exact finite_row_works_571_i6.mono (by decide +kernel)

theorem finite_row_works_571 : FiniteTemplate HasSnaky 12 required_571 envelope_571 := by
  refine finite_compose HasSnaky 11 childrenC_571 childrenD_571 finite_children_work_571 (4, 4)
    required_571 envelope_571 pivot_mem_571 child_required_sub_571 child_envelope_sub_571 ?_
  intro b hb
  exact common_sub_571 (mem_commonEnvelope childrenD_571 b hb)

theorem finite_children_work_587 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_587 j) (childrenD_587 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 2 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 6 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_586 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_586 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_587 : FiniteTemplate HasSnaky 12 required_587 envelope_587 := by
  refine finite_compose HasSnaky 11 childrenC_587 childrenD_587 finite_children_work_587 (2, 5)
    required_587 envelope_587 pivot_mem_587 child_required_sub_587 child_envelope_sub_587 ?_
  intro b hb
  exact common_sub_587 (mem_commonEnvelope childrenD_587 b hb)

theorem finite_children_work_588 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_588 j) (childrenD_588 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_42 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_289 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_291 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_586 1 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_588 : FiniteTemplate HasSnaky 12 required_588 envelope_588 := by
  refine finite_compose HasSnaky 11 childrenC_588 childrenD_588 finite_children_work_588 (4, 3)
    required_588 envelope_588 pivot_mem_588 child_required_sub_588 child_envelope_sub_588 ?_
  intro b hb
  exact common_sub_588 (mem_commonEnvelope childrenD_588 b hb)

end FiniteCongruenceChecks.SnakyFinite
