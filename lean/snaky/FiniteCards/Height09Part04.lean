/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height07Part02
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_539_i4 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_539_i4 j) (childrenD_539_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 4 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_539_i4 : FiniteTemplate HasSnaky 3 required_539_i4 envelope_539_i4 := by
  refine finite_compose HasSnaky 2 childrenC_539_i4 childrenD_539_i4 finite_children_work_539_i4 (3, 5)
    required_539_i4 envelope_539_i4 pivot_mem_539_i4 child_required_sub_539_i4 child_envelope_sub_539_i4 ?_
  intro b hb
  exact common_sub_539_i4 (mem_commonEnvelope childrenD_539_i4 b hb)

theorem finite_children_work_539_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_539_i3 j) (childrenD_539_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_539_i4.mono (by decide +kernel)

theorem finite_row_works_539_i3 : FiniteTemplate HasSnaky 4 required_539_i3 envelope_539_i3 := by
  refine finite_compose HasSnaky 3 childrenC_539_i3 childrenD_539_i3 finite_children_work_539_i3 (3, 4)
    required_539_i3 envelope_539_i3 pivot_mem_539_i3 child_required_sub_539_i3 child_envelope_sub_539_i3 ?_
  intro b hb
  exact common_sub_539_i3 (mem_commonEnvelope childrenD_539_i3 b hb)

theorem finite_children_work_539_i7 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_539_i7 j) (childrenD_539_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_153 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_539_i7 : FiniteTemplate HasSnaky 3 required_539_i7 envelope_539_i7 := by
  refine finite_compose HasSnaky 2 childrenC_539_i7 childrenD_539_i7 finite_children_work_539_i7 (4, 2)
    required_539_i7 envelope_539_i7 pivot_mem_539_i7 child_required_sub_539_i7 child_envelope_sub_539_i7 ?_
  intro b hb
  exact common_sub_539_i7 (mem_commonEnvelope childrenD_539_i7 b hb)

theorem finite_children_work_539_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_539_i6 j) (childrenD_539_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_539_i7.mono (by decide +kernel)

theorem finite_row_works_539_i6 : FiniteTemplate HasSnaky 4 required_539_i6 envelope_539_i6 := by
  refine finite_compose HasSnaky 3 childrenC_539_i6 childrenD_539_i6 finite_children_work_539_i6 (3, 5)
    required_539_i6 envelope_539_i6 pivot_mem_539_i6 child_required_sub_539_i6 child_envelope_sub_539_i6 ?_
  intro b hb
  exact common_sub_539_i6 (mem_commonEnvelope childrenD_539_i6 b hb)

theorem finite_children_work_539_i5 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_539_i5 j) (childrenD_539_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_539_i6.mono (by decide +kernel)

theorem finite_row_works_539_i5 : FiniteTemplate HasSnaky 5 required_539_i5 envelope_539_i5 := by
  refine finite_compose HasSnaky 4 childrenC_539_i5 childrenD_539_i5 finite_children_work_539_i5 (3, 4)
    required_539_i5 envelope_539_i5 pivot_mem_539_i5 child_required_sub_539_i5 child_envelope_sub_539_i5 ?_
  intro b hb
  exact common_sub_539_i5 (mem_commonEnvelope childrenD_539_i5 b hb)

theorem finite_children_work_539_i9 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_539_i9 j) (childrenD_539_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_2 7 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_539_i9 : FiniteTemplate HasSnaky 2 required_539_i9 envelope_539_i9 := by
  refine finite_compose HasSnaky 1 childrenC_539_i9 childrenD_539_i9 finite_children_work_539_i9 (1, 2)
    required_539_i9 envelope_539_i9 pivot_mem_539_i9 child_required_sub_539_i9 child_envelope_sub_539_i9 ?_
  intro b hb
  exact common_sub_539_i9 (mem_commonEnvelope childrenD_539_i9 b hb)

theorem finite_children_work_539_i8 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_539_i8 j) (childrenD_539_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_539_i9.mono (by decide +kernel)

theorem finite_row_works_539_i8 : FiniteTemplate HasSnaky 3 required_539_i8 envelope_539_i8 := by
  refine finite_compose HasSnaky 2 childrenC_539_i8 childrenD_539_i8 finite_children_work_539_i8 (1, 1)
    required_539_i8 envelope_539_i8 pivot_mem_539_i8 child_required_sub_539_i8 child_envelope_sub_539_i8 ?_
  intro b hb
  exact common_sub_539_i8 (mem_commonEnvelope childrenD_539_i8 b hb)

theorem finite_children_work_539_i10 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_539_i10 j) (childrenD_539_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_83 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_281 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_539_i10 : FiniteTemplate HasSnaky 3 required_539_i10 envelope_539_i10 := by
  refine finite_compose HasSnaky 2 childrenC_539_i10 childrenD_539_i10 finite_children_work_539_i10 (4, 1)
    required_539_i10 envelope_539_i10 pivot_mem_539_i10 child_required_sub_539_i10 child_envelope_sub_539_i10 ?_
  intro b hb
  exact common_sub_539_i10 (mem_commonEnvelope childrenD_539_i10 b hb)

theorem finite_children_work_539_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_539_i2 j) (childrenD_539_i2 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_539_i3.mono (by decide +kernel)
  · exact finite_row_works_539_i5.mono (by decide +kernel)
  · exact finite_row_works_539_i8.mono (by decide +kernel)
  · exact finite_row_works_539_i10.mono (by decide +kernel)

theorem finite_row_works_539_i2 : FiniteTemplate HasSnaky 6 required_539_i2 envelope_539_i2 := by
  refine finite_compose HasSnaky 5 childrenC_539_i2 childrenD_539_i2 finite_children_work_539_i2 (2, 1)
    required_539_i2 envelope_539_i2 pivot_mem_539_i2 child_required_sub_539_i2 child_envelope_sub_539_i2 ?_
  intro b hb
  exact common_sub_539_i2 (mem_commonEnvelope childrenD_539_i2 b hb)

theorem finite_children_work_539_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_539_i1 j) (childrenD_539_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 3 (1, 9)).mono (by decide +kernel)
  · exact finite_row_works_539_i2.mono (by decide +kernel)

theorem finite_row_works_539_i1 : FiniteTemplate HasSnaky 7 required_539_i1 envelope_539_i1 := by
  refine finite_compose HasSnaky 6 childrenC_539_i1 childrenD_539_i1 finite_children_work_539_i1 (2, 5)
    required_539_i1 envelope_539_i1 pivot_mem_539_i1 child_required_sub_539_i1 child_envelope_sub_539_i1 ?_
  intro b hb
  exact common_sub_539_i1 (mem_commonEnvelope childrenD_539_i1 b hb)

theorem finite_children_work_539_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_539_i0 j) (childrenD_539_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 8)).mono (by decide +kernel)
  · exact finite_row_works_539_i1.mono (by decide +kernel)

theorem finite_row_works_539_i0 : FiniteTemplate HasSnaky 8 required_539_i0 envelope_539_i0 := by
  refine finite_compose HasSnaky 7 childrenC_539_i0 childrenD_539_i0 finite_children_work_539_i0 (0, 5)
    required_539_i0 envelope_539_i0 pivot_mem_539_i0 child_required_sub_539_i0 child_envelope_sub_539_i0 ?_
  intro b hb
  exact common_sub_539_i0 (mem_commonEnvelope childrenD_539_i0 b hb)

theorem finite_children_work_539 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_539 j) (childrenD_539 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_539_i0.mono (by decide +kernel)

theorem finite_row_works_539 : FiniteTemplate HasSnaky 9 required_539 envelope_539 := by
  refine finite_compose HasSnaky 8 childrenC_539 childrenD_539 finite_children_work_539 (1, 9)
    required_539 envelope_539 pivot_mem_539 child_required_sub_539 child_envelope_sub_539 ?_
  intro b hb
  exact common_sub_539 (mem_commonEnvelope childrenD_539 b hb)

theorem finite_children_work_548 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_548 j) (childrenD_548 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_547 4 (0, 8)).mono (by decide +kernel)

theorem finite_row_works_548 : FiniteTemplate HasSnaky 9 required_548 envelope_548 := by
  refine finite_compose HasSnaky 8 childrenC_548 childrenD_548 finite_children_work_548 (1, 7)
    required_548 envelope_548 pivot_mem_548 child_required_sub_548 child_envelope_sub_548 ?_
  intro b hb
  exact common_sub_548 (mem_commonEnvelope childrenD_548 b hb)

theorem finite_children_work_549 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_549 j) (childrenD_549 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_547 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_549 : FiniteTemplate HasSnaky 9 required_549 envelope_549 := by
  refine finite_compose HasSnaky 8 childrenC_549 childrenD_549 finite_children_work_549 (1, 3)
    required_549 envelope_549 pivot_mem_549 child_required_sub_549 child_envelope_sub_549 ?_
  intro b hb
  exact common_sub_549 (mem_commonEnvelope childrenD_549 b hb)

theorem finite_children_work_561_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_561_i0 j) (childrenD_561_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 7 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_57 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_561_i0 : FiniteTemplate HasSnaky 5 required_561_i0 envelope_561_i0 := by
  refine finite_compose HasSnaky 4 childrenC_561_i0 childrenD_561_i0 finite_children_work_561_i0 (2, 4)
    required_561_i0 envelope_561_i0 pivot_mem_561_i0 child_required_sub_561_i0 child_envelope_sub_561_i0 ?_
  intro b hb
  exact common_sub_561_i0 (mem_commonEnvelope childrenD_561_i0 b hb)

theorem finite_children_work_561 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_561 j) (childrenD_561 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_154 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_319 4 (0, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_335 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_561_i0.mono (by decide +kernel)

theorem finite_row_works_561 : FiniteTemplate HasSnaky 9 required_561 envelope_561 := by
  refine finite_compose HasSnaky 8 childrenC_561 childrenD_561 finite_children_work_561 (2, 7)
    required_561 envelope_561 pivot_mem_561 child_required_sub_561 child_envelope_sub_561 ?_
  intro b hb
  exact common_sub_561 (mem_commonEnvelope childrenD_561 b hb)

theorem finite_children_work_562_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_562_i0 j) (childrenD_562_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_122 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_388 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_562_i0 : FiniteTemplate HasSnaky 8 required_562_i0 envelope_562_i0 := by
  refine finite_compose HasSnaky 7 childrenC_562_i0 childrenD_562_i0 finite_children_work_562_i0 (3, 5)
    required_562_i0 envelope_562_i0 pivot_mem_562_i0 child_required_sub_562_i0 child_envelope_sub_562_i0 ?_
  intro b hb
  exact common_sub_562_i0 (mem_commonEnvelope childrenD_562_i0 b hb)

theorem finite_children_work_562 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_562 j) (childrenD_562 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_506 6 (4, 7)).mono (by decide +kernel)
  · exact finite_row_works_562_i0.mono (by decide +kernel)

theorem finite_row_works_562 : FiniteTemplate HasSnaky 9 required_562 envelope_562 := by
  refine finite_compose HasSnaky 8 childrenC_562 childrenD_562 finite_children_work_562 (3, 3)
    required_562 envelope_562 pivot_mem_562 child_required_sub_562 child_envelope_sub_562 ?_
  intro b hb
  exact common_sub_562 (mem_commonEnvelope childrenD_562 b hb)

theorem finite_children_work_570_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_570_i0 j) (childrenD_570_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_446 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_570_i0 : FiniteTemplate HasSnaky 8 required_570_i0 envelope_570_i0 := by
  refine finite_compose HasSnaky 7 childrenC_570_i0 childrenD_570_i0 finite_children_work_570_i0 (4, 5)
    required_570_i0 envelope_570_i0 pivot_mem_570_i0 child_required_sub_570_i0 child_envelope_sub_570_i0 ?_
  intro b hb
  exact common_sub_570_i0 (mem_commonEnvelope childrenD_570_i0 b hb)

theorem finite_children_work_570_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_570_i2 j) (childrenD_570_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_331 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_570_i2 : FiniteTemplate HasSnaky 7 required_570_i2 envelope_570_i2 := by
  refine finite_compose HasSnaky 6 childrenC_570_i2 childrenD_570_i2 finite_children_work_570_i2 (5, 3)
    required_570_i2 envelope_570_i2 pivot_mem_570_i2 child_required_sub_570_i2 child_envelope_sub_570_i2 ?_
  intro b hb
  exact common_sub_570_i2 (mem_commonEnvelope childrenD_570_i2 b hb)

theorem finite_children_work_570_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_570_i1 j) (childrenD_570_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_570_i2.mono (by decide +kernel)

theorem finite_row_works_570_i1 : FiniteTemplate HasSnaky 8 required_570_i1 envelope_570_i1 := by
  refine finite_compose HasSnaky 7 childrenC_570_i1 childrenD_570_i1 finite_children_work_570_i1 (2, 3)
    required_570_i1 envelope_570_i1 pivot_mem_570_i1 child_required_sub_570_i1 child_envelope_sub_570_i1 ?_
  intro b hb
  exact common_sub_570_i1 (mem_commonEnvelope childrenD_570_i1 b hb)

theorem finite_children_work_570 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_570 j) (childrenD_570 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_150 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_283 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_570_i0.mono (by decide +kernel)
  · exact finite_row_works_570_i1.mono (by decide +kernel)

theorem finite_row_works_570 : FiniteTemplate HasSnaky 9 required_570 envelope_570 := by
  refine finite_compose HasSnaky 8 childrenC_570 childrenD_570 finite_children_work_570 (4, 3)
    required_570 envelope_570 pivot_mem_570 child_required_sub_570 child_envelope_sub_570 ?_
  intro b hb
  exact common_sub_570 (mem_commonEnvelope childrenD_570 b hb)

end FiniteCongruenceChecks.SnakyFinite
