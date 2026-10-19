/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_559_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_559_i0 j) (childrenD_559_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 1 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_559_i0 : FiniteTemplate HasSnaky 5 required_559_i0 envelope_559_i0 := by
  refine finite_compose HasSnaky 4 childrenC_559_i0 childrenD_559_i0 finite_children_work_559_i0 (4, 0)
    required_559_i0 envelope_559_i0 pivot_mem_559_i0 child_required_sub_559_i0 child_envelope_sub_559_i0 ?_
  intro b hb
  exact common_sub_559_i0 (mem_commonEnvelope childrenD_559_i0 b hb)

theorem finite_children_work_559_i6 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_559_i6 j) (childrenD_559_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_0 0 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_559_i6 : FiniteTemplate HasSnaky 2 required_559_i6 envelope_559_i6 := by
  refine finite_compose HasSnaky 1 childrenC_559_i6 childrenD_559_i6 finite_children_work_559_i6 (1, 3)
    required_559_i6 envelope_559_i6 pivot_mem_559_i6 child_required_sub_559_i6 child_envelope_sub_559_i6 ?_
  intro b hb
  exact common_sub_559_i6 (mem_commonEnvelope childrenD_559_i6 b hb)

theorem finite_children_work_559_i5 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_559_i5 j) (childrenD_559_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 6 (6, 4)).mono (by decide +kernel)
  · exact finite_row_works_559_i6.mono (by decide +kernel)

theorem finite_row_works_559_i5 : FiniteTemplate HasSnaky 3 required_559_i5 envelope_559_i5 := by
  refine finite_compose HasSnaky 2 childrenC_559_i5 childrenD_559_i5 finite_children_work_559_i5 (2, 3)
    required_559_i5 envelope_559_i5 pivot_mem_559_i5 child_required_sub_559_i5 child_envelope_sub_559_i5 ?_
  intro b hb
  exact common_sub_559_i5 (mem_commonEnvelope childrenD_559_i5 b hb)

theorem finite_children_work_559_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_559_i4 j) (childrenD_559_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_559_i5.mono (by decide +kernel)

theorem finite_row_works_559_i4 : FiniteTemplate HasSnaky 4 required_559_i4 envelope_559_i4 := by
  refine finite_compose HasSnaky 3 childrenC_559_i4 childrenD_559_i4 finite_children_work_559_i4 (4, 4)
    required_559_i4 envelope_559_i4 pivot_mem_559_i4 child_required_sub_559_i4 child_envelope_sub_559_i4 ?_
  intro b hb
  exact common_sub_559_i4 (mem_commonEnvelope childrenD_559_i4 b hb)

theorem finite_children_work_559_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_559_i3 j) (childrenD_559_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_35 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_559_i4.mono (by decide +kernel)

theorem finite_row_works_559_i3 : FiniteTemplate HasSnaky 5 required_559_i3 envelope_559_i3 := by
  refine finite_compose HasSnaky 4 childrenC_559_i3 childrenD_559_i3 finite_children_work_559_i3 (6, 4)
    required_559_i3 envelope_559_i3 pivot_mem_559_i3 child_required_sub_559_i3 child_envelope_sub_559_i3 ?_
  intro b hb
  exact common_sub_559_i3 (mem_commonEnvelope childrenD_559_i3 b hb)

theorem finite_children_work_559_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_559_i2 j) (childrenD_559_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_244 5 (6, 0)).mono (by decide +kernel)
  · exact finite_row_works_559_i3.mono (by decide +kernel)

theorem finite_row_works_559_i2 : FiniteTemplate HasSnaky 6 required_559_i2 envelope_559_i2 := by
  refine finite_compose HasSnaky 5 childrenC_559_i2 childrenD_559_i2 finite_children_work_559_i2 (5, 0)
    required_559_i2 envelope_559_i2 pivot_mem_559_i2 child_required_sub_559_i2 child_envelope_sub_559_i2 ?_
  intro b hb
  exact common_sub_559_i2 (mem_commonEnvelope childrenD_559_i2 b hb)

theorem finite_children_work_559_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_559_i1 j) (childrenD_559_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_559_i2.mono (by decide +kernel)

theorem finite_row_works_559_i1 : FiniteTemplate HasSnaky 7 required_559_i1 envelope_559_i1 := by
  refine finite_compose HasSnaky 6 childrenC_559_i1 childrenD_559_i1 finite_children_work_559_i1 (3, 4)
    required_559_i1 envelope_559_i1 pivot_mem_559_i1 child_required_sub_559_i1 child_envelope_sub_559_i1 ?_
  intro b hb
  exact common_sub_559_i1 (mem_commonEnvelope childrenD_559_i1 b hb)

theorem finite_children_work_559 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_559 j) (childrenD_559 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 4 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_236 5 (7, 0)).mono (by decide +kernel)
  · exact finite_row_works_559_i0.mono (by decide +kernel)
  · exact finite_row_works_559_i1.mono (by decide +kernel)

theorem finite_row_works_559 : FiniteTemplate HasSnaky 8 required_559 envelope_559 := by
  refine finite_compose HasSnaky 7 childrenC_559 childrenD_559 finite_children_work_559 (6, 1)
    required_559 envelope_559 pivot_mem_559 child_required_sub_559 child_envelope_sub_559 ?_
  intro b hb
  exact common_sub_559 (mem_commonEnvelope childrenD_559 b hb)

theorem finite_children_work_566 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_566 j) (childrenD_566 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_116 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_172 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_172 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_182 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_565 5 (6, 1)).mono (by decide +kernel)

theorem finite_row_works_566 : FiniteTemplate HasSnaky 8 required_566 envelope_566 := by
  refine finite_compose HasSnaky 7 childrenC_566 childrenD_566 finite_children_work_566 (3, 5)
    required_566 envelope_566 pivot_mem_566 child_required_sub_566 child_envelope_sub_566 ?_
  intro b hb
  exact common_sub_566 (mem_commonEnvelope childrenD_566 b hb)

theorem finite_children_work_604_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_604_i0 j) (childrenD_604_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_267 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_604_i0 : FiniteTemplate HasSnaky 7 required_604_i0 envelope_604_i0 := by
  refine finite_compose HasSnaky 6 childrenC_604_i0 childrenD_604_i0 finite_children_work_604_i0 (3, 4)
    required_604_i0 envelope_604_i0 pivot_mem_604_i0 child_required_sub_604_i0 child_envelope_sub_604_i0 ?_
  intro b hb
  exact common_sub_604_i0 (mem_commonEnvelope childrenD_604_i0 b hb)

theorem finite_children_work_604 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_604 j) (childrenD_604 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_604_i0.mono (by decide +kernel)

theorem finite_row_works_604 : FiniteTemplate HasSnaky 8 required_604 envelope_604 := by
  refine finite_compose HasSnaky 7 childrenC_604 childrenD_604 finite_children_work_604 (3, 2)
    required_604 envelope_604 pivot_mem_604 child_required_sub_604 child_envelope_sub_604 ?_
  intro b hb
  exact common_sub_604 (mem_commonEnvelope childrenD_604 b hb)

theorem finite_children_work_607_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_607_i0 j) (childrenD_607_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 3 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_383 5 (6, 2)).mono (by decide +kernel)

theorem finite_row_works_607_i0 : FiniteTemplate HasSnaky 6 required_607_i0 envelope_607_i0 := by
  refine finite_compose HasSnaky 5 childrenC_607_i0 childrenD_607_i0 finite_children_work_607_i0 (4, 2)
    required_607_i0 envelope_607_i0 pivot_mem_607_i0 child_required_sub_607_i0 child_envelope_sub_607_i0 ?_
  intro b hb
  exact common_sub_607_i0 (mem_commonEnvelope childrenD_607_i0 b hb)

theorem finite_children_work_607_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_607_i3 j) (childrenD_607_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_42 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_607_i3 : FiniteTemplate HasSnaky 5 required_607_i3 envelope_607_i3 := by
  refine finite_compose HasSnaky 4 childrenC_607_i3 childrenD_607_i3 finite_children_work_607_i3 (2, 5)
    required_607_i3 envelope_607_i3 pivot_mem_607_i3 child_required_sub_607_i3 child_envelope_sub_607_i3 ?_
  intro b hb
  exact common_sub_607_i3 (mem_commonEnvelope childrenD_607_i3 b hb)

theorem finite_children_work_607_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_607_i2 j) (childrenD_607_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_352 7 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_607_i3.mono (by decide +kernel)

theorem finite_row_works_607_i2 : FiniteTemplate HasSnaky 6 required_607_i2 envelope_607_i2 := by
  refine finite_compose HasSnaky 5 childrenC_607_i2 childrenD_607_i2 finite_children_work_607_i2 (1, 2)
    required_607_i2 envelope_607_i2 pivot_mem_607_i2 child_required_sub_607_i2 child_envelope_sub_607_i2 ?_
  intro b hb
  exact common_sub_607_i2 (mem_commonEnvelope childrenD_607_i2 b hb)

theorem finite_children_work_607_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_607_i1 j) (childrenD_607_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 5 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_607_i2.mono (by decide +kernel)

theorem finite_row_works_607_i1 : FiniteTemplate HasSnaky 7 required_607_i1 envelope_607_i1 := by
  refine finite_compose HasSnaky 6 childrenC_607_i1 childrenD_607_i1 finite_children_work_607_i1 (4, 6)
    required_607_i1 envelope_607_i1 pivot_mem_607_i1 child_required_sub_607_i1 child_envelope_sub_607_i1 ?_
  intro b hb
  exact common_sub_607_i1 (mem_commonEnvelope childrenD_607_i1 b hb)

theorem finite_children_work_607_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_607_i4 j) (childrenD_607_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_197 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_363 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_371 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_606 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_607_i4 : FiniteTemplate HasSnaky 7 required_607_i4 envelope_607_i4 := by
  refine finite_compose HasSnaky 6 childrenC_607_i4 childrenD_607_i4 finite_children_work_607_i4 (4, 6)
    required_607_i4 envelope_607_i4 pivot_mem_607_i4 child_required_sub_607_i4 child_envelope_sub_607_i4 ?_
  intro b hb
  exact common_sub_607_i4 (mem_commonEnvelope childrenD_607_i4 b hb)

theorem finite_children_work_607 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_607 j) (childrenD_607 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_211 4 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_607_i0.mono (by decide +kernel)
  · exact finite_row_works_607_i1.mono (by decide +kernel)
  · exact finite_row_works_607_i4.mono (by decide +kernel)

theorem finite_row_works_607 : FiniteTemplate HasSnaky 8 required_607 envelope_607 := by
  refine finite_compose HasSnaky 7 childrenC_607 childrenD_607 finite_children_work_607 (4, 3)
    required_607 envelope_607 pivot_mem_607 child_required_sub_607 child_envelope_sub_607 ?_
  intro b hb
  exact common_sub_607 (mem_commonEnvelope childrenD_607 b hb)

theorem finite_children_work_619_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_619_i0 j) (childrenD_619_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_56 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_253 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_619_i0 : FiniteTemplate HasSnaky 7 required_619_i0 envelope_619_i0 := by
  refine finite_compose HasSnaky 6 childrenC_619_i0 childrenD_619_i0 finite_children_work_619_i0 (2, 2)
    required_619_i0 envelope_619_i0 pivot_mem_619_i0 child_required_sub_619_i0 child_envelope_sub_619_i0 ?_
  intro b hb
  exact common_sub_619_i0 (mem_commonEnvelope childrenD_619_i0 b hb)

theorem finite_children_work_619 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_619 j) (childrenD_619 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_292 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_619_i0.mono (by decide +kernel)

theorem finite_row_works_619 : FiniteTemplate HasSnaky 8 required_619 envelope_619 := by
  refine finite_compose HasSnaky 7 childrenC_619 childrenD_619 finite_children_work_619 (4, 3)
    required_619 envelope_619 pivot_mem_619 child_required_sub_619 child_envelope_sub_619 ?_
  intro b hb
  exact common_sub_619 (mem_commonEnvelope childrenD_619 b hb)

theorem finite_children_work_651_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_651_i0 j) (childrenD_651_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_55 5 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 7 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_651_i0 : FiniteTemplate HasSnaky 5 required_651_i0 envelope_651_i0 := by
  refine finite_compose HasSnaky 4 childrenC_651_i0 childrenD_651_i0 finite_children_work_651_i0 (3, 5)
    required_651_i0 envelope_651_i0 pivot_mem_651_i0 child_required_sub_651_i0 child_envelope_sub_651_i0 ?_
  intro b hb
  exact common_sub_651_i0 (mem_commonEnvelope childrenD_651_i0 b hb)

theorem finite_children_work_651_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_651_i1 j) (childrenD_651_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_46 5 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_651_i1 : FiniteTemplate HasSnaky 5 required_651_i1 envelope_651_i1 := by
  refine finite_compose HasSnaky 4 childrenC_651_i1 childrenD_651_i1 finite_children_work_651_i1 (3, 5)
    required_651_i1 envelope_651_i1 pivot_mem_651_i1 child_required_sub_651_i1 child_envelope_sub_651_i1 ?_
  intro b hb
  exact common_sub_651_i1 (mem_commonEnvelope childrenD_651_i1 b hb)

theorem finite_children_work_651_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_651_i2 j) (childrenD_651_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_85 7 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_94 2 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_651_i2 : FiniteTemplate HasSnaky 7 required_651_i2 envelope_651_i2 := by
  refine finite_compose HasSnaky 6 childrenC_651_i2 childrenD_651_i2 finite_children_work_651_i2 (4, 3)
    required_651_i2 envelope_651_i2 pivot_mem_651_i2 child_required_sub_651_i2 child_envelope_sub_651_i2 ?_
  intro b hb
  exact common_sub_651_i2 (mem_commonEnvelope childrenD_651_i2 b hb)

theorem finite_children_work_651 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_651 j) (childrenD_651 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_651_i0.mono (by decide +kernel)
  · exact finite_row_works_651_i1.mono (by decide +kernel)
  · exact finite_row_works_651_i2.mono (by decide +kernel)

theorem finite_row_works_651 : FiniteTemplate HasSnaky 8 required_651 envelope_651 := by
  refine finite_compose HasSnaky 7 childrenC_651 childrenD_651 finite_children_work_651 (3, 6)
    required_651 envelope_651 pivot_mem_651 child_required_sub_651 child_envelope_sub_651 ?_
  intro b hb
  exact common_sub_651 (mem_commonEnvelope childrenD_651 b hb)

end FiniteCongruenceChecks.SnakyFinite
