/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part06
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_521_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_521_i1 j) (childrenD_521_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_45 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_45 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_521_i1 : FiniteTemplate HasSnaky 4 required_521_i1 envelope_521_i1 := by
  refine finite_compose HasSnaky 3 childrenC_521_i1 childrenD_521_i1 finite_children_work_521_i1 (2, 3)
    required_521_i1 envelope_521_i1 pivot_mem_521_i1 child_required_sub_521_i1 child_envelope_sub_521_i1 ?_
  intro b hb
  exact common_sub_521_i1 (mem_commonEnvelope childrenD_521_i1 b hb)

theorem finite_children_work_521_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_521_i0 j) (childrenD_521_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_521_i1.mono (by decide +kernel)

theorem finite_row_works_521_i0 : FiniteTemplate HasSnaky 5 required_521_i0 envelope_521_i0 := by
  refine finite_compose HasSnaky 4 childrenC_521_i0 childrenD_521_i0 finite_children_work_521_i0 (2, 4)
    required_521_i0 envelope_521_i0 pivot_mem_521_i0 child_required_sub_521_i0 child_envelope_sub_521_i0 ?_
  intro b hb
  exact common_sub_521_i0 (mem_commonEnvelope childrenD_521_i0 b hb)

theorem finite_children_work_521 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_521 j) (childrenD_521 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_521_i0.mono (by decide +kernel)

theorem finite_row_works_521 : FiniteTemplate HasSnaky 6 required_521 envelope_521 := by
  refine finite_compose HasSnaky 5 childrenC_521 childrenD_521 finite_children_work_521 (2, 1)
    required_521 envelope_521 pivot_mem_521 child_required_sub_521 child_envelope_sub_521 ?_
  intro b hb
  exact common_sub_521 (mem_commonEnvelope childrenD_521 b hb)

theorem finite_children_work_525_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_525_i1 j) (childrenD_525_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_525_i1 : FiniteTemplate HasSnaky 4 required_525_i1 envelope_525_i1 := by
  refine finite_compose HasSnaky 3 childrenC_525_i1 childrenD_525_i1 finite_children_work_525_i1 (3, 3)
    required_525_i1 envelope_525_i1 pivot_mem_525_i1 child_required_sub_525_i1 child_envelope_sub_525_i1 ?_
  intro b hb
  exact common_sub_525_i1 (mem_commonEnvelope childrenD_525_i1 b hb)

theorem finite_children_work_525_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_525_i0 j) (childrenD_525_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_525_i1.mono (by decide +kernel)

theorem finite_row_works_525_i0 : FiniteTemplate HasSnaky 5 required_525_i0 envelope_525_i0 := by
  refine finite_compose HasSnaky 4 childrenC_525_i0 childrenD_525_i0 finite_children_work_525_i0 (3, 2)
    required_525_i0 envelope_525_i0 pivot_mem_525_i0 child_required_sub_525_i0 child_envelope_sub_525_i0 ?_
  intro b hb
  exact common_sub_525_i0 (mem_commonEnvelope childrenD_525_i0 b hb)

theorem finite_children_work_525 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_525 j) (childrenD_525 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_525_i0.mono (by decide +kernel)

theorem finite_row_works_525 : FiniteTemplate HasSnaky 6 required_525 envelope_525 := by
  refine finite_compose HasSnaky 5 childrenC_525 childrenD_525 finite_children_work_525 (3, 0)
    required_525 envelope_525 pivot_mem_525 child_required_sub_525 child_envelope_sub_525 ?_
  intro b hb
  exact common_sub_525 (mem_commonEnvelope childrenD_525 b hb)

theorem finite_children_work_544_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_544_i1 j) (childrenD_544_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_62 7 (6, 4)).mono (by decide +kernel)

theorem finite_row_works_544_i1 : FiniteTemplate HasSnaky 4 required_544_i1 envelope_544_i1 := by
  refine finite_compose HasSnaky 3 childrenC_544_i1 childrenD_544_i1 finite_children_work_544_i1 (5, 3)
    required_544_i1 envelope_544_i1 pivot_mem_544_i1 child_required_sub_544_i1 child_envelope_sub_544_i1 ?_
  intro b hb
  exact common_sub_544_i1 (mem_commonEnvelope childrenD_544_i1 b hb)

theorem finite_children_work_544_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_544_i0 j) (childrenD_544_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_259 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_544_i1.mono (by decide +kernel)

theorem finite_row_works_544_i0 : FiniteTemplate HasSnaky 5 required_544_i0 envelope_544_i0 := by
  refine finite_compose HasSnaky 4 childrenC_544_i0 childrenD_544_i0 finite_children_work_544_i0 (4, 3)
    required_544_i0 envelope_544_i0 pivot_mem_544_i0 child_required_sub_544_i0 child_envelope_sub_544_i0 ?_
  intro b hb
  exact common_sub_544_i0 (mem_commonEnvelope childrenD_544_i0 b hb)

theorem finite_children_work_544 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_544 j) (childrenD_544 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 4 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_544_i0.mono (by decide +kernel)

theorem finite_row_works_544 : FiniteTemplate HasSnaky 6 required_544 envelope_544 := by
  refine finite_compose HasSnaky 5 childrenC_544 childrenD_544 finite_children_work_544 (3, 4)
    required_544 envelope_544 pivot_mem_544 child_required_sub_544 child_envelope_sub_544 ?_
  intro b hb
  exact common_sub_544 (mem_commonEnvelope childrenD_544 b hb)

theorem finite_children_work_600_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_600_i0 j) (childrenD_600_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_600_i0 : FiniteTemplate HasSnaky 5 required_600_i0 envelope_600_i0 := by
  refine finite_compose HasSnaky 4 childrenC_600_i0 childrenD_600_i0 finite_children_work_600_i0 (3, 5)
    required_600_i0 envelope_600_i0 pivot_mem_600_i0 child_required_sub_600_i0 child_envelope_sub_600_i0 ?_
  intro b hb
  exact common_sub_600_i0 (mem_commonEnvelope childrenD_600_i0 b hb)

theorem finite_children_work_600 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_600 j) (childrenD_600 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 6 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_600_i0.mono (by decide +kernel)

theorem finite_row_works_600 : FiniteTemplate HasSnaky 6 required_600 envelope_600 := by
  refine finite_compose HasSnaky 5 childrenC_600 childrenD_600 finite_children_work_600 (3, 2)
    required_600 envelope_600 pivot_mem_600 child_required_sub_600 child_envelope_sub_600 ?_
  intro b hb
  exact common_sub_600 (mem_commonEnvelope childrenD_600 b hb)

theorem finite_children_work_606_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_606_i0 j) (childrenD_606_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_240 2 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_606_i0 : FiniteTemplate HasSnaky 5 required_606_i0 envelope_606_i0 := by
  refine finite_compose HasSnaky 4 childrenC_606_i0 childrenD_606_i0 finite_children_work_606_i0 (3, 4)
    required_606_i0 envelope_606_i0 pivot_mem_606_i0 child_required_sub_606_i0 child_envelope_sub_606_i0 ?_
  intro b hb
  exact common_sub_606_i0 (mem_commonEnvelope childrenD_606_i0 b hb)

theorem finite_children_work_606 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_606 j) (childrenD_606 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_168 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_606_i0.mono (by decide +kernel)

theorem finite_row_works_606 : FiniteTemplate HasSnaky 6 required_606 envelope_606 := by
  refine finite_compose HasSnaky 5 childrenC_606 childrenD_606 finite_children_work_606 (3, 3)
    required_606 envelope_606 pivot_mem_606 child_required_sub_606 child_envelope_sub_606 ?_
  intro b hb
  exact common_sub_606 (mem_commonEnvelope childrenD_606 b hb)

theorem finite_children_work_609_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_609_i0 j) (childrenD_609_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_48 3 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_609_i0 : FiniteTemplate HasSnaky 5 required_609_i0 envelope_609_i0 := by
  refine finite_compose HasSnaky 4 childrenC_609_i0 childrenD_609_i0 finite_children_work_609_i0 (2, 1)
    required_609_i0 envelope_609_i0 pivot_mem_609_i0 child_required_sub_609_i0 child_envelope_sub_609_i0 ?_
  intro b hb
  exact common_sub_609_i0 (mem_commonEnvelope childrenD_609_i0 b hb)

theorem finite_children_work_609_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_609_i1 j) (childrenD_609_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_54 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_609_i1 : FiniteTemplate HasSnaky 4 required_609_i1 envelope_609_i1 := by
  refine finite_compose HasSnaky 3 childrenC_609_i1 childrenD_609_i1 finite_children_work_609_i1 (3, 3)
    required_609_i1 envelope_609_i1 pivot_mem_609_i1 child_required_sub_609_i1 child_envelope_sub_609_i1 ?_
  intro b hb
  exact common_sub_609_i1 (mem_commonEnvelope childrenD_609_i1 b hb)

theorem finite_children_work_609 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_609 j) (childrenD_609 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_609_i0.mono (by decide +kernel)
  · exact finite_row_works_609_i1.mono (by decide +kernel)

theorem finite_row_works_609 : FiniteTemplate HasSnaky 6 required_609 envelope_609 := by
  refine finite_compose HasSnaky 5 childrenC_609 childrenD_609 finite_children_work_609 (3, 1)
    required_609 envelope_609 pivot_mem_609 child_required_sub_609 child_envelope_sub_609 ?_
  intro b hb
  exact common_sub_609 (mem_commonEnvelope childrenD_609 b hb)

theorem finite_children_work_611_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_611_i0 j) (childrenD_611_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_93 3 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_611_i0 : FiniteTemplate HasSnaky 5 required_611_i0 envelope_611_i0 := by
  refine finite_compose HasSnaky 4 childrenC_611_i0 childrenD_611_i0 finite_children_work_611_i0 (2, 3)
    required_611_i0 envelope_611_i0 pivot_mem_611_i0 child_required_sub_611_i0 child_envelope_sub_611_i0 ?_
  intro b hb
  exact common_sub_611_i0 (mem_commonEnvelope childrenD_611_i0 b hb)

theorem finite_children_work_611 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_611 j) (childrenD_611 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 2 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_611_i0.mono (by decide +kernel)

theorem finite_row_works_611 : FiniteTemplate HasSnaky 6 required_611 envelope_611 := by
  refine finite_compose HasSnaky 5 childrenC_611 childrenD_611 finite_children_work_611 (2, 5)
    required_611 envelope_611 pivot_mem_611 child_required_sub_611 child_envelope_sub_611 ?_
  intro b hb
  exact common_sub_611 (mem_commonEnvelope childrenD_611 b hb)

theorem finite_children_work_641_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_641_i0 j) (childrenD_641_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_60 2 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_641_i0 : FiniteTemplate HasSnaky 5 required_641_i0 envelope_641_i0 := by
  refine finite_compose HasSnaky 4 childrenC_641_i0 childrenD_641_i0 finite_children_work_641_i0 (3, 4)
    required_641_i0 envelope_641_i0 pivot_mem_641_i0 child_required_sub_641_i0 child_envelope_sub_641_i0 ?_
  intro b hb
  exact common_sub_641_i0 (mem_commonEnvelope childrenD_641_i0 b hb)

theorem finite_children_work_641 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_641 j) (childrenD_641 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_144 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_641_i0.mono (by decide +kernel)

theorem finite_row_works_641 : FiniteTemplate HasSnaky 6 required_641 envelope_641 := by
  refine finite_compose HasSnaky 5 childrenC_641 childrenD_641 finite_children_work_641 (2, 3)
    required_641 envelope_641 pivot_mem_641 child_required_sub_641 child_envelope_sub_641 ?_
  intro b hb
  exact common_sub_641 (mem_commonEnvelope childrenD_641 b hb)

theorem finite_children_work_714_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_714_i0 j) (childrenD_714_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_41 0 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_714_i0 : FiniteTemplate HasSnaky 5 required_714_i0 envelope_714_i0 := by
  refine finite_compose HasSnaky 4 childrenC_714_i0 childrenD_714_i0 finite_children_work_714_i0 (3, 6)
    required_714_i0 envelope_714_i0 pivot_mem_714_i0 child_required_sub_714_i0 child_envelope_sub_714_i0 ?_
  intro b hb
  exact common_sub_714_i0 (mem_commonEnvelope childrenD_714_i0 b hb)

theorem finite_children_work_714 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_714 j) (childrenD_714 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_88 3 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_714_i0.mono (by decide +kernel)

theorem finite_row_works_714 : FiniteTemplate HasSnaky 6 required_714 envelope_714 := by
  refine finite_compose HasSnaky 5 childrenC_714 childrenD_714 finite_children_work_714 (3, 3)
    required_714 envelope_714 pivot_mem_714 child_required_sub_714 child_envelope_sub_714 ?_
  intro b hb
  exact common_sub_714 (mem_commonEnvelope childrenD_714 b hb)

end FiniteCongruenceChecks.SnakyFinite
