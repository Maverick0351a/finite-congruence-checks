/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_381_i1 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_381_i1 j) (childrenD_381_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_381_i1 : FiniteTemplate HasSnaky 2 required_381_i1 envelope_381_i1 := by
  refine finite_compose HasSnaky 1 childrenC_381_i1 childrenD_381_i1 finite_children_work_381_i1 (4, 1)
    required_381_i1 envelope_381_i1 pivot_mem_381_i1 child_required_sub_381_i1 child_envelope_sub_381_i1 ?_
  intro b hb
  exact common_sub_381_i1 (mem_commonEnvelope childrenD_381_i1 b hb)

theorem finite_children_work_381_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_381_i0 j) (childrenD_381_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_381_i1.mono (by decide +kernel)

theorem finite_row_works_381_i0 : FiniteTemplate HasSnaky 3 required_381_i0 envelope_381_i0 := by
  refine finite_compose HasSnaky 2 childrenC_381_i0 childrenD_381_i0 finite_children_work_381_i0 (4, 0)
    required_381_i0 envelope_381_i0 pivot_mem_381_i0 child_required_sub_381_i0 child_envelope_sub_381_i0 ?_
  intro b hb
  exact common_sub_381_i0 (mem_commonEnvelope childrenD_381_i0 b hb)

theorem finite_children_work_381 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_381 j) (childrenD_381 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_381_i0.mono (by decide +kernel)

theorem finite_row_works_381 : FiniteTemplate HasSnaky 4 required_381 envelope_381 := by
  refine finite_compose HasSnaky 3 childrenC_381 childrenD_381 finite_children_work_381 (3, 1)
    required_381 envelope_381 pivot_mem_381 child_required_sub_381 child_envelope_sub_381 ?_
  intro b hb
  exact common_sub_381 (mem_commonEnvelope childrenD_381 b hb)

theorem finite_children_work_424_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_424_i0 j) (childrenD_424_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_424_i0 : FiniteTemplate HasSnaky 3 required_424_i0 envelope_424_i0 := by
  refine finite_compose HasSnaky 2 childrenC_424_i0 childrenD_424_i0 finite_children_work_424_i0 (4, 2)
    required_424_i0 envelope_424_i0 pivot_mem_424_i0 child_required_sub_424_i0 child_envelope_sub_424_i0 ?_
  intro b hb
  exact common_sub_424_i0 (mem_commonEnvelope childrenD_424_i0 b hb)

theorem finite_children_work_424 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_424 j) (childrenD_424 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_25 5 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_424_i0.mono (by decide +kernel)

theorem finite_row_works_424 : FiniteTemplate HasSnaky 4 required_424 envelope_424 := by
  refine finite_compose HasSnaky 3 childrenC_424 childrenD_424 finite_children_work_424 (3, 4)
    required_424 envelope_424 pivot_mem_424 child_required_sub_424 child_envelope_sub_424 ?_
  intro b hb
  exact common_sub_424 (mem_commonEnvelope childrenD_424 b hb)

theorem finite_children_work_432_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_432_i0 j) (childrenD_432_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_146 5 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_432_i0 : FiniteTemplate HasSnaky 3 required_432_i0 envelope_432_i0 := by
  refine finite_compose HasSnaky 2 childrenC_432_i0 childrenD_432_i0 finite_children_work_432_i0 (4, 1)
    required_432_i0 envelope_432_i0 pivot_mem_432_i0 child_required_sub_432_i0 child_envelope_sub_432_i0 ?_
  intro b hb
  exact common_sub_432_i0 (mem_commonEnvelope childrenD_432_i0 b hb)

theorem finite_children_work_432 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_432 j) (childrenD_432 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_432_i0.mono (by decide +kernel)

theorem finite_row_works_432 : FiniteTemplate HasSnaky 4 required_432 envelope_432 := by
  refine finite_compose HasSnaky 3 childrenC_432 childrenD_432 finite_children_work_432 (4, 0)
    required_432 envelope_432 pivot_mem_432 child_required_sub_432 child_envelope_sub_432 ?_
  intro b hb
  exact common_sub_432 (mem_commonEnvelope childrenD_432 b hb)

theorem finite_children_work_496_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_496_i0 j) (childrenD_496_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_30 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_496_i0 : FiniteTemplate HasSnaky 3 required_496_i0 envelope_496_i0 := by
  refine finite_compose HasSnaky 2 childrenC_496_i0 childrenD_496_i0 finite_children_work_496_i0 (1, 2)
    required_496_i0 envelope_496_i0 pivot_mem_496_i0 child_required_sub_496_i0 child_envelope_sub_496_i0 ?_
  intro b hb
  exact common_sub_496_i0 (mem_commonEnvelope childrenD_496_i0 b hb)

theorem finite_children_work_496 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_496 j) (childrenD_496 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_496_i0.mono (by decide +kernel)

theorem finite_row_works_496 : FiniteTemplate HasSnaky 4 required_496 envelope_496 := by
  refine finite_compose HasSnaky 3 childrenC_496 childrenD_496 finite_children_work_496 (1, 1)
    required_496 envelope_496 pivot_mem_496 child_required_sub_496 child_envelope_sub_496 ?_
  intro b hb
  exact common_sub_496 (mem_commonEnvelope childrenD_496 b hb)

theorem finite_children_work_500_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_500_i0 j) (childrenD_500_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_146.mono (by decide +kernel)

theorem finite_row_works_500_i0 : FiniteTemplate HasSnaky 3 required_500_i0 envelope_500_i0 := by
  refine finite_compose HasSnaky 2 childrenC_500_i0 childrenD_500_i0 finite_children_work_500_i0 (1, 1)
    required_500_i0 envelope_500_i0 pivot_mem_500_i0 child_required_sub_500_i0 child_envelope_sub_500_i0 ?_
  intro b hb
  exact common_sub_500_i0 (mem_commonEnvelope childrenD_500_i0 b hb)

theorem finite_children_work_500 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_500 j) (childrenD_500 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_500_i0.mono (by decide +kernel)

theorem finite_row_works_500 : FiniteTemplate HasSnaky 4 required_500 envelope_500 := by
  refine finite_compose HasSnaky 3 childrenC_500 childrenD_500 finite_children_work_500 (1, 2)
    required_500 envelope_500 pivot_mem_500 child_required_sub_500 child_envelope_sub_500 ?_
  intro b hb
  exact common_sub_500 (mem_commonEnvelope childrenD_500 b hb)

end FiniteCongruenceChecks.SnakyFinite
