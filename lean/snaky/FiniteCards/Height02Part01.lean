/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part01
import FiniteCards.Height01Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_6 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_6 j) (childrenD_6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_6 : FiniteTemplate HasSnaky 2 required_6 envelope_6 := by
  refine finite_compose HasSnaky 1 childrenC_6 childrenD_6 finite_children_work_6 (1, 4)
    required_6 envelope_6 pivot_mem_6 child_required_sub_6 child_envelope_sub_6 ?_
  intro b hb
  exact common_sub_6 (mem_commonEnvelope childrenD_6 b hb)

theorem finite_children_work_11 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_11 j) (childrenD_11 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_11 : FiniteTemplate HasSnaky 2 required_11 envelope_11 := by
  refine finite_compose HasSnaky 1 childrenC_11 childrenD_11 finite_children_work_11 (1, 1)
    required_11 envelope_11 pivot_mem_11 child_required_sub_11 child_envelope_sub_11 ?_
  intro b hb
  exact common_sub_11 (mem_commonEnvelope childrenD_11 b hb)

theorem finite_children_work_15 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_15 j) (childrenD_15 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_15 : FiniteTemplate HasSnaky 2 required_15 envelope_15 := by
  refine finite_compose HasSnaky 1 childrenC_15 childrenD_15 finite_children_work_15 (1, 4)
    required_15 envelope_15 pivot_mem_15 child_required_sub_15 child_envelope_sub_15 ?_
  intro b hb
  exact common_sub_15 (mem_commonEnvelope childrenD_15 b hb)

theorem finite_children_work_22 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_22 j) (childrenD_22 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_22 : FiniteTemplate HasSnaky 2 required_22 envelope_22 := by
  refine finite_compose HasSnaky 1 childrenC_22 childrenD_22 finite_children_work_22 (0, 3)
    required_22 envelope_22 pivot_mem_22 child_required_sub_22 child_envelope_sub_22 ?_
  intro b hb
  exact common_sub_22 (mem_commonEnvelope childrenD_22 b hb)

theorem finite_children_work_23 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_23 j) (childrenD_23 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_23 : FiniteTemplate HasSnaky 2 required_23 envelope_23 := by
  refine finite_compose HasSnaky 1 childrenC_23 childrenD_23 finite_children_work_23 (0, 4)
    required_23 envelope_23 pivot_mem_23 child_required_sub_23 child_envelope_sub_23 ?_
  intro b hb
  exact common_sub_23 (mem_commonEnvelope childrenD_23 b hb)

theorem finite_children_work_25 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_25 j) (childrenD_25 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_25 : FiniteTemplate HasSnaky 2 required_25 envelope_25 := by
  refine finite_compose HasSnaky 1 childrenC_25 childrenD_25 finite_children_work_25 (3, 0)
    required_25 envelope_25 pivot_mem_25 child_required_sub_25 child_envelope_sub_25 ?_
  intro b hb
  exact common_sub_25 (mem_commonEnvelope childrenD_25 b hb)

theorem finite_children_work_28 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_28 j) (childrenD_28 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_28 : FiniteTemplate HasSnaky 2 required_28 envelope_28 := by
  refine finite_compose HasSnaky 1 childrenC_28 childrenD_28 finite_children_work_28 (1, 2)
    required_28 envelope_28 pivot_mem_28 child_required_sub_28 child_envelope_sub_28 ?_
  intro b hb
  exact common_sub_28 (mem_commonEnvelope childrenD_28 b hb)

theorem finite_children_work_30 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_30 j) (childrenD_30 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_30 : FiniteTemplate HasSnaky 2 required_30 envelope_30 := by
  refine finite_compose HasSnaky 1 childrenC_30 childrenD_30 finite_children_work_30 (0, 2)
    required_30 envelope_30 pivot_mem_30 child_required_sub_30 child_envelope_sub_30 ?_
  intro b hb
  exact common_sub_30 (mem_commonEnvelope childrenD_30 b hb)

theorem finite_children_work_32 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_32 j) (childrenD_32 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_32 : FiniteTemplate HasSnaky 2 required_32 envelope_32 := by
  refine finite_compose HasSnaky 1 childrenC_32 childrenD_32 finite_children_work_32 (3, 0)
    required_32 envelope_32 pivot_mem_32 child_required_sub_32 child_envelope_sub_32 ?_
  intro b hb
  exact common_sub_32 (mem_commonEnvelope childrenD_32 b hb)

theorem finite_children_work_34 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_34 j) (childrenD_34 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_34 : FiniteTemplate HasSnaky 2 required_34 envelope_34 := by
  refine finite_compose HasSnaky 1 childrenC_34 childrenD_34 finite_children_work_34 (0, 3)
    required_34 envelope_34 pivot_mem_34 child_required_sub_34 child_envelope_sub_34 ?_
  intro b hb
  exact common_sub_34 (mem_commonEnvelope childrenD_34 b hb)

theorem finite_children_work_35 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_35 j) (childrenD_35 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 7 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_35 : FiniteTemplate HasSnaky 2 required_35 envelope_35 := by
  refine finite_compose HasSnaky 1 childrenC_35 childrenD_35 finite_children_work_35 (3, 2)
    required_35 envelope_35 pivot_mem_35 child_required_sub_35 child_envelope_sub_35 ?_
  intro b hb
  exact common_sub_35 (mem_commonEnvelope childrenD_35 b hb)

theorem finite_children_work_36 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_36 j) (childrenD_36 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_2 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_36 : FiniteTemplate HasSnaky 2 required_36 envelope_36 := by
  refine finite_compose HasSnaky 1 childrenC_36 childrenD_36 finite_children_work_36 (1, 4)
    required_36 envelope_36 pivot_mem_36 child_required_sub_36 child_envelope_sub_36 ?_
  intro b hb
  exact common_sub_36 (mem_commonEnvelope childrenD_36 b hb)

theorem finite_children_work_38 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_38 j) (childrenD_38 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_38 : FiniteTemplate HasSnaky 2 required_38 envelope_38 := by
  refine finite_compose HasSnaky 1 childrenC_38 childrenD_38 finite_children_work_38 (3, 2)
    required_38 envelope_38 pivot_mem_38 child_required_sub_38 child_envelope_sub_38 ?_
  intro b hb
  exact common_sub_38 (mem_commonEnvelope childrenD_38 b hb)

theorem finite_children_work_40 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_40 j) (childrenD_40 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_40 : FiniteTemplate HasSnaky 2 required_40 envelope_40 := by
  refine finite_compose HasSnaky 1 childrenC_40 childrenD_40 finite_children_work_40 (1, 3)
    required_40 envelope_40 pivot_mem_40 child_required_sub_40 child_envelope_sub_40 ?_
  intro b hb
  exact common_sub_40 (mem_commonEnvelope childrenD_40 b hb)

theorem finite_children_work_43 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_43 j) (childrenD_43 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_43 : FiniteTemplate HasSnaky 2 required_43 envelope_43 := by
  refine finite_compose HasSnaky 1 childrenC_43 childrenD_43 finite_children_work_43 (1, 4)
    required_43 envelope_43 pivot_mem_43 child_required_sub_43 child_envelope_sub_43 ?_
  intro b hb
  exact common_sub_43 (mem_commonEnvelope childrenD_43 b hb)

theorem finite_children_work_51 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_51 j) (childrenD_51 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_51 : FiniteTemplate HasSnaky 2 required_51 envelope_51 := by
  refine finite_compose HasSnaky 1 childrenC_51 childrenD_51 finite_children_work_51 (1, 4)
    required_51 envelope_51 pivot_mem_51 child_required_sub_51 child_envelope_sub_51 ?_
  intro b hb
  exact common_sub_51 (mem_commonEnvelope childrenD_51 b hb)

theorem finite_children_work_66 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_66 j) (childrenD_66 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_66 : FiniteTemplate HasSnaky 2 required_66 envelope_66 := by
  refine finite_compose HasSnaky 1 childrenC_66 childrenD_66 finite_children_work_66 (1, 4)
    required_66 envelope_66 pivot_mem_66 child_required_sub_66 child_envelope_sub_66 ?_
  intro b hb
  exact common_sub_66 (mem_commonEnvelope childrenD_66 b hb)

theorem finite_children_work_68 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_68 j) (childrenD_68 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_1 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_68 : FiniteTemplate HasSnaky 2 required_68 envelope_68 := by
  refine finite_compose HasSnaky 1 childrenC_68 childrenD_68 finite_children_work_68 (0, 2)
    required_68 envelope_68 pivot_mem_68 child_required_sub_68 child_envelope_sub_68 ?_
  intro b hb
  exact common_sub_68 (mem_commonEnvelope childrenD_68 b hb)

theorem finite_children_work_70 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_70 j) (childrenD_70 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_70 : FiniteTemplate HasSnaky 2 required_70 envelope_70 := by
  refine finite_compose HasSnaky 1 childrenC_70 childrenD_70 finite_children_work_70 (1, 3)
    required_70 envelope_70 pivot_mem_70 child_required_sub_70 child_envelope_sub_70 ?_
  intro b hb
  exact common_sub_70 (mem_commonEnvelope childrenD_70 b hb)

theorem finite_children_work_76 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_76 j) (childrenD_76 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_76 : FiniteTemplate HasSnaky 2 required_76 envelope_76 := by
  refine finite_compose HasSnaky 1 childrenC_76 childrenD_76 finite_children_work_76 (1, 4)
    required_76 envelope_76 pivot_mem_76 child_required_sub_76 child_envelope_sub_76 ?_
  intro b hb
  exact common_sub_76 (mem_commonEnvelope childrenD_76 b hb)

theorem finite_children_work_77 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_77 j) (childrenD_77 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_77 : FiniteTemplate HasSnaky 2 required_77 envelope_77 := by
  refine finite_compose HasSnaky 1 childrenC_77 childrenD_77 finite_children_work_77 (2, 1)
    required_77 envelope_77 pivot_mem_77 child_required_sub_77 child_envelope_sub_77 ?_
  intro b hb
  exact common_sub_77 (mem_commonEnvelope childrenD_77 b hb)

theorem finite_children_work_80 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_80 j) (childrenD_80 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_80 : FiniteTemplate HasSnaky 2 required_80 envelope_80 := by
  refine finite_compose HasSnaky 1 childrenC_80 childrenD_80 finite_children_work_80 (1, 3)
    required_80 envelope_80 pivot_mem_80 child_required_sub_80 child_envelope_sub_80 ?_
  intro b hb
  exact common_sub_80 (mem_commonEnvelope childrenD_80 b hb)

theorem finite_children_work_83 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_83 j) (childrenD_83 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_83 : FiniteTemplate HasSnaky 2 required_83 envelope_83 := by
  refine finite_compose HasSnaky 1 childrenC_83 childrenD_83 finite_children_work_83 (1, 4)
    required_83 envelope_83 pivot_mem_83 child_required_sub_83 child_envelope_sub_83 ?_
  intro b hb
  exact common_sub_83 (mem_commonEnvelope childrenD_83 b hb)

theorem finite_children_work_94 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_94 j) (childrenD_94 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_94 : FiniteTemplate HasSnaky 2 required_94 envelope_94 := by
  refine finite_compose HasSnaky 1 childrenC_94 childrenD_94 finite_children_work_94 (0, 3)
    required_94 envelope_94 pivot_mem_94 child_required_sub_94 child_envelope_sub_94 ?_
  intro b hb
  exact common_sub_94 (mem_commonEnvelope childrenD_94 b hb)

end FiniteCongruenceChecks.SnakyFinite
