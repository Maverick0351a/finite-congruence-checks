/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_7 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_7 j) (childrenD_7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_7 : FiniteTemplate HasSnaky 3 required_7 envelope_7 := by
  refine finite_compose HasSnaky 2 childrenC_7 childrenD_7 finite_children_work_7 (0, 5)
    required_7 envelope_7 pivot_mem_7 child_required_sub_7 child_envelope_sub_7 ?_
  intro b hb
  exact common_sub_7 (mem_commonEnvelope childrenD_7 b hb)

theorem finite_children_work_8 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_8 j) (childrenD_8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_8 : FiniteTemplate HasSnaky 3 required_8 envelope_8 := by
  refine finite_compose HasSnaky 2 childrenC_8 childrenD_8 finite_children_work_8 (4, 1)
    required_8 envelope_8 pivot_mem_8 child_required_sub_8 child_envelope_sub_8 ?_
  intro b hb
  exact common_sub_8 (mem_commonEnvelope childrenD_8 b hb)

theorem finite_children_work_9 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_9 j) (childrenD_9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_9 : FiniteTemplate HasSnaky 3 required_9 envelope_9 := by
  refine finite_compose HasSnaky 2 childrenC_9 childrenD_9 finite_children_work_9 (1, 5)
    required_9 envelope_9 pivot_mem_9 child_required_sub_9 child_envelope_sub_9 ?_
  intro b hb
  exact common_sub_9 (mem_commonEnvelope childrenD_9 b hb)

theorem finite_children_work_16 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_16 j) (childrenD_16 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_6.mono (by decide +kernel)

theorem finite_row_works_16 : FiniteTemplate HasSnaky 3 required_16 envelope_16 := by
  refine finite_compose HasSnaky 2 childrenC_16 childrenD_16 finite_children_work_16 (0, 4)
    required_16 envelope_16 pivot_mem_16 child_required_sub_16 child_envelope_sub_16 ?_
  intro b hb
  exact common_sub_16 (mem_commonEnvelope childrenD_16 b hb)

theorem finite_children_work_20 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_20 j) (childrenD_20 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_20 : FiniteTemplate HasSnaky 3 required_20 envelope_20 := by
  refine finite_compose HasSnaky 2 childrenC_20 childrenD_20 finite_children_work_20 (1, 4)
    required_20 envelope_20 pivot_mem_20 child_required_sub_20 child_envelope_sub_20 ?_
  intro b hb
  exact common_sub_20 (mem_commonEnvelope childrenD_20 b hb)

theorem finite_children_work_21 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_21 j) (childrenD_21 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_6.mono (by decide +kernel)

theorem finite_row_works_21 : FiniteTemplate HasSnaky 3 required_21 envelope_21 := by
  refine finite_compose HasSnaky 2 childrenC_21 childrenD_21 finite_children_work_21 (0, 4)
    required_21 envelope_21 pivot_mem_21 child_required_sub_21 child_envelope_sub_21 ?_
  intro b hb
  exact common_sub_21 (mem_commonEnvelope childrenD_21 b hb)

theorem finite_children_work_24 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_24 j) (childrenD_24 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 6 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_24 : FiniteTemplate HasSnaky 3 required_24 envelope_24 := by
  refine finite_compose HasSnaky 2 childrenC_24 childrenD_24 finite_children_work_24 (4, 1)
    required_24 envelope_24 pivot_mem_24 child_required_sub_24 child_envelope_sub_24 ?_
  intro b hb
  exact common_sub_24 (mem_commonEnvelope childrenD_24 b hb)

theorem finite_children_work_29 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_29 j) (childrenD_29 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_6.mono (by decide +kernel)

theorem finite_row_works_29 : FiniteTemplate HasSnaky 3 required_29 envelope_29 := by
  refine finite_compose HasSnaky 2 childrenC_29 childrenD_29 finite_children_work_29 (0, 4)
    required_29 envelope_29 pivot_mem_29 child_required_sub_29 child_envelope_sub_29 ?_
  intro b hb
  exact common_sub_29 (mem_commonEnvelope childrenD_29 b hb)

theorem finite_children_work_37 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_37 j) (childrenD_37 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_37 : FiniteTemplate HasSnaky 3 required_37 envelope_37 := by
  refine finite_compose HasSnaky 2 childrenC_37 childrenD_37 finite_children_work_37 (1, 4)
    required_37 envelope_37 pivot_mem_37 child_required_sub_37 child_envelope_sub_37 ?_
  intro b hb
  exact common_sub_37 (mem_commonEnvelope childrenD_37 b hb)

theorem finite_children_work_44 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_44 j) (childrenD_44 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_43 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_44 : FiniteTemplate HasSnaky 3 required_44 envelope_44 := by
  refine finite_compose HasSnaky 2 childrenC_44 childrenD_44 finite_children_work_44 (1, 4)
    required_44 envelope_44 pivot_mem_44 child_required_sub_44 child_envelope_sub_44 ?_
  intro b hb
  exact common_sub_44 (mem_commonEnvelope childrenD_44 b hb)

theorem finite_children_work_45 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_45 j) (childrenD_45 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_45 : FiniteTemplate HasSnaky 3 required_45 envelope_45 := by
  refine finite_compose HasSnaky 2 childrenC_45 childrenD_45 finite_children_work_45 (3, 3)
    required_45 envelope_45 pivot_mem_45 child_required_sub_45 child_envelope_sub_45 ?_
  intro b hb
  exact common_sub_45 (mem_commonEnvelope childrenD_45 b hb)

theorem finite_children_work_52 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_52 j) (childrenD_52 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_51 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_52 : FiniteTemplate HasSnaky 3 required_52 envelope_52 := by
  refine finite_compose HasSnaky 2 childrenC_52 childrenD_52 finite_children_work_52 (1, 4)
    required_52 envelope_52 pivot_mem_52 child_required_sub_52 child_envelope_sub_52 ?_
  intro b hb
  exact common_sub_52 (mem_commonEnvelope childrenD_52 b hb)

theorem finite_children_work_53 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_53 j) (childrenD_53 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_51 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_53 : FiniteTemplate HasSnaky 3 required_53 envelope_53 := by
  refine finite_compose HasSnaky 2 childrenC_53 childrenD_53 finite_children_work_53 (0, 1)
    required_53 envelope_53 pivot_mem_53 child_required_sub_53 child_envelope_sub_53 ?_
  intro b hb
  exact common_sub_53 (mem_commonEnvelope childrenD_53 b hb)

theorem finite_children_work_54 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_54 j) (childrenD_54 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_51 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_54 : FiniteTemplate HasSnaky 3 required_54 envelope_54 := by
  refine finite_compose HasSnaky 2 childrenC_54 childrenD_54 finite_children_work_54 (0, 2)
    required_54 envelope_54 pivot_mem_54 child_required_sub_54 child_envelope_sub_54 ?_
  intro b hb
  exact common_sub_54 (mem_commonEnvelope childrenD_54 b hb)

theorem finite_children_work_61 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_61 j) (childrenD_61 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_51 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_61 : FiniteTemplate HasSnaky 3 required_61 envelope_61 := by
  refine finite_compose HasSnaky 2 childrenC_61 childrenD_61 finite_children_work_61 (1, 3)
    required_61 envelope_61 pivot_mem_61 child_required_sub_61 child_envelope_sub_61 ?_
  intro b hb
  exact common_sub_61 (mem_commonEnvelope childrenD_61 b hb)

theorem finite_children_work_62 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_62 j) (childrenD_62 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 4 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_62 : FiniteTemplate HasSnaky 3 required_62 envelope_62 := by
  refine finite_compose HasSnaky 2 childrenC_62 childrenD_62 finite_children_work_62 (1, 5)
    required_62 envelope_62 pivot_mem_62 child_required_sub_62 child_envelope_sub_62 ?_
  intro b hb
  exact common_sub_62 (mem_commonEnvelope childrenD_62 b hb)

theorem finite_children_work_64 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_64 j) (childrenD_64 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_43 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_64 : FiniteTemplate HasSnaky 3 required_64 envelope_64 := by
  refine finite_compose HasSnaky 2 childrenC_64 childrenD_64 finite_children_work_64 (0, 2)
    required_64 envelope_64 pivot_mem_64 child_required_sub_64 child_envelope_sub_64 ?_
  intro b hb
  exact common_sub_64 (mem_commonEnvelope childrenD_64 b hb)

theorem finite_children_work_69 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_69 j) (childrenD_69 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_15 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_69 : FiniteTemplate HasSnaky 3 required_69 envelope_69 := by
  refine finite_compose HasSnaky 2 childrenC_69 childrenD_69 finite_children_work_69 (3, 1)
    required_69 envelope_69 pivot_mem_69 child_required_sub_69 child_envelope_sub_69 ?_
  intro b hb
  exact common_sub_69 (mem_commonEnvelope childrenD_69 b hb)

theorem finite_children_work_74 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_74 j) (childrenD_74 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_30.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_30 2 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_36.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_36 2 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_74 : FiniteTemplate HasSnaky 3 required_74 envelope_74 := by
  refine finite_compose HasSnaky 2 childrenC_74 childrenD_74 finite_children_work_74 (1, 3)
    required_74 envelope_74 pivot_mem_74 child_required_sub_74 child_envelope_sub_74 ?_
  intro b hb
  exact common_sub_74 (mem_commonEnvelope childrenD_74 b hb)

theorem finite_children_work_78 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_78 j) (childrenD_78 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_77 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_78 : FiniteTemplate HasSnaky 3 required_78 envelope_78 := by
  refine finite_compose HasSnaky 2 childrenC_78 childrenD_78 finite_children_work_78 (3, 0)
    required_78 envelope_78 pivot_mem_78 child_required_sub_78 child_envelope_sub_78 ?_
  intro b hb
  exact common_sub_78 (mem_commonEnvelope childrenD_78 b hb)

theorem finite_children_work_87 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_87 j) (childrenD_87 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_87 : FiniteTemplate HasSnaky 3 required_87 envelope_87 := by
  refine finite_compose HasSnaky 2 childrenC_87 childrenD_87 finite_children_work_87 (4, 2)
    required_87 envelope_87 pivot_mem_87 child_required_sub_87 child_envelope_sub_87 ?_
  intro b hb
  exact common_sub_87 (mem_commonEnvelope childrenD_87 b hb)

theorem finite_children_work_101 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_101 j) (childrenD_101 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_51 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_101 : FiniteTemplate HasSnaky 3 required_101 envelope_101 := by
  refine finite_compose HasSnaky 2 childrenC_101 childrenD_101 finite_children_work_101 (0, 3)
    required_101 envelope_101 pivot_mem_101 child_required_sub_101 child_envelope_sub_101 ?_
  intro b hb
  exact common_sub_101 (mem_commonEnvelope childrenD_101 b hb)

theorem finite_children_work_103 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_103 j) (childrenD_103 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_6.mono (by decide +kernel)
  · exact finite_row_works_11.mono (by decide +kernel)

theorem finite_row_works_103 : FiniteTemplate HasSnaky 3 required_103 envelope_103 := by
  refine finite_compose HasSnaky 2 childrenC_103 childrenD_103 finite_children_work_103 (0, 4)
    required_103 envelope_103 pivot_mem_103 child_required_sub_103 child_envelope_sub_103 ?_
  intro b hb
  exact common_sub_103 (mem_commonEnvelope childrenD_103 b hb)

theorem finite_children_work_105 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_105 j) (childrenD_105 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_11.mono (by decide +kernel)

theorem finite_row_works_105 : FiniteTemplate HasSnaky 3 required_105 envelope_105 := by
  refine finite_compose HasSnaky 2 childrenC_105 childrenD_105 finite_children_work_105 (0, 3)
    required_105 envelope_105 pivot_mem_105 child_required_sub_105 child_envelope_sub_105 ?_
  intro b hb
  exact common_sub_105 (mem_commonEnvelope childrenD_105 b hb)

end FiniteCongruenceChecks.SnakyFinite
