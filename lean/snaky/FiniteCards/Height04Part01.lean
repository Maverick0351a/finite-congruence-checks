/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_10 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_10 j) (childrenD_10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_10 : FiniteTemplate HasSnaky 4 required_10 envelope_10 := by
  refine finite_compose HasSnaky 3 childrenC_10 childrenD_10 finite_children_work_10 (1, 4)
    required_10 envelope_10 pivot_mem_10 child_required_sub_10 child_envelope_sub_10 ?_
  intro b hb
  exact common_sub_10 (mem_commonEnvelope childrenD_10 b hb)

theorem finite_children_work_12 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_12 j) (childrenD_12 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_12 : FiniteTemplate HasSnaky 4 required_12 envelope_12 := by
  refine finite_compose HasSnaky 3 childrenC_12 childrenD_12 finite_children_work_12 (1, 5)
    required_12 envelope_12 pivot_mem_12 child_required_sub_12 child_envelope_sub_12 ?_
  intro b hb
  exact common_sub_12 (mem_commonEnvelope childrenD_12 b hb)

theorem finite_children_work_13 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_13 j) (childrenD_13 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_13 : FiniteTemplate HasSnaky 4 required_13 envelope_13 := by
  refine finite_compose HasSnaky 3 childrenC_13 childrenD_13 finite_children_work_13 (1, 5)
    required_13 envelope_13 pivot_mem_13 child_required_sub_13 child_envelope_sub_13 ?_
  intro b hb
  exact common_sub_13 (mem_commonEnvelope childrenD_13 b hb)

theorem finite_children_work_14 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_14 j) (childrenD_14 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_14 : FiniteTemplate HasSnaky 4 required_14 envelope_14 := by
  refine finite_compose HasSnaky 3 childrenC_14 childrenD_14 finite_children_work_14 (1, 5)
    required_14 envelope_14 pivot_mem_14 child_required_sub_14 child_envelope_sub_14 ?_
  intro b hb
  exact common_sub_14 (mem_commonEnvelope childrenD_14 b hb)

theorem finite_children_work_17 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_17 j) (childrenD_17 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 2 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_17 : FiniteTemplate HasSnaky 4 required_17 envelope_17 := by
  refine finite_compose HasSnaky 3 childrenC_17 childrenD_17 finite_children_work_17 (1, 4)
    required_17 envelope_17 pivot_mem_17 child_required_sub_17 child_envelope_sub_17 ?_
  intro b hb
  exact common_sub_17 (mem_commonEnvelope childrenD_17 b hb)

theorem finite_children_work_18 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_18 j) (childrenD_18 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_18 : FiniteTemplate HasSnaky 4 required_18 envelope_18 := by
  refine finite_compose HasSnaky 3 childrenC_18 childrenD_18 finite_children_work_18 (1, 4)
    required_18 envelope_18 pivot_mem_18 child_required_sub_18 child_envelope_sub_18 ?_
  intro b hb
  exact common_sub_18 (mem_commonEnvelope childrenD_18 b hb)

theorem finite_children_work_26 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_26 j) (childrenD_26 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_7 3 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_26 : FiniteTemplate HasSnaky 4 required_26 envelope_26 := by
  refine finite_compose HasSnaky 3 childrenC_26 childrenD_26 finite_children_work_26 (4, 1)
    required_26 envelope_26 pivot_mem_26 child_required_sub_26 child_envelope_sub_26 ?_
  intro b hb
  exact common_sub_26 (mem_commonEnvelope childrenD_26 b hb)

theorem finite_children_work_27 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_27 j) (childrenD_27 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_27 : FiniteTemplate HasSnaky 4 required_27 envelope_27 := by
  refine finite_compose HasSnaky 3 childrenC_27 childrenD_27 finite_children_work_27 (0, 4)
    required_27 envelope_27 pivot_mem_27 child_required_sub_27 child_envelope_sub_27 ?_
  intro b hb
  exact common_sub_27 (mem_commonEnvelope childrenD_27 b hb)

theorem finite_children_work_31 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_31 j) (childrenD_31 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_31 : FiniteTemplate HasSnaky 4 required_31 envelope_31 := by
  refine finite_compose HasSnaky 3 childrenC_31 childrenD_31 finite_children_work_31 (1, 5)
    required_31 envelope_31 pivot_mem_31 child_required_sub_31 child_envelope_sub_31 ?_
  intro b hb
  exact common_sub_31 (mem_commonEnvelope childrenD_31 b hb)

theorem finite_children_work_33 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_33 j) (childrenD_33 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_33 : FiniteTemplate HasSnaky 4 required_33 envelope_33 := by
  refine finite_compose HasSnaky 3 childrenC_33 childrenD_33 finite_children_work_33 (1, 5)
    required_33 envelope_33 pivot_mem_33 child_required_sub_33 child_envelope_sub_33 ?_
  intro b hb
  exact common_sub_33 (mem_commonEnvelope childrenD_33 b hb)

theorem finite_children_work_39 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_39 j) (childrenD_39 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_39 : FiniteTemplate HasSnaky 4 required_39 envelope_39 := by
  refine finite_compose HasSnaky 3 childrenC_39 childrenD_39 finite_children_work_39 (1, 3)
    required_39 envelope_39 pivot_mem_39 child_required_sub_39 child_envelope_sub_39 ?_
  intro b hb
  exact common_sub_39 (mem_commonEnvelope childrenD_39 b hb)

theorem finite_children_work_41 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_41 j) (childrenD_41 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_41 : FiniteTemplate HasSnaky 4 required_41 envelope_41 := by
  refine finite_compose HasSnaky 3 childrenC_41 childrenD_41 finite_children_work_41 (1, 4)
    required_41 envelope_41 pivot_mem_41 child_required_sub_41 child_envelope_sub_41 ?_
  intro b hb
  exact common_sub_41 (mem_commonEnvelope childrenD_41 b hb)

theorem finite_children_work_42 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_42 j) (childrenD_42 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_42 : FiniteTemplate HasSnaky 4 required_42 envelope_42 := by
  refine finite_compose HasSnaky 3 childrenC_42 childrenD_42 finite_children_work_42 (1, 3)
    required_42 envelope_42 pivot_mem_42 child_required_sub_42 child_envelope_sub_42 ?_
  intro b hb
  exact common_sub_42 (mem_commonEnvelope childrenD_42 b hb)

theorem finite_children_work_46 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_46 j) (childrenD_46 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_45.mono (by decide +kernel)

theorem finite_row_works_46 : FiniteTemplate HasSnaky 4 required_46 envelope_46 := by
  refine finite_compose HasSnaky 3 childrenC_46 childrenD_46 finite_children_work_46 (3, 1)
    required_46 envelope_46 pivot_mem_46 child_required_sub_46 child_envelope_sub_46 ?_
  intro b hb
  exact common_sub_46 (mem_commonEnvelope childrenD_46 b hb)

theorem finite_children_work_48 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_48 j) (childrenD_48 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_48 : FiniteTemplate HasSnaky 4 required_48 envelope_48 := by
  refine finite_compose HasSnaky 3 childrenC_48 childrenD_48 finite_children_work_48 (1, 4)
    required_48 envelope_48 pivot_mem_48 child_required_sub_48 child_envelope_sub_48 ?_
  intro b hb
  exact common_sub_48 (mem_commonEnvelope childrenD_48 b hb)

theorem finite_children_work_49 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_49 j) (childrenD_49 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_49 : FiniteTemplate HasSnaky 4 required_49 envelope_49 := by
  refine finite_compose HasSnaky 3 childrenC_49 childrenD_49 finite_children_work_49 (4, 1)
    required_49 envelope_49 pivot_mem_49 child_required_sub_49 child_envelope_sub_49 ?_
  intro b hb
  exact common_sub_49 (mem_commonEnvelope childrenD_49 b hb)

theorem finite_children_work_50 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_50 j) (childrenD_50 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_50 : FiniteTemplate HasSnaky 4 required_50 envelope_50 := by
  refine finite_compose HasSnaky 3 childrenC_50 childrenD_50 finite_children_work_50 (1, 2)
    required_50 envelope_50 pivot_mem_50 child_required_sub_50 child_envelope_sub_50 ?_
  intro b hb
  exact common_sub_50 (mem_commonEnvelope childrenD_50 b hb)

theorem finite_children_work_55 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_55 j) (childrenD_55 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_55 : FiniteTemplate HasSnaky 4 required_55 envelope_55 := by
  refine finite_compose HasSnaky 3 childrenC_55 childrenD_55 finite_children_work_55 (3, 4)
    required_55 envelope_55 pivot_mem_55 child_required_sub_55 child_envelope_sub_55 ?_
  intro b hb
  exact common_sub_55 (mem_commonEnvelope childrenD_55 b hb)

theorem finite_children_work_56 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_56 j) (childrenD_56 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 6 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_56 : FiniteTemplate HasSnaky 4 required_56 envelope_56 := by
  refine finite_compose HasSnaky 3 childrenC_56 childrenD_56 finite_children_work_56 (3, 4)
    required_56 envelope_56 pivot_mem_56 child_required_sub_56 child_envelope_sub_56 ?_
  intro b hb
  exact common_sub_56 (mem_commonEnvelope childrenD_56 b hb)

theorem finite_children_work_57 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_57 j) (childrenD_57 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 6 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_57 : FiniteTemplate HasSnaky 4 required_57 envelope_57 := by
  refine finite_compose HasSnaky 3 childrenC_57 childrenD_57 finite_children_work_57 (3, 4)
    required_57 envelope_57 pivot_mem_57 child_required_sub_57 child_envelope_sub_57 ?_
  intro b hb
  exact common_sub_57 (mem_commonEnvelope childrenD_57 b hb)

theorem finite_children_work_58 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_58 j) (childrenD_58 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_58 : FiniteTemplate HasSnaky 4 required_58 envelope_58 := by
  refine finite_compose HasSnaky 3 childrenC_58 childrenD_58 finite_children_work_58 (4, 3)
    required_58 envelope_58 pivot_mem_58 child_required_sub_58 child_envelope_sub_58 ?_
  intro b hb
  exact common_sub_58 (mem_commonEnvelope childrenD_58 b hb)

theorem finite_children_work_60 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_60 j) (childrenD_60 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_60 : FiniteTemplate HasSnaky 4 required_60 envelope_60 := by
  refine finite_compose HasSnaky 3 childrenC_60 childrenD_60 finite_children_work_60 (0, 3)
    required_60 envelope_60 pivot_mem_60 child_required_sub_60 child_envelope_sub_60 ?_
  intro b hb
  exact common_sub_60 (mem_commonEnvelope childrenD_60 b hb)

theorem finite_children_work_63 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_63 j) (childrenD_63 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 2 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_62 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_63 : FiniteTemplate HasSnaky 4 required_63 envelope_63 := by
  refine finite_compose HasSnaky 3 childrenC_63 childrenD_63 finite_children_work_63 (1, 4)
    required_63 envelope_63 pivot_mem_63 child_required_sub_63 child_envelope_sub_63 ?_
  intro b hb
  exact common_sub_63 (mem_commonEnvelope childrenD_63 b hb)

theorem finite_children_work_65 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_65 j) (childrenD_65 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_20 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_65 : FiniteTemplate HasSnaky 4 required_65 envelope_65 := by
  refine finite_compose HasSnaky 3 childrenC_65 childrenD_65 finite_children_work_65 (1, 5)
    required_65 envelope_65 pivot_mem_65 child_required_sub_65 child_envelope_sub_65 ?_
  intro b hb
  exact common_sub_65 (mem_commonEnvelope childrenD_65 b hb)

end FiniteCongruenceChecks.SnakyFinite
