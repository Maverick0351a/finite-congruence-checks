/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height02Part02
import FiniteCards.Height01Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_96 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_96 j) (childrenD_96 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 5 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_96 : FiniteTemplate HasSnaky 2 required_96 envelope_96 := by
  refine finite_compose HasSnaky 1 childrenC_96 childrenD_96 finite_children_work_96 (3, 0)
    required_96 envelope_96 pivot_mem_96 child_required_sub_96 child_envelope_sub_96 ?_
  intro b hb
  exact common_sub_96 (mem_commonEnvelope childrenD_96 b hb)

theorem finite_children_work_102 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_102 j) (childrenD_102 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_102 : FiniteTemplate HasSnaky 2 required_102 envelope_102 := by
  refine finite_compose HasSnaky 1 childrenC_102 childrenD_102 finite_children_work_102 (1, 3)
    required_102 envelope_102 pivot_mem_102 child_required_sub_102 child_envelope_sub_102 ?_
  intro b hb
  exact common_sub_102 (mem_commonEnvelope childrenD_102 b hb)

theorem finite_children_work_121 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_121 j) (childrenD_121 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_121 : FiniteTemplate HasSnaky 2 required_121 envelope_121 := by
  refine finite_compose HasSnaky 1 childrenC_121 childrenD_121 finite_children_work_121 (3, 0)
    required_121 envelope_121 pivot_mem_121 child_required_sub_121 child_envelope_sub_121 ?_
  intro b hb
  exact common_sub_121 (mem_commonEnvelope childrenD_121 b hb)

theorem finite_children_work_123 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_123 j) (childrenD_123 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_4 6 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_123 : FiniteTemplate HasSnaky 2 required_123 envelope_123 := by
  refine finite_compose HasSnaky 1 childrenC_123 childrenD_123 finite_children_work_123 (4, 1)
    required_123 envelope_123 pivot_mem_123 child_required_sub_123 child_envelope_sub_123 ?_
  intro b hb
  exact common_sub_123 (mem_commonEnvelope childrenD_123 b hb)

theorem finite_children_work_129 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_129 j) (childrenD_129 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_129 : FiniteTemplate HasSnaky 2 required_129 envelope_129 := by
  refine finite_compose HasSnaky 1 childrenC_129 childrenD_129 finite_children_work_129 (1, 2)
    required_129 envelope_129 pivot_mem_129 child_required_sub_129 child_envelope_sub_129 ?_
  intro b hb
  exact common_sub_129 (mem_commonEnvelope childrenD_129 b hb)

theorem finite_children_work_138 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_138 j) (childrenD_138 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_138 : FiniteTemplate HasSnaky 2 required_138 envelope_138 := by
  refine finite_compose HasSnaky 1 childrenC_138 childrenD_138 finite_children_work_138 (1, 4)
    required_138 envelope_138 pivot_mem_138 child_required_sub_138 child_envelope_sub_138 ?_
  intro b hb
  exact common_sub_138 (mem_commonEnvelope childrenD_138 b hb)

theorem finite_children_work_146 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_146 j) (childrenD_146 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_146 : FiniteTemplate HasSnaky 2 required_146 envelope_146 := by
  refine finite_compose HasSnaky 1 childrenC_146 childrenD_146 finite_children_work_146 (2, 1)
    required_146 envelope_146 pivot_mem_146 child_required_sub_146 child_envelope_sub_146 ?_
  intro b hb
  exact common_sub_146 (mem_commonEnvelope childrenD_146 b hb)

theorem finite_children_work_153 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_153 j) (childrenD_153 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 2 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_153 : FiniteTemplate HasSnaky 2 required_153 envelope_153 := by
  refine finite_compose HasSnaky 1 childrenC_153 childrenD_153 finite_children_work_153 (1, 4)
    required_153 envelope_153 pivot_mem_153 child_required_sub_153 child_envelope_sub_153 ?_
  intro b hb
  exact common_sub_153 (mem_commonEnvelope childrenD_153 b hb)

theorem finite_children_work_154 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_154 j) (childrenD_154 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_154 : FiniteTemplate HasSnaky 2 required_154 envelope_154 := by
  refine finite_compose HasSnaky 1 childrenC_154 childrenD_154 finite_children_work_154 (1, 3)
    required_154 envelope_154 pivot_mem_154 child_required_sub_154 child_envelope_sub_154 ?_
  intro b hb
  exact common_sub_154 (mem_commonEnvelope childrenD_154 b hb)

theorem finite_children_work_156 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_156 j) (childrenD_156 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_156 : FiniteTemplate HasSnaky 2 required_156 envelope_156 := by
  refine finite_compose HasSnaky 1 childrenC_156 childrenD_156 finite_children_work_156 (3, 1)
    required_156 envelope_156 pivot_mem_156 child_required_sub_156 child_envelope_sub_156 ?_
  intro b hb
  exact common_sub_156 (mem_commonEnvelope childrenD_156 b hb)

theorem finite_children_work_169 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_169 j) (childrenD_169 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_1 7 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_169 : FiniteTemplate HasSnaky 2 required_169 envelope_169 := by
  refine finite_compose HasSnaky 1 childrenC_169 childrenD_169 finite_children_work_169 (1, 4)
    required_169 envelope_169 pivot_mem_169 child_required_sub_169 child_envelope_sub_169 ?_
  intro b hb
  exact common_sub_169 (mem_commonEnvelope childrenD_169 b hb)

theorem finite_children_work_170 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_170 j) (childrenD_170 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_170 : FiniteTemplate HasSnaky 2 required_170 envelope_170 := by
  refine finite_compose HasSnaky 1 childrenC_170 childrenD_170 finite_children_work_170 (1, 2)
    required_170 envelope_170 pivot_mem_170 child_required_sub_170 child_envelope_sub_170 ?_
  intro b hb
  exact common_sub_170 (mem_commonEnvelope childrenD_170 b hb)

theorem finite_children_work_200 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_200 j) (childrenD_200 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_200 : FiniteTemplate HasSnaky 2 required_200 envelope_200 := by
  refine finite_compose HasSnaky 1 childrenC_200 childrenD_200 finite_children_work_200 (1, 3)
    required_200 envelope_200 pivot_mem_200 child_required_sub_200 child_envelope_sub_200 ?_
  intro b hb
  exact common_sub_200 (mem_commonEnvelope childrenD_200 b hb)

theorem finite_children_work_210 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_210 j) (childrenD_210 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_4 6 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_210 : FiniteTemplate HasSnaky 2 required_210 envelope_210 := by
  refine finite_compose HasSnaky 1 childrenC_210 childrenD_210 finite_children_work_210 (0, 0)
    required_210 envelope_210 pivot_mem_210 child_required_sub_210 child_envelope_sub_210 ?_
  intro b hb
  exact common_sub_210 (mem_commonEnvelope childrenD_210 b hb)

theorem finite_children_work_220 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_220 j) (childrenD_220 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_220 : FiniteTemplate HasSnaky 2 required_220 envelope_220 := by
  refine finite_compose HasSnaky 1 childrenC_220 childrenD_220 finite_children_work_220 (3, 1)
    required_220 envelope_220 pivot_mem_220 child_required_sub_220 child_envelope_sub_220 ?_
  intro b hb
  exact common_sub_220 (mem_commonEnvelope childrenD_220 b hb)

theorem finite_children_work_224 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_224 j) (childrenD_224 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (3, 4)).mono (by decide +kernel)

theorem finite_row_works_224 : FiniteTemplate HasSnaky 2 required_224 envelope_224 := by
  refine finite_compose HasSnaky 1 childrenC_224 childrenD_224 finite_children_work_224 (3, 1)
    required_224 envelope_224 pivot_mem_224 child_required_sub_224 child_envelope_sub_224 ?_
  intro b hb
  exact common_sub_224 (mem_commonEnvelope childrenD_224 b hb)

theorem finite_children_work_244 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_244 j) (childrenD_244 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_244 : FiniteTemplate HasSnaky 2 required_244 envelope_244 := by
  refine finite_compose HasSnaky 1 childrenC_244 childrenD_244 finite_children_work_244 (1, 4)
    required_244 envelope_244 pivot_mem_244 child_required_sub_244 child_envelope_sub_244 ?_
  intro b hb
  exact common_sub_244 (mem_commonEnvelope childrenD_244 b hb)

theorem finite_children_work_281 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_281 j) (childrenD_281 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_281 : FiniteTemplate HasSnaky 2 required_281 envelope_281 := by
  refine finite_compose HasSnaky 1 childrenC_281 childrenD_281 finite_children_work_281 (1, 3)
    required_281 envelope_281 pivot_mem_281 child_required_sub_281 child_envelope_sub_281 ?_
  intro b hb
  exact common_sub_281 (mem_commonEnvelope childrenD_281 b hb)

end FiniteCongruenceChecks.SnakyFinite
