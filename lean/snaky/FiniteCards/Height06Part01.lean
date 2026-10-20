/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_85 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_85 j) (childrenD_85 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_65 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_72 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_85 : FiniteTemplate HasSnaky 6 required_85 envelope_85 := by
  refine finite_compose HasSnaky 5 childrenC_85 childrenD_85 finite_children_work_85 (2, 5)
    required_85 envelope_85 pivot_mem_85 child_required_sub_85 child_envelope_sub_85 ?_
  intro b hb
  exact common_sub_85 (mem_commonEnvelope childrenD_85 b hb)

theorem finite_children_work_95 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_95 j) (childrenD_95 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_95 : FiniteTemplate HasSnaky 6 required_95 envelope_95 := by
  refine finite_compose HasSnaky 5 childrenC_95 childrenD_95 finite_children_work_95 (1, 5)
    required_95 envelope_95 pivot_mem_95 child_required_sub_95 child_envelope_sub_95 ?_
  intro b hb
  exact common_sub_95 (mem_commonEnvelope childrenD_95 b hb)

theorem finite_children_work_110 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_110 j) (childrenD_110 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_28 5 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_100 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_110 : FiniteTemplate HasSnaky 6 required_110 envelope_110 := by
  refine finite_compose HasSnaky 5 childrenC_110 childrenD_110 finite_children_work_110 (3, 4)
    required_110 envelope_110 pivot_mem_110 child_required_sub_110 child_envelope_sub_110 ?_
  intro b hb
  exact common_sub_110 (mem_commonEnvelope childrenD_110 b hb)

theorem finite_children_work_115 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_115 j) (childrenD_115 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_114.mono (by decide +kernel)

theorem finite_row_works_115 : FiniteTemplate HasSnaky 6 required_115 envelope_115 := by
  refine finite_compose HasSnaky 5 childrenC_115 childrenD_115 finite_children_work_115 (3, 2)
    required_115 envelope_115 pivot_mem_115 child_required_sub_115 child_envelope_sub_115 ?_
  intro b hb
  exact common_sub_115 (mem_commonEnvelope childrenD_115 b hb)

theorem finite_children_work_119 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_119 j) (childrenD_119 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_114.mono (by decide +kernel)

theorem finite_row_works_119 : FiniteTemplate HasSnaky 6 required_119 envelope_119 := by
  refine finite_compose HasSnaky 5 childrenC_119 childrenD_119 finite_children_work_119 (2, 3)
    required_119 envelope_119 pivot_mem_119 child_required_sub_119 child_envelope_sub_119 ?_
  intro b hb
  exact common_sub_119 (mem_commonEnvelope childrenD_119 b hb)

theorem finite_children_work_134 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_134 j) (childrenD_134 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 4 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_134 : FiniteTemplate HasSnaky 6 required_134 envelope_134 := by
  refine finite_compose HasSnaky 5 childrenC_134 childrenD_134 finite_children_work_134 (4, 2)
    required_134 envelope_134 pivot_mem_134 child_required_sub_134 child_envelope_sub_134 ?_
  intro b hb
  exact common_sub_134 (mem_commonEnvelope childrenD_134 b hb)

theorem finite_children_work_135 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_135 j) (childrenD_135 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_135 : FiniteTemplate HasSnaky 6 required_135 envelope_135 := by
  refine finite_compose HasSnaky 5 childrenC_135 childrenD_135 finite_children_work_135 (2, 5)
    required_135 envelope_135 pivot_mem_135 child_required_sub_135 child_envelope_sub_135 ?_
  intro b hb
  exact common_sub_135 (mem_commonEnvelope childrenD_135 b hb)

theorem finite_children_work_136 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_136 j) (childrenD_136 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_136 : FiniteTemplate HasSnaky 6 required_136 envelope_136 := by
  refine finite_compose HasSnaky 5 childrenC_136 childrenD_136 finite_children_work_136 (2, 4)
    required_136 envelope_136 pivot_mem_136 child_required_sub_136 child_envelope_sub_136 ?_
  intro b hb
  exact common_sub_136 (mem_commonEnvelope childrenD_136 b hb)

theorem finite_children_work_137 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_137 j) (childrenD_137 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_137 : FiniteTemplate HasSnaky 6 required_137 envelope_137 := by
  refine finite_compose HasSnaky 5 childrenC_137 childrenD_137 finite_children_work_137 (4, 2)
    required_137 envelope_137 pivot_mem_137 child_required_sub_137 child_envelope_sub_137 ?_
  intro b hb
  exact common_sub_137 (mem_commonEnvelope childrenD_137 b hb)

theorem finite_children_work_161 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_161 j) (childrenD_161 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_142.mono (by decide +kernel)

theorem finite_row_works_161 : FiniteTemplate HasSnaky 6 required_161 envelope_161 := by
  refine finite_compose HasSnaky 5 childrenC_161 childrenD_161 finite_children_work_161 (4, 3)
    required_161 envelope_161 pivot_mem_161 child_required_sub_161 child_envelope_sub_161 ?_
  intro b hb
  exact common_sub_161 (mem_commonEnvelope childrenD_161 b hb)

theorem finite_children_work_162 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_162 j) (childrenD_162 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_142.mono (by decide +kernel)

theorem finite_row_works_162 : FiniteTemplate HasSnaky 6 required_162 envelope_162 := by
  refine finite_compose HasSnaky 5 childrenC_162 childrenD_162 finite_children_work_162 (4, 3)
    required_162 envelope_162 pivot_mem_162 child_required_sub_162 child_envelope_sub_162 ?_
  intro b hb
  exact common_sub_162 (mem_commonEnvelope childrenD_162 b hb)

theorem finite_children_work_166 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_166 j) (childrenD_166 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_28 5 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_100 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_166 : FiniteTemplate HasSnaky 6 required_166 envelope_166 := by
  refine finite_compose HasSnaky 5 childrenC_166 childrenD_166 finite_children_work_166 (3, 3)
    required_166 envelope_166 pivot_mem_166 child_required_sub_166 child_envelope_sub_166 ?_
  intro b hb
  exact common_sub_166 (mem_commonEnvelope childrenD_166 b hb)

theorem finite_children_work_167 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_167 j) (childrenD_167 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_152 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_167 : FiniteTemplate HasSnaky 6 required_167 envelope_167 := by
  refine finite_compose HasSnaky 5 childrenC_167 childrenD_167 finite_children_work_167 (3, 2)
    required_167 envelope_167 pivot_mem_167 child_required_sub_167 child_envelope_sub_167 ?_
  intro b hb
  exact common_sub_167 (mem_commonEnvelope childrenD_167 b hb)

theorem finite_children_work_172 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_172 j) (childrenD_172 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_142.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_142 6 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_172 : FiniteTemplate HasSnaky 6 required_172 envelope_172 := by
  refine finite_compose HasSnaky 5 childrenC_172 childrenD_172 finite_children_work_172 (4, 3)
    required_172 envelope_172 pivot_mem_172 child_required_sub_172 child_envelope_sub_172 ?_
  intro b hb
  exact common_sub_172 (mem_commonEnvelope childrenD_172 b hb)

theorem finite_children_work_173 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_173 j) (childrenD_173 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_142.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_142 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_173 : FiniteTemplate HasSnaky 6 required_173 envelope_173 := by
  refine finite_compose HasSnaky 5 childrenC_173 childrenD_173 finite_children_work_173 (4, 3)
    required_173 envelope_173 pivot_mem_173 child_required_sub_173 child_envelope_sub_173 ?_
  intro b hb
  exact common_sub_173 (mem_commonEnvelope childrenD_173 b hb)

theorem finite_children_work_180 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_180 j) (childrenD_180 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 4 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_180 : FiniteTemplate HasSnaky 6 required_180 envelope_180 := by
  refine finite_compose HasSnaky 5 childrenC_180 childrenD_180 finite_children_work_180 (4, 2)
    required_180 envelope_180 pivot_mem_180 child_required_sub_180 child_envelope_sub_180 ?_
  intro b hb
  exact common_sub_180 (mem_commonEnvelope childrenD_180 b hb)

theorem finite_children_work_181 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_181 j) (childrenD_181 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_181 : FiniteTemplate HasSnaky 6 required_181 envelope_181 := by
  refine finite_compose HasSnaky 5 childrenC_181 childrenD_181 finite_children_work_181 (4, 2)
    required_181 envelope_181 pivot_mem_181 child_required_sub_181 child_envelope_sub_181 ?_
  intro b hb
  exact common_sub_181 (mem_commonEnvelope childrenD_181 b hb)

theorem finite_children_work_182 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_182 j) (childrenD_182 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_182 : FiniteTemplate HasSnaky 6 required_182 envelope_182 := by
  refine finite_compose HasSnaky 5 childrenC_182 childrenD_182 finite_children_work_182 (2, 5)
    required_182 envelope_182 pivot_mem_182 child_required_sub_182 child_envelope_sub_182 ?_
  intro b hb
  exact common_sub_182 (mem_commonEnvelope childrenD_182 b hb)

theorem finite_children_work_184 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_184 j) (childrenD_184 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_99 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 6 (5, 5)).mono (by decide +kernel)

theorem finite_row_works_184 : FiniteTemplate HasSnaky 6 required_184 envelope_184 := by
  refine finite_compose HasSnaky 5 childrenC_184 childrenD_184 finite_children_work_184 (2, 3)
    required_184 envelope_184 pivot_mem_184 child_required_sub_184 child_envelope_sub_184 ?_
  intro b hb
  exact common_sub_184 (mem_commonEnvelope childrenD_184 b hb)

theorem finite_children_work_188 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_188 j) (childrenD_188 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 5 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_188 : FiniteTemplate HasSnaky 6 required_188 envelope_188 := by
  refine finite_compose HasSnaky 5 childrenC_188 childrenD_188 finite_children_work_188 (2, 5)
    required_188 envelope_188 pivot_mem_188 child_required_sub_188 child_envelope_sub_188 ?_
  intro b hb
  exact common_sub_188 (mem_commonEnvelope childrenD_188 b hb)

theorem finite_children_work_189 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_189 j) (childrenD_189 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_62 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 6 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 2 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_189 : FiniteTemplate HasSnaky 6 required_189 envelope_189 := by
  refine finite_compose HasSnaky 5 childrenC_189 childrenD_189 finite_children_work_189 (1, 5)
    required_189 envelope_189 pivot_mem_189 child_required_sub_189 child_envelope_sub_189 ?_
  intro b hb
  exact common_sub_189 (mem_commonEnvelope childrenD_189 b hb)

theorem finite_children_work_190 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_190 j) (childrenD_190 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 6 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_190 : FiniteTemplate HasSnaky 6 required_190 envelope_190 := by
  refine finite_compose HasSnaky 5 childrenC_190 childrenD_190 finite_children_work_190 (2, 5)
    required_190 envelope_190 pivot_mem_190 child_required_sub_190 child_envelope_sub_190 ?_
  intro b hb
  exact common_sub_190 (mem_commonEnvelope childrenD_190 b hb)

theorem finite_children_work_192 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_192 j) (childrenD_192 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_186.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_191 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_192 : FiniteTemplate HasSnaky 6 required_192 envelope_192 := by
  refine finite_compose HasSnaky 5 childrenC_192 childrenD_192 finite_children_work_192 (1, 5)
    required_192 envelope_192 pivot_mem_192 child_required_sub_192 child_envelope_sub_192 ?_
  intro b hb
  exact common_sub_192 (mem_commonEnvelope childrenD_192 b hb)

end FiniteCongruenceChecks.SnakyFinite
