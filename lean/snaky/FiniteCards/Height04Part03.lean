/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_149 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_149 j) (childrenD_149 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_124.mono (by decide +kernel)

theorem finite_row_works_149 : FiniteTemplate HasSnaky 4 required_149 envelope_149 := by
  refine finite_compose HasSnaky 3 childrenC_149 childrenD_149 finite_children_work_149 (1, 3)
    required_149 envelope_149 pivot_mem_149 child_required_sub_149 child_envelope_sub_149 ?_
  intro b hb
  exact common_sub_149 (mem_commonEnvelope childrenD_149 b hb)

theorem finite_children_work_150 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_150 j) (childrenD_150 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_150 : FiniteTemplate HasSnaky 4 required_150 envelope_150 := by
  refine finite_compose HasSnaky 3 childrenC_150 childrenD_150 finite_children_work_150 (1, 2)
    required_150 envelope_150 pivot_mem_150 child_required_sub_150 child_envelope_sub_150 ?_
  intro b hb
  exact common_sub_150 (mem_commonEnvelope childrenD_150 b hb)

theorem finite_children_work_151 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_151 j) (childrenD_151 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_151 : FiniteTemplate HasSnaky 4 required_151 envelope_151 := by
  refine finite_compose HasSnaky 3 childrenC_151 childrenD_151 finite_children_work_151 (4, 2)
    required_151 envelope_151 pivot_mem_151 child_required_sub_151 child_envelope_sub_151 ?_
  intro b hb
  exact common_sub_151 (mem_commonEnvelope childrenD_151 b hb)

theorem finite_children_work_165 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_165 j) (childrenD_165 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_64 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_165 : FiniteTemplate HasSnaky 4 required_165 envelope_165 := by
  refine finite_compose HasSnaky 3 childrenC_165 childrenD_165 finite_children_work_165 (4, 3)
    required_165 envelope_165 pivot_mem_165 child_required_sub_165 child_envelope_sub_165 ?_
  intro b hb
  exact common_sub_165 (mem_commonEnvelope childrenD_165 b hb)

theorem finite_children_work_168 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_168 j) (childrenD_168 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_131 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_168 : FiniteTemplate HasSnaky 4 required_168 envelope_168 := by
  refine finite_compose HasSnaky 3 childrenC_168 childrenD_168 finite_children_work_168 (2, 2)
    required_168 envelope_168 pivot_mem_168 child_required_sub_168 child_envelope_sub_168 ?_
  intro b hb
  exact common_sub_168 (mem_commonEnvelope childrenD_168 b hb)

theorem finite_children_work_178 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_178 j) (childrenD_178 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_177 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_178 : FiniteTemplate HasSnaky 4 required_178 envelope_178 := by
  refine finite_compose HasSnaky 3 childrenC_178 childrenD_178 finite_children_work_178 (1, 1)
    required_178 envelope_178 pivot_mem_178 child_required_sub_178 child_envelope_sub_178 ?_
  intro b hb
  exact common_sub_178 (mem_commonEnvelope childrenD_178 b hb)

theorem finite_children_work_185 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_185 j) (childrenD_185 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_113.mono (by decide +kernel)

theorem finite_row_works_185 : FiniteTemplate HasSnaky 4 required_185 envelope_185 := by
  refine finite_compose HasSnaky 3 childrenC_185 childrenD_185 finite_children_work_185 (1, 4)
    required_185 envelope_185 pivot_mem_185 child_required_sub_185 child_envelope_sub_185 ?_
  intro b hb
  exact common_sub_185 (mem_commonEnvelope childrenD_185 b hb)

theorem finite_children_work_194 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_194 j) (childrenD_194 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_194 : FiniteTemplate HasSnaky 4 required_194 envelope_194 := by
  refine finite_compose HasSnaky 3 childrenC_194 childrenD_194 finite_children_work_194 (1, 4)
    required_194 envelope_194 pivot_mem_194 child_required_sub_194 child_envelope_sub_194 ?_
  intro b hb
  exact common_sub_194 (mem_commonEnvelope childrenD_194 b hb)

theorem finite_children_work_195 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_195 j) (childrenD_195 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_195 : FiniteTemplate HasSnaky 4 required_195 envelope_195 := by
  refine finite_compose HasSnaky 3 childrenC_195 childrenD_195 finite_children_work_195 (1, 4)
    required_195 envelope_195 pivot_mem_195 child_required_sub_195 child_envelope_sub_195 ?_
  intro b hb
  exact common_sub_195 (mem_commonEnvelope childrenD_195 b hb)

theorem finite_children_work_196 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_196 j) (childrenD_196 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_143 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_196 : FiniteTemplate HasSnaky 4 required_196 envelope_196 := by
  refine finite_compose HasSnaky 3 childrenC_196 childrenD_196 finite_children_work_196 (3, 0)
    required_196 envelope_196 pivot_mem_196 child_required_sub_196 child_envelope_sub_196 ?_
  intro b hb
  exact common_sub_196 (mem_commonEnvelope childrenD_196 b hb)

theorem finite_children_work_199 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_199 j) (childrenD_199 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_198.mono (by decide +kernel)

theorem finite_row_works_199 : FiniteTemplate HasSnaky 4 required_199 envelope_199 := by
  refine finite_compose HasSnaky 3 childrenC_199 childrenD_199 finite_children_work_199 (1, 1)
    required_199 envelope_199 pivot_mem_199 child_required_sub_199 child_envelope_sub_199 ?_
  intro b hb
  exact common_sub_199 (mem_commonEnvelope childrenD_199 b hb)

theorem finite_children_work_206 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_206 j) (childrenD_206 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_205.mono (by decide +kernel)

theorem finite_row_works_206 : FiniteTemplate HasSnaky 4 required_206 envelope_206 := by
  refine finite_compose HasSnaky 3 childrenC_206 childrenD_206 finite_children_work_206 (1, 1)
    required_206 envelope_206 pivot_mem_206 child_required_sub_206 child_envelope_sub_206 ?_
  intro b hb
  exact common_sub_206 (mem_commonEnvelope childrenD_206 b hb)

theorem finite_children_work_208 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_208 j) (childrenD_208 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_207 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_208 : FiniteTemplate HasSnaky 4 required_208 envelope_208 := by
  refine finite_compose HasSnaky 3 childrenC_208 childrenD_208 finite_children_work_208 (4, 0)
    required_208 envelope_208 pivot_mem_208 child_required_sub_208 child_envelope_sub_208 ?_
  intro b hb
  exact common_sub_208 (mem_commonEnvelope childrenD_208 b hb)

theorem finite_children_work_213 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_213 j) (childrenD_213 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_212 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_213 : FiniteTemplate HasSnaky 4 required_213 envelope_213 := by
  refine finite_compose HasSnaky 3 childrenC_213 childrenD_213 finite_children_work_213 (1, 4)
    required_213 envelope_213 pivot_mem_213 child_required_sub_213 child_envelope_sub_213 ?_
  intro b hb
  exact common_sub_213 (mem_commonEnvelope childrenD_213 b hb)

theorem finite_children_work_216 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_216 j) (childrenD_216 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_54 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_216 : FiniteTemplate HasSnaky 4 required_216 envelope_216 := by
  refine finite_compose HasSnaky 3 childrenC_216 childrenD_216 finite_children_work_216 (4, 3)
    required_216 envelope_216 pivot_mem_216 child_required_sub_216 child_envelope_sub_216 ?_
  intro b hb
  exact common_sub_216 (mem_commonEnvelope childrenD_216 b hb)

theorem finite_children_work_227 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_227 j) (childrenD_227 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_227 : FiniteTemplate HasSnaky 4 required_227 envelope_227 := by
  refine finite_compose HasSnaky 3 childrenC_227 childrenD_227 finite_children_work_227 (1, 4)
    required_227 envelope_227 pivot_mem_227 child_required_sub_227 child_envelope_sub_227 ?_
  intro b hb
  exact common_sub_227 (mem_commonEnvelope childrenD_227 b hb)

theorem finite_children_work_229 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_229 j) (childrenD_229 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_215.mono (by decide +kernel)

theorem finite_row_works_229 : FiniteTemplate HasSnaky 4 required_229 envelope_229 := by
  refine finite_compose HasSnaky 3 childrenC_229 childrenD_229 finite_children_work_229 (3, 3)
    required_229 envelope_229 pivot_mem_229 child_required_sub_229 child_envelope_sub_229 ?_
  intro b hb
  exact common_sub_229 (mem_commonEnvelope childrenD_229 b hb)

theorem finite_children_work_235 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_235 j) (childrenD_235 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_226 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_235 : FiniteTemplate HasSnaky 4 required_235 envelope_235 := by
  refine finite_compose HasSnaky 3 childrenC_235 childrenD_235 finite_children_work_235 (2, 1)
    required_235 envelope_235 pivot_mem_235 child_required_sub_235 child_envelope_sub_235 ?_
  intro b hb
  exact common_sub_235 (mem_commonEnvelope childrenD_235 b hb)

theorem finite_children_work_240 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_240 j) (childrenD_240 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_240 : FiniteTemplate HasSnaky 4 required_240 envelope_240 := by
  refine finite_compose HasSnaky 3 childrenC_240 childrenD_240 finite_children_work_240 (2, 3)
    required_240 envelope_240 pivot_mem_240 child_required_sub_240 child_envelope_sub_240 ?_
  intro b hb
  exact common_sub_240 (mem_commonEnvelope childrenD_240 b hb)

theorem finite_children_work_242 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_242 j) (childrenD_242 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_69 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_242 : FiniteTemplate HasSnaky 4 required_242 envelope_242 := by
  refine finite_compose HasSnaky 3 childrenC_242 childrenD_242 finite_children_work_242 (4, 2)
    required_242 envelope_242 pivot_mem_242 child_required_sub_242 child_envelope_sub_242 ?_
  intro b hb
  exact common_sub_242 (mem_commonEnvelope childrenD_242 b hb)

theorem finite_children_work_259 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_259 j) (childrenD_259 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_159 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_259 : FiniteTemplate HasSnaky 4 required_259 envelope_259 := by
  refine finite_compose HasSnaky 3 childrenC_259 childrenD_259 finite_children_work_259 (2, 4)
    required_259 envelope_259 pivot_mem_259 child_required_sub_259 child_envelope_sub_259 ?_
  intro b hb
  exact common_sub_259 (mem_commonEnvelope childrenD_259 b hb)

theorem finite_children_work_263 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_263 j) (childrenD_263 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_263 : FiniteTemplate HasSnaky 4 required_263 envelope_263 := by
  refine finite_compose HasSnaky 3 childrenC_263 childrenD_263 finite_children_work_263 (3, 4)
    required_263 envelope_263 pivot_mem_263 child_required_sub_263 child_envelope_sub_263 ?_
  intro b hb
  exact common_sub_263 (mem_commonEnvelope childrenD_263 b hb)

theorem finite_children_work_264 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_264 j) (childrenD_264 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_201 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_264 : FiniteTemplate HasSnaky 4 required_264 envelope_264 := by
  refine finite_compose HasSnaky 3 childrenC_264 childrenD_264 finite_children_work_264 (1, 4)
    required_264 envelope_264 pivot_mem_264 child_required_sub_264 child_envelope_sub_264 ?_
  intro b hb
  exact common_sub_264 (mem_commonEnvelope childrenD_264 b hb)

theorem finite_children_work_266 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_266 j) (childrenD_266 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_113 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_266 : FiniteTemplate HasSnaky 4 required_266 envelope_266 := by
  refine finite_compose HasSnaky 3 childrenC_266 childrenD_266 finite_children_work_266 (0, 6)
    required_266 envelope_266 pivot_mem_266 child_required_sub_266 child_envelope_sub_266 ?_
  intro b hb
  exact common_sub_266 (mem_commonEnvelope childrenD_266 b hb)

end FiniteCongruenceChecks.SnakyFinite
