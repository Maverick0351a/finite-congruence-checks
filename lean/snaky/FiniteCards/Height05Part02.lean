/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_183 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_183 j) (childrenD_183 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_178 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_183 : FiniteTemplate HasSnaky 5 required_183 envelope_183 := by
  refine finite_compose HasSnaky 4 childrenC_183 childrenD_183 finite_children_work_183 (4, 2)
    required_183 envelope_183 pivot_mem_183 child_required_sub_183 child_envelope_sub_183 ?_
  intro b hb
  exact common_sub_183 (mem_commonEnvelope childrenD_183 b hb)

theorem finite_children_work_186 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_186 j) (childrenD_186 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_185 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_186 : FiniteTemplate HasSnaky 5 required_186 envelope_186 := by
  refine finite_compose HasSnaky 4 childrenC_186 childrenD_186 finite_children_work_186 (1, 1)
    required_186 envelope_186 pivot_mem_186 child_required_sub_186 child_envelope_sub_186 ?_
  intro b hb
  exact common_sub_186 (mem_commonEnvelope childrenD_186 b hb)

theorem finite_children_work_187 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_187 j) (childrenD_187 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_7 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_185 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_187 : FiniteTemplate HasSnaky 5 required_187 envelope_187 := by
  refine finite_compose HasSnaky 4 childrenC_187 childrenD_187 finite_children_work_187 (0, 6)
    required_187 envelope_187 pivot_mem_187 child_required_sub_187 child_envelope_sub_187 ?_
  intro b hb
  exact common_sub_187 (mem_commonEnvelope childrenD_187 b hb)

theorem finite_children_work_191 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_191 j) (childrenD_191 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_89 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_191 : FiniteTemplate HasSnaky 5 required_191 envelope_191 := by
  refine finite_compose HasSnaky 4 childrenC_191 childrenD_191 finite_children_work_191 (0, 1)
    required_191 envelope_191 pivot_mem_191 child_required_sub_191 child_envelope_sub_191 ?_
  intro b hb
  exact common_sub_191 (mem_commonEnvelope childrenD_191 b hb)

theorem finite_children_work_197 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_197 j) (childrenD_197 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_196.mono (by decide +kernel)

theorem finite_row_works_197 : FiniteTemplate HasSnaky 5 required_197 envelope_197 := by
  refine finite_compose HasSnaky 4 childrenC_197 childrenD_197 finite_children_work_197 (4, 1)
    required_197 envelope_197 pivot_mem_197 child_required_sub_197 child_envelope_sub_197 ?_
  intro b hb
  exact common_sub_197 (mem_commonEnvelope childrenD_197 b hb)

theorem finite_children_work_202 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_202 j) (childrenD_202 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_202 : FiniteTemplate HasSnaky 5 required_202 envelope_202 := by
  refine finite_compose HasSnaky 4 childrenC_202 childrenD_202 finite_children_work_202 (3, 2)
    required_202 envelope_202 pivot_mem_202 child_required_sub_202 child_envelope_sub_202 ?_
  intro b hb
  exact common_sub_202 (mem_commonEnvelope childrenD_202 b hb)

theorem finite_children_work_211 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_211 j) (childrenD_211 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_151 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_211 : FiniteTemplate HasSnaky 5 required_211 envelope_211 := by
  refine finite_compose HasSnaky 4 childrenC_211 childrenD_211 finite_children_work_211 (3, 5)
    required_211 envelope_211 pivot_mem_211 child_required_sub_211 child_envelope_sub_211 ?_
  intro b hb
  exact common_sub_211 (mem_commonEnvelope childrenD_211 b hb)

theorem finite_children_work_214 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_214 j) (childrenD_214 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_213 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_214 : FiniteTemplate HasSnaky 5 required_214 envelope_214 := by
  refine finite_compose HasSnaky 4 childrenC_214 childrenD_214 finite_children_work_214 (3, 4)
    required_214 envelope_214 pivot_mem_214 child_required_sub_214 child_envelope_sub_214 ?_
  intro b hb
  exact common_sub_214 (mem_commonEnvelope childrenD_214 b hb)

theorem finite_children_work_225 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_225 j) (childrenD_225 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 5 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_225 : FiniteTemplate HasSnaky 5 required_225 envelope_225 := by
  refine finite_compose HasSnaky 4 childrenC_225 childrenD_225 finite_children_work_225 (1, 5)
    required_225 envelope_225 pivot_mem_225 child_required_sub_225 child_envelope_sub_225 ?_
  intro b hb
  exact common_sub_225 (mem_commonEnvelope childrenD_225 b hb)

theorem finite_children_work_228 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_228 j) (childrenD_228 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_227 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_228 : FiniteTemplate HasSnaky 5 required_228 envelope_228 := by
  refine finite_compose HasSnaky 4 childrenC_228 childrenD_228 finite_children_work_228 (3, 2)
    required_228 envelope_228 pivot_mem_228 child_required_sub_228 child_envelope_sub_228 ?_
  intro b hb
  exact common_sub_228 (mem_commonEnvelope childrenD_228 b hb)

theorem finite_children_work_230 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_230 j) (childrenD_230 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_229 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_230 : FiniteTemplate HasSnaky 5 required_230 envelope_230 := by
  refine finite_compose HasSnaky 4 childrenC_230 childrenD_230 finite_children_work_230 (4, 2)
    required_230 envelope_230 pivot_mem_230 child_required_sub_230 child_envelope_sub_230 ?_
  intro b hb
  exact common_sub_230 (mem_commonEnvelope childrenD_230 b hb)

theorem finite_children_work_231 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_231 j) (childrenD_231 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_231 : FiniteTemplate HasSnaky 5 required_231 envelope_231 := by
  refine finite_compose HasSnaky 4 childrenC_231 childrenD_231 finite_children_work_231 (4, 3)
    required_231 envelope_231 pivot_mem_231 child_required_sub_231 child_envelope_sub_231 ?_
  intro b hb
  exact common_sub_231 (mem_commonEnvelope childrenD_231 b hb)

theorem finite_children_work_232 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_232 j) (childrenD_232 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 5 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_232 : FiniteTemplate HasSnaky 5 required_232 envelope_232 := by
  refine finite_compose HasSnaky 4 childrenC_232 childrenD_232 finite_children_work_232 (1, 4)
    required_232 envelope_232 pivot_mem_232 child_required_sub_232 child_envelope_sub_232 ?_
  intro b hb
  exact common_sub_232 (mem_commonEnvelope childrenD_232 b hb)

theorem finite_children_work_233 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_233 j) (childrenD_233 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 3 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_233 : FiniteTemplate HasSnaky 5 required_233 envelope_233 := by
  refine finite_compose HasSnaky 4 childrenC_233 childrenD_233 finite_children_work_233 (4, 1)
    required_233 envelope_233 pivot_mem_233 child_required_sub_233 child_envelope_sub_233 ?_
  intro b hb
  exact common_sub_233 (mem_commonEnvelope childrenD_233 b hb)

theorem finite_children_work_234 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_234 j) (childrenD_234 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_148 2 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_234 : FiniteTemplate HasSnaky 5 required_234 envelope_234 := by
  refine finite_compose HasSnaky 4 childrenC_234 childrenD_234 finite_children_work_234 (2, 1)
    required_234 envelope_234 pivot_mem_234 child_required_sub_234 child_envelope_sub_234 ?_
  intro b hb
  exact common_sub_234 (mem_commonEnvelope childrenD_234 b hb)

theorem finite_children_work_237 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_237 j) (childrenD_237 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_10.mono (by decide +kernel)

theorem finite_row_works_237 : FiniteTemplate HasSnaky 5 required_237 envelope_237 := by
  refine finite_compose HasSnaky 4 childrenC_237 childrenD_237 finite_children_work_237 (0, 1)
    required_237 envelope_237 pivot_mem_237 child_required_sub_237 child_envelope_sub_237 ?_
  intro b hb
  exact common_sub_237 (mem_commonEnvelope childrenD_237 b hb)

theorem finite_children_work_241 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_241 j) (childrenD_241 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_91 2 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_241 : FiniteTemplate HasSnaky 5 required_241 envelope_241 := by
  refine finite_compose HasSnaky 4 childrenC_241 childrenD_241 finite_children_work_241 (2, 1)
    required_241 envelope_241 pivot_mem_241 child_required_sub_241 child_envelope_sub_241 ?_
  intro b hb
  exact common_sub_241 (mem_commonEnvelope childrenD_241 b hb)

theorem finite_children_work_243 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_243 j) (childrenD_243 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_242.mono (by decide +kernel)

theorem finite_row_works_243 : FiniteTemplate HasSnaky 5 required_243 envelope_243 := by
  refine finite_compose HasSnaky 4 childrenC_243 childrenD_243 finite_children_work_243 (2, 2)
    required_243 envelope_243 pivot_mem_243 child_required_sub_243 child_envelope_sub_243 ?_
  intro b hb
  exact common_sub_243 (mem_commonEnvelope childrenD_243 b hb)

theorem finite_children_work_249 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_249 j) (childrenD_249 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_249 : FiniteTemplate HasSnaky 5 required_249 envelope_249 := by
  refine finite_compose HasSnaky 4 childrenC_249 childrenD_249 finite_children_work_249 (4, 2)
    required_249 envelope_249 pivot_mem_249 child_required_sub_249 child_envelope_sub_249 ?_
  intro b hb
  exact common_sub_249 (mem_commonEnvelope childrenD_249 b hb)

theorem finite_children_work_250 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_250 j) (childrenD_250 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_195.mono (by decide +kernel)

theorem finite_row_works_250 : FiniteTemplate HasSnaky 5 required_250 envelope_250 := by
  refine finite_compose HasSnaky 4 childrenC_250 childrenD_250 finite_children_work_250 (1, 2)
    required_250 envelope_250 pivot_mem_250 child_required_sub_250 child_envelope_sub_250 ?_
  intro b hb
  exact common_sub_250 (mem_commonEnvelope childrenD_250 b hb)

theorem finite_children_work_252 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_252 j) (childrenD_252 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_55 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_91 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_252 : FiniteTemplate HasSnaky 5 required_252 envelope_252 := by
  refine finite_compose HasSnaky 4 childrenC_252 childrenD_252 finite_children_work_252 (2, 4)
    required_252 envelope_252 pivot_mem_252 child_required_sub_252 child_envelope_sub_252 ?_
  intro b hb
  exact common_sub_252 (mem_commonEnvelope childrenD_252 b hb)

theorem finite_children_work_254 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_254 j) (childrenD_254 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_75.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_103 6 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_254 : FiniteTemplate HasSnaky 5 required_254 envelope_254 := by
  refine finite_compose HasSnaky 4 childrenC_254 childrenD_254 finite_children_work_254 (1, 5)
    required_254 envelope_254 pivot_mem_254 child_required_sub_254 child_envelope_sub_254 ?_
  intro b hb
  exact common_sub_254 (mem_commonEnvelope childrenD_254 b hb)

theorem finite_children_work_260 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_260 j) (childrenD_260 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_208 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_260 : FiniteTemplate HasSnaky 5 required_260 envelope_260 := by
  refine finite_compose HasSnaky 4 childrenC_260 childrenD_260 finite_children_work_260 (3, 0)
    required_260 envelope_260 pivot_mem_260 child_required_sub_260 child_envelope_sub_260 ?_
  intro b hb
  exact common_sub_260 (mem_commonEnvelope childrenD_260 b hb)

theorem finite_children_work_265 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_265 j) (childrenD_265 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_93 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_265 : FiniteTemplate HasSnaky 5 required_265 envelope_265 := by
  refine finite_compose HasSnaky 4 childrenC_265 childrenD_265 finite_children_work_265 (1, 4)
    required_265 envelope_265 pivot_mem_265 child_required_sub_265 child_envelope_sub_265 ?_
  intro b hb
  exact common_sub_265 (mem_commonEnvelope childrenD_265 b hb)

end FiniteCongruenceChecks.SnakyFinite
