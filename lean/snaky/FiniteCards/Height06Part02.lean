/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_193 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_193 j) (childrenD_193 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 5 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_191 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_193 : FiniteTemplate HasSnaky 6 required_193 envelope_193 := by
  refine finite_compose HasSnaky 5 childrenC_193 childrenD_193 finite_children_work_193 (1, 5)
    required_193 envelope_193 pivot_mem_193 child_required_sub_193 child_envelope_sub_193 ?_
  intro b hb
  exact common_sub_193 (mem_commonEnvelope childrenD_193 b hb)

theorem finite_children_work_203 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_203 j) (childrenD_203 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_202 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_203 : FiniteTemplate HasSnaky 6 required_203 envelope_203 := by
  refine finite_compose HasSnaky 5 childrenC_203 childrenD_203 finite_children_work_203 (1, 3)
    required_203 envelope_203 pivot_mem_203 child_required_sub_203 child_envelope_sub_203 ?_
  intro b hb
  exact common_sub_203 (mem_commonEnvelope childrenD_203 b hb)

theorem finite_children_work_217 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_217 j) (childrenD_217 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_217 : FiniteTemplate HasSnaky 6 required_217 envelope_217 := by
  refine finite_compose HasSnaky 5 childrenC_217 childrenD_217 finite_children_work_217 (2, 4)
    required_217 envelope_217 pivot_mem_217 child_required_sub_217 child_envelope_sub_217 ?_
  intro b hb
  exact common_sub_217 (mem_commonEnvelope childrenD_217 b hb)

theorem finite_children_work_238 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_238 j) (childrenD_238 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_238 : FiniteTemplate HasSnaky 6 required_238 envelope_238 := by
  refine finite_compose HasSnaky 5 childrenC_238 childrenD_238 finite_children_work_238 (2, 4)
    required_238 envelope_238 pivot_mem_238 child_required_sub_238 child_envelope_sub_238 ?_
  intro b hb
  exact common_sub_238 (mem_commonEnvelope childrenD_238 b hb)

theorem finite_children_work_248 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_248 j) (childrenD_248 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_127 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_248 : FiniteTemplate HasSnaky 6 required_248 envelope_248 := by
  refine finite_compose HasSnaky 5 childrenC_248 childrenD_248 finite_children_work_248 (2, 5)
    required_248 envelope_248 pivot_mem_248 child_required_sub_248 child_envelope_sub_248 ?_
  intro b hb
  exact common_sub_248 (mem_commonEnvelope childrenD_248 b hb)

theorem finite_children_work_253 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_253 j) (childrenD_253 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_252.mono (by decide +kernel)

theorem finite_row_works_253 : FiniteTemplate HasSnaky 6 required_253 envelope_253 := by
  refine finite_compose HasSnaky 5 childrenC_253 childrenD_253 finite_children_work_253 (4, 3)
    required_253 envelope_253 pivot_mem_253 child_required_sub_253 child_envelope_sub_253 ?_
  intro b hb
  exact common_sub_253 (mem_commonEnvelope childrenD_253 b hb)

theorem finite_children_work_255 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_255 j) (childrenD_255 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_254 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_255 : FiniteTemplate HasSnaky 6 required_255 envelope_255 := by
  refine finite_compose HasSnaky 5 childrenC_255 childrenD_255 finite_children_work_255 (3, 2)
    required_255 envelope_255 pivot_mem_255 child_required_sub_255 child_envelope_sub_255 ?_
  intro b hb
  exact common_sub_255 (mem_commonEnvelope childrenD_255 b hb)

theorem finite_children_work_267 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_267 j) (childrenD_267 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_75 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_266 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_267 : FiniteTemplate HasSnaky 6 required_267 envelope_267 := by
  refine finite_compose HasSnaky 5 childrenC_267 childrenD_267 finite_children_work_267 (2, 5)
    required_267 envelope_267 pivot_mem_267 child_required_sub_267 child_envelope_sub_267 ?_
  intro b hb
  exact common_sub_267 (mem_commonEnvelope childrenD_267 b hb)

theorem finite_children_work_270 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_270 j) (childrenD_270 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_70 7 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_106 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_122 1 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_269 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_270 : FiniteTemplate HasSnaky 6 required_270 envelope_270 := by
  refine finite_compose HasSnaky 5 childrenC_270 childrenD_270 finite_children_work_270 (4, 2)
    required_270 envelope_270 pivot_mem_270 child_required_sub_270 child_envelope_sub_270 ?_
  intro b hb
  exact common_sub_270 (mem_commonEnvelope childrenD_270 b hb)

theorem finite_children_work_275 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_275 j) (childrenD_275 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 3 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_275 : FiniteTemplate HasSnaky 6 required_275 envelope_275 := by
  refine finite_compose HasSnaky 5 childrenC_275 childrenD_275 finite_children_work_275 (4, 2)
    required_275 envelope_275 pivot_mem_275 child_required_sub_275 child_envelope_sub_275 ?_
  intro b hb
  exact common_sub_275 (mem_commonEnvelope childrenD_275 b hb)

theorem finite_children_work_283 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_283 j) (childrenD_283 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_282 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_283 : FiniteTemplate HasSnaky 6 required_283 envelope_283 := by
  refine finite_compose HasSnaky 5 childrenC_283 childrenD_283 finite_children_work_283 (2, 2)
    required_283 envelope_283 pivot_mem_283 child_required_sub_283 child_envelope_sub_283 ?_
  intro b hb
  exact common_sub_283 (mem_commonEnvelope childrenD_283 b hb)

theorem finite_children_work_284 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_284 j) (childrenD_284 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_75 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_284 : FiniteTemplate HasSnaky 6 required_284 envelope_284 := by
  refine finite_compose HasSnaky 5 childrenC_284 childrenD_284 finite_children_work_284 (1, 3)
    required_284 envelope_284 pivot_mem_284 child_required_sub_284 child_envelope_sub_284 ?_
  intro b hb
  exact common_sub_284 (mem_commonEnvelope childrenD_284 b hb)

theorem finite_children_work_287 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_287 j) (childrenD_287 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_169 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_230 5 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_287 : FiniteTemplate HasSnaky 6 required_287 envelope_287 := by
  refine finite_compose HasSnaky 5 childrenC_287 childrenD_287 finite_children_work_287 (1, 6)
    required_287 envelope_287 pivot_mem_287 child_required_sub_287 child_envelope_sub_287 ?_
  intro b hb
  exact common_sub_287 (mem_commonEnvelope childrenD_287 b hb)

theorem finite_children_work_292 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_292 j) (childrenD_292 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_214.mono (by decide +kernel)

theorem finite_row_works_292 : FiniteTemplate HasSnaky 6 required_292 envelope_292 := by
  refine finite_compose HasSnaky 5 childrenC_292 childrenD_292 finite_children_work_292 (4, 3)
    required_292 envelope_292 pivot_mem_292 child_required_sub_292 child_envelope_sub_292 ?_
  intro b hb
  exact common_sub_292 (mem_commonEnvelope childrenD_292 b hb)

theorem finite_children_work_300 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_300 j) (childrenD_300 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_128 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_155 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_300 : FiniteTemplate HasSnaky 6 required_300 envelope_300 := by
  refine finite_compose HasSnaky 5 childrenC_300 childrenD_300 finite_children_work_300 (2, 5)
    required_300 envelope_300 pivot_mem_300 child_required_sub_300 child_envelope_sub_300 ?_
  intro b hb
  exact common_sub_300 (mem_commonEnvelope childrenD_300 b hb)

theorem finite_children_work_302 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_302 j) (childrenD_302 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 7 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_214 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_302 : FiniteTemplate HasSnaky 6 required_302 envelope_302 := by
  refine finite_compose HasSnaky 5 childrenC_302 childrenD_302 finite_children_work_302 (5, 3)
    required_302 envelope_302 pivot_mem_302 child_required_sub_302 child_envelope_sub_302 ?_
  intro b hb
  exact common_sub_302 (mem_commonEnvelope childrenD_302 b hb)

theorem finite_children_work_303 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_303 j) (childrenD_303 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_55 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_234 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_303 : FiniteTemplate HasSnaky 6 required_303 envelope_303 := by
  refine finite_compose HasSnaky 5 childrenC_303 childrenD_303 finite_children_work_303 (3, 4)
    required_303 envelope_303 pivot_mem_303 child_required_sub_303 child_envelope_sub_303 ?_
  intro b hb
  exact common_sub_303 (mem_commonEnvelope childrenD_303 b hb)

theorem finite_children_work_313 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_313 j) (childrenD_313 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_312 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_313 : FiniteTemplate HasSnaky 6 required_313 envelope_313 := by
  refine finite_compose HasSnaky 5 childrenC_313 childrenD_313 finite_children_work_313 (3, 0)
    required_313 envelope_313 pivot_mem_313 child_required_sub_313 child_envelope_sub_313 ?_
  intro b hb
  exact common_sub_313 (mem_commonEnvelope childrenD_313 b hb)

theorem finite_children_work_315 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_315 j) (childrenD_315 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_315 : FiniteTemplate HasSnaky 6 required_315 envelope_315 := by
  refine finite_compose HasSnaky 5 childrenC_315 childrenD_315 finite_children_work_315 (1, 4)
    required_315 envelope_315 pivot_mem_315 child_required_sub_315 child_envelope_sub_315 ?_
  intro b hb
  exact common_sub_315 (mem_commonEnvelope childrenD_315 b hb)

theorem finite_children_work_316 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_316 j) (childrenD_316 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_316 : FiniteTemplate HasSnaky 6 required_316 envelope_316 := by
  refine finite_compose HasSnaky 5 childrenC_316 childrenD_316 finite_children_work_316 (1, 2)
    required_316 envelope_316 pivot_mem_316 child_required_sub_316 child_envelope_sub_316 ?_
  intro b hb
  exact common_sub_316 (mem_commonEnvelope childrenD_316 b hb)

theorem finite_children_work_331_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_331_i1 j) (childrenD_331_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 6 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_331_i1 : FiniteTemplate HasSnaky 4 required_331_i1 envelope_331_i1 := by
  refine finite_compose HasSnaky 3 childrenC_331_i1 childrenD_331_i1 finite_children_work_331_i1 (3, 5)
    required_331_i1 envelope_331_i1 pivot_mem_331_i1 child_required_sub_331_i1 child_envelope_sub_331_i1 ?_
  intro b hb
  exact common_sub_331_i1 (mem_commonEnvelope childrenD_331_i1 b hb)

theorem finite_children_work_331_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_331_i0 j) (childrenD_331_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_331_i1.mono (by decide +kernel)

theorem finite_row_works_331_i0 : FiniteTemplate HasSnaky 5 required_331_i0 envelope_331_i0 := by
  refine finite_compose HasSnaky 4 childrenC_331_i0 childrenD_331_i0 finite_children_work_331_i0 (3, 2)
    required_331_i0 envelope_331_i0 pivot_mem_331_i0 child_required_sub_331_i0 child_envelope_sub_331_i0 ?_
  intro b hb
  exact common_sub_331_i0 (mem_commonEnvelope childrenD_331_i0 b hb)

theorem finite_children_work_331 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_331 j) (childrenD_331 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_331_i0.mono (by decide +kernel)

theorem finite_row_works_331 : FiniteTemplate HasSnaky 6 required_331 envelope_331 := by
  refine finite_compose HasSnaky 5 childrenC_331 childrenD_331 finite_children_work_331 (3, 4)
    required_331 envelope_331 pivot_mem_331 child_required_sub_331 child_envelope_sub_331 ?_
  intro b hb
  exact common_sub_331 (mem_commonEnvelope childrenD_331 b hb)

end FiniteCongruenceChecks.SnakyFinite
