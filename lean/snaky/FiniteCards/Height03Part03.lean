/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_221 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_221 j) (childrenD_221 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_220 4 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_221 : FiniteTemplate HasSnaky 3 required_221 envelope_221 := by
  refine finite_compose HasSnaky 2 childrenC_221 childrenD_221 finite_children_work_221 (1, 3)
    required_221 envelope_221 pivot_mem_221 child_required_sub_221 child_envelope_sub_221 ?_
  intro b hb
  exact common_sub_221 (mem_commonEnvelope childrenD_221 b hb)

theorem finite_children_work_222 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_222 j) (childrenD_222 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_220.mono (by decide +kernel)

theorem finite_row_works_222 : FiniteTemplate HasSnaky 3 required_222 envelope_222 := by
  refine finite_compose HasSnaky 2 childrenC_222 childrenD_222 finite_children_work_222 (2, 1)
    required_222 envelope_222 pivot_mem_222 child_required_sub_222 child_envelope_sub_222 ?_
  intro b hb
  exact common_sub_222 (mem_commonEnvelope childrenD_222 b hb)

theorem finite_children_work_223 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_223 j) (childrenD_223 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_223 : FiniteTemplate HasSnaky 3 required_223 envelope_223 := by
  refine finite_compose HasSnaky 2 childrenC_223 childrenD_223 finite_children_work_223 (3, 0)
    required_223 envelope_223 pivot_mem_223 child_required_sub_223 child_envelope_sub_223 ?_
  intro b hb
  exact common_sub_223 (mem_commonEnvelope childrenD_223 b hb)

theorem finite_children_work_226 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_226 j) (childrenD_226 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_226 : FiniteTemplate HasSnaky 3 required_226 envelope_226 := by
  refine finite_compose HasSnaky 2 childrenC_226 childrenD_226 finite_children_work_226 (4, 1)
    required_226 envelope_226 pivot_mem_226 child_required_sub_226 child_envelope_sub_226 ?_
  intro b hb
  exact common_sub_226 (mem_commonEnvelope childrenD_226 b hb)

theorem finite_children_work_236 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_236 j) (childrenD_236 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_236 : FiniteTemplate HasSnaky 3 required_236 envelope_236 := by
  refine finite_compose HasSnaky 2 childrenC_236 childrenD_236 finite_children_work_236 (1, 5)
    required_236 envelope_236 pivot_mem_236 child_required_sub_236 child_envelope_sub_236 ?_
  intro b hb
  exact common_sub_236 (mem_commonEnvelope childrenD_236 b hb)

theorem finite_children_work_239 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_239 j) (childrenD_239 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 6 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_25 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_239 : FiniteTemplate HasSnaky 3 required_239 envelope_239 := by
  refine finite_compose HasSnaky 2 childrenC_239 childrenD_239 finite_children_work_239 (3, 1)
    required_239 envelope_239 pivot_mem_239 child_required_sub_239 child_envelope_sub_239 ?_
  intro b hb
  exact common_sub_239 (mem_commonEnvelope childrenD_239 b hb)

theorem finite_children_work_245 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_245 j) (childrenD_245 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_245 : FiniteTemplate HasSnaky 3 required_245 envelope_245 := by
  refine finite_compose HasSnaky 2 childrenC_245 childrenD_245 finite_children_work_245 (1, 4)
    required_245 envelope_245 pivot_mem_245 child_required_sub_245 child_envelope_sub_245 ?_
  intro b hb
  exact common_sub_245 (mem_commonEnvelope childrenD_245 b hb)

theorem finite_children_work_246 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_246 j) (childrenD_246 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_25 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_246 : FiniteTemplate HasSnaky 3 required_246 envelope_246 := by
  refine finite_compose HasSnaky 2 childrenC_246 childrenD_246 finite_children_work_246 (1, 4)
    required_246 envelope_246 pivot_mem_246 child_required_sub_246 child_envelope_sub_246 ?_
  intro b hb
  exact common_sub_246 (mem_commonEnvelope childrenD_246 b hb)

theorem finite_children_work_247 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_247 j) (childrenD_247 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_247 : FiniteTemplate HasSnaky 3 required_247 envelope_247 := by
  refine finite_compose HasSnaky 2 childrenC_247 childrenD_247 finite_children_work_247 (3, 4)
    required_247 envelope_247 pivot_mem_247 child_required_sub_247 child_envelope_sub_247 ?_
  intro b hb
  exact common_sub_247 (mem_commonEnvelope childrenD_247 b hb)

theorem finite_children_work_251 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_251 j) (childrenD_251 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_224 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_251 : FiniteTemplate HasSnaky 3 required_251 envelope_251 := by
  refine finite_compose HasSnaky 2 childrenC_251 childrenD_251 finite_children_work_251 (4, 2)
    required_251 envelope_251 pivot_mem_251 child_required_sub_251 child_envelope_sub_251 ?_
  intro b hb
  exact common_sub_251 (mem_commonEnvelope childrenD_251 b hb)

theorem finite_children_work_261 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_261 j) (childrenD_261 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact finite_row_works_129.mono (by decide +kernel)

theorem finite_row_works_261 : FiniteTemplate HasSnaky 3 required_261 envelope_261 := by
  refine finite_compose HasSnaky 2 childrenC_261 childrenD_261 finite_children_work_261 (1, 3)
    required_261 envelope_261 pivot_mem_261 child_required_sub_261 child_envelope_sub_261 ?_
  intro b hb
  exact common_sub_261 (mem_commonEnvelope childrenD_261 b hb)

theorem finite_children_work_262 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_262 j) (childrenD_262 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_66 3 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_262 : FiniteTemplate HasSnaky 3 required_262 envelope_262 := by
  refine finite_compose HasSnaky 2 childrenC_262 childrenD_262 finite_children_work_262 (1, 1)
    required_262 envelope_262 pivot_mem_262 child_required_sub_262 child_envelope_sub_262 ?_
  intro b hb
  exact common_sub_262 (mem_commonEnvelope childrenD_262 b hb)

theorem finite_children_work_280 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_280 j) (childrenD_280 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_280 : FiniteTemplate HasSnaky 3 required_280 envelope_280 := by
  refine finite_compose HasSnaky 2 childrenC_280 childrenD_280 finite_children_work_280 (1, 2)
    required_280 envelope_280 pivot_mem_280 child_required_sub_280 child_envelope_sub_280 ?_
  intro b hb
  exact common_sub_280 (mem_commonEnvelope childrenD_280 b hb)

theorem finite_children_work_310 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_310 j) (childrenD_310 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_76 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_310 : FiniteTemplate HasSnaky 3 required_310 envelope_310 := by
  refine finite_compose HasSnaky 2 childrenC_310 childrenD_310 finite_children_work_310 (1, 3)
    required_310 envelope_310 pivot_mem_310 child_required_sub_310 child_envelope_sub_310 ?_
  intro b hb
  exact common_sub_310 (mem_commonEnvelope childrenD_310 b hb)

theorem finite_children_work_333_i0 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_333_i0 j) (childrenD_333_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_333_i0 : FiniteTemplate HasSnaky 2 required_333_i0 envelope_333_i0 := by
  refine finite_compose HasSnaky 1 childrenC_333_i0 childrenD_333_i0 finite_children_work_333_i0 (0, 2)
    required_333_i0 envelope_333_i0 pivot_mem_333_i0 child_required_sub_333_i0 child_envelope_sub_333_i0 ?_
  intro b hb
  exact common_sub_333_i0 (mem_commonEnvelope childrenD_333_i0 b hb)

theorem finite_children_work_333 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_333 j) (childrenD_333 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_333_i0.mono (by decide +kernel)

theorem finite_row_works_333 : FiniteTemplate HasSnaky 3 required_333 envelope_333 := by
  refine finite_compose HasSnaky 2 childrenC_333 childrenD_333 finite_children_work_333 (1, 4)
    required_333 envelope_333 pivot_mem_333 child_required_sub_333 child_envelope_sub_333 ?_
  intro b hb
  exact common_sub_333 (mem_commonEnvelope childrenD_333 b hb)

theorem finite_children_work_350_i0 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_350_i0 j) (childrenD_350_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 3 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 4 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_350_i0 : FiniteTemplate HasSnaky 2 required_350_i0 envelope_350_i0 := by
  refine finite_compose HasSnaky 1 childrenC_350_i0 childrenD_350_i0 finite_children_work_350_i0 (4, 1)
    required_350_i0 envelope_350_i0 pivot_mem_350_i0 child_required_sub_350_i0 child_envelope_sub_350_i0 ?_
  intro b hb
  exact common_sub_350_i0 (mem_commonEnvelope childrenD_350_i0 b hb)

theorem finite_children_work_350 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_350 j) (childrenD_350 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_350_i0.mono (by decide +kernel)

theorem finite_row_works_350 : FiniteTemplate HasSnaky 3 required_350 envelope_350 := by
  refine finite_compose HasSnaky 2 childrenC_350 childrenD_350 finite_children_work_350 (4, 0)
    required_350 envelope_350 pivot_mem_350 child_required_sub_350 child_envelope_sub_350 ?_
  intro b hb
  exact common_sub_350 (mem_commonEnvelope childrenD_350 b hb)

theorem finite_children_work_374_i0 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_374_i0 j) (childrenD_374_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 7 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_374_i0 : FiniteTemplate HasSnaky 2 required_374_i0 envelope_374_i0 := by
  refine finite_compose HasSnaky 1 childrenC_374_i0 childrenD_374_i0 finite_children_work_374_i0 (4, 1)
    required_374_i0 envelope_374_i0 pivot_mem_374_i0 child_required_sub_374_i0 child_envelope_sub_374_i0 ?_
  intro b hb
  exact common_sub_374_i0 (mem_commonEnvelope childrenD_374_i0 b hb)

theorem finite_children_work_374 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_374 j) (childrenD_374 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_374_i0.mono (by decide +kernel)

theorem finite_row_works_374 : FiniteTemplate HasSnaky 3 required_374 envelope_374 := by
  refine finite_compose HasSnaky 2 childrenC_374 childrenD_374 finite_children_work_374 (4, 2)
    required_374 envelope_374 pivot_mem_374 child_required_sub_374 child_envelope_sub_374 ?_
  intro b hb
  exact common_sub_374 (mem_commonEnvelope childrenD_374 b hb)

theorem finite_children_work_402_i0 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_402_i0 j) (childrenD_402_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_402_i0 : FiniteTemplate HasSnaky 2 required_402_i0 envelope_402_i0 := by
  refine finite_compose HasSnaky 1 childrenC_402_i0 childrenD_402_i0 finite_children_work_402_i0 (2, 4)
    required_402_i0 envelope_402_i0 pivot_mem_402_i0 child_required_sub_402_i0 child_envelope_sub_402_i0 ?_
  intro b hb
  exact common_sub_402_i0 (mem_commonEnvelope childrenD_402_i0 b hb)

theorem finite_children_work_402 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_402 j) (childrenD_402 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_402_i0.mono (by decide +kernel)

theorem finite_row_works_402 : FiniteTemplate HasSnaky 3 required_402 envelope_402 := by
  refine finite_compose HasSnaky 2 childrenC_402 childrenD_402 finite_children_work_402 (3, 1)
    required_402 envelope_402 pivot_mem_402 child_required_sub_402 child_envelope_sub_402 ?_
  intro b hb
  exact common_sub_402 (mem_commonEnvelope childrenD_402 b hb)

end FiniteCongruenceChecks.SnakyFinite
