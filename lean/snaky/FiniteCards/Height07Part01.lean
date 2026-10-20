/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_116 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_116 j) (childrenD_116 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_116 : FiniteTemplate HasSnaky 7 required_116 envelope_116 := by
  refine finite_compose HasSnaky 6 childrenC_116 childrenD_116 finite_children_work_116 (4, 3)
    required_116 envelope_116 pivot_mem_116 child_required_sub_116 child_envelope_sub_116 ?_
  intro b hb
  exact common_sub_116 (mem_commonEnvelope childrenD_116 b hb)

theorem finite_children_work_117 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_117 j) (childrenD_117 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_117 : FiniteTemplate HasSnaky 7 required_117 envelope_117 := by
  refine finite_compose HasSnaky 6 childrenC_117 childrenD_117 finite_children_work_117 (4, 3)
    required_117 envelope_117 pivot_mem_117 child_required_sub_117 child_envelope_sub_117 ?_
  intro b hb
  exact common_sub_117 (mem_commonEnvelope childrenD_117 b hb)

theorem finite_children_work_118 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_118 j) (childrenD_118 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_118 : FiniteTemplate HasSnaky 7 required_118 envelope_118 := by
  refine finite_compose HasSnaky 6 childrenC_118 childrenD_118 finite_children_work_118 (4, 3)
    required_118 envelope_118 pivot_mem_118 child_required_sub_118 child_envelope_sub_118 ?_
  intro b hb
  exact common_sub_118 (mem_commonEnvelope childrenD_118 b hb)

theorem finite_children_work_204 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_204 j) (childrenD_204 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_203 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_204 : FiniteTemplate HasSnaky 7 required_204 envelope_204 := by
  refine finite_compose HasSnaky 6 childrenC_204 childrenD_204 finite_children_work_204 (2, 3)
    required_204 envelope_204 pivot_mem_204 child_required_sub_204 child_envelope_sub_204 ?_
  intro b hb
  exact common_sub_204 (mem_commonEnvelope childrenD_204 b hb)

theorem finite_children_work_256 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_256 j) (childrenD_256 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_255.mono (by decide +kernel)

theorem finite_row_works_256 : FiniteTemplate HasSnaky 7 required_256 envelope_256 := by
  refine finite_compose HasSnaky 6 childrenC_256 childrenD_256 finite_children_work_256 (3, 4)
    required_256 envelope_256 pivot_mem_256 child_required_sub_256 child_envelope_sub_256 ?_
  intro b hb
  exact common_sub_256 (mem_commonEnvelope childrenD_256 b hb)

theorem finite_children_work_276 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_276 j) (childrenD_276 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_155 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_275 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_276 : FiniteTemplate HasSnaky 7 required_276 envelope_276 := by
  refine finite_compose HasSnaky 6 childrenC_276 childrenD_276 finite_children_work_276 (2, 4)
    required_276 envelope_276 pivot_mem_276 child_required_sub_276 child_envelope_sub_276 ?_
  intro b hb
  exact common_sub_276 (mem_commonEnvelope childrenD_276 b hb)

theorem finite_children_work_286 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_286 j) (childrenD_286 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_253 5 (6, 1)).mono (by decide +kernel)

theorem finite_row_works_286 : FiniteTemplate HasSnaky 7 required_286 envelope_286 := by
  refine finite_compose HasSnaky 6 childrenC_286 childrenD_286 finite_children_work_286 (4, 2)
    required_286 envelope_286 pivot_mem_286 child_required_sub_286 child_envelope_sub_286 ?_
  intro b hb
  exact common_sub_286 (mem_commonEnvelope childrenD_286 b hb)

theorem finite_children_work_290 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_290 j) (childrenD_290 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_203.mono (by decide +kernel)

theorem finite_row_works_290 : FiniteTemplate HasSnaky 7 required_290 envelope_290 := by
  refine finite_compose HasSnaky 6 childrenC_290 childrenD_290 finite_children_work_290 (2, 1)
    required_290 envelope_290 pivot_mem_290 child_required_sub_290 child_envelope_sub_290 ?_
  intro b hb
  exact common_sub_290 (mem_commonEnvelope childrenD_290 b hb)

theorem finite_children_work_295 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_295 j) (childrenD_295 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 5 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (6, 0)).mono (by decide +kernel)

theorem finite_row_works_295 : FiniteTemplate HasSnaky 7 required_295 envelope_295 := by
  refine finite_compose HasSnaky 6 childrenC_295 childrenD_295 finite_children_work_295 (3, 1)
    required_295 envelope_295 pivot_mem_295 child_required_sub_295 child_envelope_sub_295 ?_
  intro b hb
  exact common_sub_295 (mem_commonEnvelope childrenD_295 b hb)

theorem finite_children_work_297 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_297 j) (childrenD_297 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 7 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_142 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_162 4 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_297 : FiniteTemplate HasSnaky 7 required_297 envelope_297 := by
  refine finite_compose HasSnaky 6 childrenC_297 childrenD_297 finite_children_work_297 (5, 3)
    required_297 envelope_297 pivot_mem_297 child_required_sub_297 child_envelope_sub_297 ?_
  intro b hb
  exact common_sub_297 (mem_commonEnvelope childrenD_297 b hb)

theorem finite_children_work_298 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_298 j) (childrenD_298 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 7 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_142 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_161 4 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_298 : FiniteTemplate HasSnaky 7 required_298 envelope_298 := by
  refine finite_compose HasSnaky 6 childrenC_298 childrenD_298 finite_children_work_298 (5, 3)
    required_298 envelope_298 pivot_mem_298 child_required_sub_298 child_envelope_sub_298 ?_
  intro b hb
  exact common_sub_298 (mem_commonEnvelope childrenD_298 b hb)

theorem finite_children_work_309 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_309 j) (childrenD_309 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_309 : FiniteTemplate HasSnaky 7 required_309 envelope_309 := by
  refine finite_compose HasSnaky 6 childrenC_309 childrenD_309 finite_children_work_309 (4, 3)
    required_309 envelope_309 pivot_mem_309 child_required_sub_309 child_envelope_sub_309 ?_
  intro b hb
  exact common_sub_309 (mem_commonEnvelope childrenD_309 b hb)

theorem finite_children_work_317 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_317 j) (childrenD_317 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_60 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_316 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_317 : FiniteTemplate HasSnaky 7 required_317 envelope_317 := by
  refine finite_compose HasSnaky 6 childrenC_317 childrenD_317 finite_children_work_317 (3, 5)
    required_317 envelope_317 pivot_mem_317 child_required_sub_317 child_envelope_sub_317 ?_
  intro b hb
  exact common_sub_317 (mem_commonEnvelope childrenD_317 b hb)

theorem finite_children_work_318 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_318 j) (childrenD_318 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_315 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_318 : FiniteTemplate HasSnaky 7 required_318 envelope_318 := by
  refine finite_compose HasSnaky 6 childrenC_318 childrenD_318 finite_children_work_318 (1, 3)
    required_318 envelope_318 pivot_mem_318 child_required_sub_318 child_envelope_sub_318 ?_
  intro b hb
  exact common_sub_318 (mem_commonEnvelope childrenD_318 b hb)

theorem finite_children_work_320 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_320 j) (childrenD_320 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_316 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_320 : FiniteTemplate HasSnaky 7 required_320 envelope_320 := by
  refine finite_compose HasSnaky 6 childrenC_320 childrenD_320 finite_children_work_320 (3, 5)
    required_320 envelope_320 pivot_mem_320 child_required_sub_320 child_envelope_sub_320 ?_
  intro b hb
  exact common_sub_320 (mem_commonEnvelope childrenD_320 b hb)

theorem finite_children_work_324 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_324 j) (childrenD_324 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_60 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_237 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_307 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_316 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_324 : FiniteTemplate HasSnaky 7 required_324 envelope_324 := by
  refine finite_compose HasSnaky 6 childrenC_324 childrenD_324 finite_children_work_324 (1, 3)
    required_324 envelope_324 pivot_mem_324 child_required_sub_324 child_envelope_sub_324 ?_
  intro b hb
  exact common_sub_324 (mem_commonEnvelope childrenD_324 b hb)

theorem finite_children_work_329 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_329 j) (childrenD_329 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_315 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_329 : FiniteTemplate HasSnaky 7 required_329 envelope_329 := by
  refine finite_compose HasSnaky 6 childrenC_329 childrenD_329 finite_children_work_329 (1, 4)
    required_329 envelope_329 pivot_mem_329 child_required_sub_329 child_envelope_sub_329 ?_
  intro b hb
  exact common_sub_329 (mem_commonEnvelope childrenD_329 b hb)

theorem finite_children_work_332 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_332 j) (childrenD_332 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_331 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_332 : FiniteTemplate HasSnaky 7 required_332 envelope_332 := by
  refine finite_compose HasSnaky 6 childrenC_332 childrenD_332 finite_children_work_332 (4, 3)
    required_332 envelope_332 pivot_mem_332 child_required_sub_332 child_envelope_sub_332 ?_
  intro b hb
  exact common_sub_332 (mem_commonEnvelope childrenD_332 b hb)

theorem finite_children_work_337 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_337 j) (childrenD_337 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_143 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_336 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_337 : FiniteTemplate HasSnaky 7 required_337 envelope_337 := by
  refine finite_compose HasSnaky 6 childrenC_337 childrenD_337 finite_children_work_337 (1, 2)
    required_337 envelope_337 pivot_mem_337 child_required_sub_337 child_envelope_sub_337 ?_
  intro b hb
  exact common_sub_337 (mem_commonEnvelope childrenD_337 b hb)

theorem finite_children_work_339 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_339 j) (childrenD_339 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_35 7 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_336 2 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_339 : FiniteTemplate HasSnaky 7 required_339 envelope_339 := by
  refine finite_compose HasSnaky 6 childrenC_339 childrenD_339 finite_children_work_339 (4, 2)
    required_339 envelope_339 pivot_mem_339 child_required_sub_339 child_envelope_sub_339 ?_
  intro b hb
  exact common_sub_339 (mem_commonEnvelope childrenD_339 b hb)

theorem finite_children_work_341 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_341 j) (childrenD_341 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 7 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_57 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_340 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_341 : FiniteTemplate HasSnaky 7 required_341 envelope_341 := by
  refine finite_compose HasSnaky 6 childrenC_341 childrenD_341 finite_children_work_341 (4, 4)
    required_341 envelope_341 pivot_mem_341 child_required_sub_341 child_envelope_sub_341 ?_
  intro b hb
  exact common_sub_341 (mem_commonEnvelope childrenD_341 b hb)

theorem finite_children_work_344 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_344 j) (childrenD_344 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_343 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_344 : FiniteTemplate HasSnaky 7 required_344 envelope_344 := by
  refine finite_compose HasSnaky 6 childrenC_344 childrenD_344 finite_children_work_344 (1, 3)
    required_344 envelope_344 pivot_mem_344 child_required_sub_344 child_envelope_sub_344 ?_
  intro b hb
  exact common_sub_344 (mem_commonEnvelope childrenD_344 b hb)

theorem finite_children_work_353 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_353 j) (childrenD_353 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_95 6 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_352 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_353 : FiniteTemplate HasSnaky 7 required_353 envelope_353 := by
  refine finite_compose HasSnaky 6 childrenC_353 childrenD_353 finite_children_work_353 (4, 6)
    required_353 envelope_353 pivot_mem_353 child_required_sub_353 child_envelope_sub_353 ?_
  intro b hb
  exact common_sub_353 (mem_commonEnvelope childrenD_353 b hb)

end FiniteCongruenceChecks.SnakyFinite
