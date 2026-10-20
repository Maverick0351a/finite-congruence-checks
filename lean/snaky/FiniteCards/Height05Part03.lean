/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_272 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_272 j) (childrenD_272 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_39 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_272 : FiniteTemplate HasSnaky 5 required_272 envelope_272 := by
  refine finite_compose HasSnaky 4 childrenC_272 childrenD_272 finite_children_work_272 (2, 1)
    required_272 envelope_272 pivot_mem_272 child_required_sub_272 child_envelope_sub_272 ?_
  intro b hb
  exact common_sub_272 (mem_commonEnvelope childrenD_272 b hb)

theorem finite_children_work_273 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_273 j) (childrenD_273 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_206 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_273 : FiniteTemplate HasSnaky 5 required_273 envelope_273 := by
  refine finite_compose HasSnaky 4 childrenC_273 childrenD_273 finite_children_work_273 (3, 3)
    required_273 envelope_273 pivot_mem_273 child_required_sub_273 child_envelope_sub_273 ?_
  intro b hb
  exact common_sub_273 (mem_commonEnvelope childrenD_273 b hb)

theorem finite_children_work_274 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_274 j) (childrenD_274 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_83 5 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_274 : FiniteTemplate HasSnaky 5 required_274 envelope_274 := by
  refine finite_compose HasSnaky 4 childrenC_274 childrenD_274 finite_children_work_274 (3, 2)
    required_274 envelope_274 pivot_mem_274 child_required_sub_274 child_envelope_sub_274 ?_
  intro b hb
  exact common_sub_274 (mem_commonEnvelope childrenD_274 b hb)

theorem finite_children_work_278 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_278 j) (childrenD_278 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_277.mono (by decide +kernel)

theorem finite_row_works_278 : FiniteTemplate HasSnaky 5 required_278 envelope_278 := by
  refine finite_compose HasSnaky 4 childrenC_278 childrenD_278 finite_children_work_278 (4, 2)
    required_278 envelope_278 pivot_mem_278 child_required_sub_278 child_envelope_sub_278 ?_
  intro b hb
  exact common_sub_278 (mem_commonEnvelope childrenD_278 b hb)

theorem finite_children_work_279 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_279 j) (childrenD_279 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_141 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_279 : FiniteTemplate HasSnaky 5 required_279 envelope_279 := by
  refine finite_compose HasSnaky 4 childrenC_279 childrenD_279 finite_children_work_279 (4, 3)
    required_279 envelope_279 pivot_mem_279 child_required_sub_279 child_envelope_sub_279 ?_
  intro b hb
  exact common_sub_279 (mem_commonEnvelope childrenD_279 b hb)

theorem finite_children_work_282 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_282 j) (childrenD_282 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_92.mono (by decide +kernel)

theorem finite_row_works_282 : FiniteTemplate HasSnaky 5 required_282 envelope_282 := by
  refine finite_compose HasSnaky 4 childrenC_282 childrenD_282 finite_children_work_282 (3, 2)
    required_282 envelope_282 pivot_mem_282 child_required_sub_282 child_envelope_sub_282 ?_
  intro b hb
  exact common_sub_282 (mem_commonEnvelope childrenD_282 b hb)

theorem finite_children_work_293 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_293 j) (childrenD_293 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_293 : FiniteTemplate HasSnaky 5 required_293 envelope_293 := by
  refine finite_compose HasSnaky 4 childrenC_293 childrenD_293 finite_children_work_293 (4, 3)
    required_293 envelope_293 pivot_mem_293 child_required_sub_293 child_envelope_sub_293 ?_
  intro b hb
  exact common_sub_293 (mem_commonEnvelope childrenD_293 b hb)

theorem finite_children_work_294 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_294 j) (childrenD_294 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_48 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_165 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_294 : FiniteTemplate HasSnaky 5 required_294 envelope_294 := by
  refine finite_compose HasSnaky 4 childrenC_294 childrenD_294 finite_children_work_294 (3, 3)
    required_294 envelope_294 pivot_mem_294 child_required_sub_294 child_envelope_sub_294 ?_
  intro b hb
  exact common_sub_294 (mem_commonEnvelope childrenD_294 b hb)

theorem finite_children_work_296 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_296 j) (childrenD_296 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_132 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_296 : FiniteTemplate HasSnaky 5 required_296 envelope_296 := by
  refine finite_compose HasSnaky 4 childrenC_296 childrenD_296 finite_children_work_296 (2, 3)
    required_296 envelope_296 pivot_mem_296 child_required_sub_296 child_envelope_sub_296 ?_
  intro b hb
  exact common_sub_296 (mem_commonEnvelope childrenD_296 b hb)

theorem finite_children_work_299 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_299 j) (childrenD_299 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_165 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_264 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_299 : FiniteTemplate HasSnaky 5 required_299 envelope_299 := by
  refine finite_compose HasSnaky 4 childrenC_299 childrenD_299 finite_children_work_299 (3, 5)
    required_299 envelope_299 pivot_mem_299 child_required_sub_299 child_envelope_sub_299 ?_
  intro b hb
  exact common_sub_299 (mem_commonEnvelope childrenD_299 b hb)

theorem finite_children_work_301 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_301 j) (childrenD_301 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 3 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_55.mono (by decide +kernel)

theorem finite_row_works_301 : FiniteTemplate HasSnaky 5 required_301 envelope_301 := by
  refine finite_compose HasSnaky 4 childrenC_301 childrenD_301 finite_children_work_301 (3, 3)
    required_301 envelope_301 pivot_mem_301 child_required_sub_301 child_envelope_sub_301 ?_
  intro b hb
  exact common_sub_301 (mem_commonEnvelope childrenD_301 b hb)

theorem finite_children_work_306 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_306 j) (childrenD_306 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_207 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_306 : FiniteTemplate HasSnaky 5 required_306 envelope_306 := by
  refine finite_compose HasSnaky 4 childrenC_306 childrenD_306 finite_children_work_306 (4, 1)
    required_306 envelope_306 pivot_mem_306 child_required_sub_306 child_envelope_sub_306 ?_
  intro b hb
  exact common_sub_306 (mem_commonEnvelope childrenD_306 b hb)

theorem finite_children_work_308 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_308 j) (childrenD_308 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_158 6 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_308 : FiniteTemplate HasSnaky 5 required_308 envelope_308 := by
  refine finite_compose HasSnaky 4 childrenC_308 childrenD_308 finite_children_work_308 (1, 5)
    required_308 envelope_308 pivot_mem_308 child_required_sub_308 child_envelope_sub_308 ?_
  intro b hb
  exact common_sub_308 (mem_commonEnvelope childrenD_308 b hb)

theorem finite_children_work_312 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_312 j) (childrenD_312 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_311 4 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_312 : FiniteTemplate HasSnaky 5 required_312 envelope_312 := by
  refine finite_compose HasSnaky 4 childrenC_312 childrenD_312 finite_children_work_312 (2, 1)
    required_312 envelope_312 pivot_mem_312 child_required_sub_312 child_envelope_sub_312 ?_
  intro b hb
  exact common_sub_312 (mem_commonEnvelope childrenD_312 b hb)

theorem finite_children_work_314_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_314_i0 j) (childrenD_314_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_20 1 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_314_i0 : FiniteTemplate HasSnaky 4 required_314_i0 envelope_314_i0 := by
  refine finite_compose HasSnaky 3 childrenC_314_i0 childrenD_314_i0 finite_children_work_314_i0 (3, 0)
    required_314_i0 envelope_314_i0 pivot_mem_314_i0 child_required_sub_314_i0 child_envelope_sub_314_i0 ?_
  intro b hb
  exact common_sub_314_i0 (mem_commonEnvelope childrenD_314_i0 b hb)

theorem finite_children_work_314 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_314 j) (childrenD_314 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 1 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_314_i0.mono (by decide +kernel)

theorem finite_row_works_314 : FiniteTemplate HasSnaky 5 required_314 envelope_314 := by
  refine finite_compose HasSnaky 4 childrenC_314 childrenD_314 finite_children_work_314 (4, 1)
    required_314 envelope_314 pivot_mem_314 child_required_sub_314 child_envelope_sub_314 ?_
  intro b hb
  exact common_sub_314 (mem_commonEnvelope childrenD_314 b hb)

theorem finite_children_work_335 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_335 j) (childrenD_335 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_334 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_335 : FiniteTemplate HasSnaky 5 required_335 envelope_335 := by
  refine finite_compose HasSnaky 4 childrenC_335 childrenD_335 finite_children_work_335 (3, 3)
    required_335 envelope_335 pivot_mem_335 child_required_sub_335 child_envelope_sub_335 ?_
  intro b hb
  exact common_sub_335 (mem_commonEnvelope childrenD_335 b hb)

theorem finite_children_work_342_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_342_i0 j) (childrenD_342_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_342_i0 : FiniteTemplate HasSnaky 4 required_342_i0 envelope_342_i0 := by
  refine finite_compose HasSnaky 3 childrenC_342_i0 childrenD_342_i0 finite_children_work_342_i0 (3, 4)
    required_342_i0 envelope_342_i0 pivot_mem_342_i0 child_required_sub_342_i0 child_envelope_sub_342_i0 ?_
  intro b hb
  exact common_sub_342_i0 (mem_commonEnvelope childrenD_342_i0 b hb)

theorem finite_children_work_342 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_342 j) (childrenD_342 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_342_i0.mono (by decide +kernel)

theorem finite_row_works_342 : FiniteTemplate HasSnaky 5 required_342 envelope_342 := by
  refine finite_compose HasSnaky 4 childrenC_342 childrenD_342 finite_children_work_342 (3, 1)
    required_342 envelope_342 pivot_mem_342 child_required_sub_342 child_envelope_sub_342 ?_
  intro b hb
  exact common_sub_342 (mem_commonEnvelope childrenD_342 b hb)

theorem finite_children_work_347_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_347_i1 j) (childrenD_347_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_94 3 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_347_i1 : FiniteTemplate HasSnaky 3 required_347_i1 envelope_347_i1 := by
  refine finite_compose HasSnaky 2 childrenC_347_i1 childrenD_347_i1 finite_children_work_347_i1 (2, 3)
    required_347_i1 envelope_347_i1 pivot_mem_347_i1 child_required_sub_347_i1 child_envelope_sub_347_i1 ?_
  intro b hb
  exact common_sub_347_i1 (mem_commonEnvelope childrenD_347_i1 b hb)

theorem finite_children_work_347_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_347_i0 j) (childrenD_347_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_347_i1.mono (by decide +kernel)

theorem finite_row_works_347_i0 : FiniteTemplate HasSnaky 4 required_347_i0 envelope_347_i0 := by
  refine finite_compose HasSnaky 3 childrenC_347_i0 childrenD_347_i0 finite_children_work_347_i0 (0, 3)
    required_347_i0 envelope_347_i0 pivot_mem_347_i0 child_required_sub_347_i0 child_envelope_sub_347_i0 ?_
  intro b hb
  exact common_sub_347_i0 (mem_commonEnvelope childrenD_347_i0 b hb)

theorem finite_children_work_347 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_347 j) (childrenD_347 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_20.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 2 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_347_i0.mono (by decide +kernel)

theorem finite_row_works_347 : FiniteTemplate HasSnaky 5 required_347 envelope_347 := by
  refine finite_compose HasSnaky 4 childrenC_347 childrenD_347 finite_children_work_347 (1, 3)
    required_347 envelope_347 pivot_mem_347 child_required_sub_347 child_envelope_sub_347 ?_
  intro b hb
  exact common_sub_347 (mem_commonEnvelope childrenD_347 b hb)

theorem finite_children_work_352 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_352 j) (childrenD_352 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_351 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_352 : FiniteTemplate HasSnaky 5 required_352 envelope_352 := by
  refine finite_compose HasSnaky 4 childrenC_352 childrenD_352 finite_children_work_352 (4, 2)
    required_352 envelope_352 pivot_mem_352 child_required_sub_352 child_envelope_sub_352 ?_
  intro b hb
  exact common_sub_352 (mem_commonEnvelope childrenD_352 b hb)

theorem finite_children_work_355 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_355 j) (childrenD_355 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_354 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_355 : FiniteTemplate HasSnaky 5 required_355 envelope_355 := by
  refine finite_compose HasSnaky 4 childrenC_355 childrenD_355 finite_children_work_355 (3, 4)
    required_355 envelope_355 pivot_mem_355 child_required_sub_355 child_envelope_sub_355 ?_
  intro b hb
  exact common_sub_355 (mem_commonEnvelope childrenD_355 b hb)

end FiniteCongruenceChecks.SnakyFinite
