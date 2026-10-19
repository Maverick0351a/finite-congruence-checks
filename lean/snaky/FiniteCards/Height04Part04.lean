/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_268 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_268 j) (childrenD_268 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_268 : FiniteTemplate HasSnaky 4 required_268 envelope_268 := by
  refine finite_compose HasSnaky 3 childrenC_268 childrenD_268 finite_children_work_268 (1, 4)
    required_268 envelope_268 pivot_mem_268 child_required_sub_268 child_envelope_sub_268 ?_
  intro b hb
  exact common_sub_268 (mem_commonEnvelope childrenD_268 b hb)

theorem finite_children_work_269 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_269 j) (childrenD_269 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_21 2 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_269 : FiniteTemplate HasSnaky 4 required_269 envelope_269 := by
  refine finite_compose HasSnaky 3 childrenC_269 childrenD_269 finite_children_work_269 (1, 5)
    required_269 envelope_269 pivot_mem_269 child_required_sub_269 child_envelope_sub_269 ?_
  intro b hb
  exact common_sub_269 (mem_commonEnvelope childrenD_269 b hb)

theorem finite_children_work_271 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_271 j) (childrenD_271 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_271 : FiniteTemplate HasSnaky 4 required_271 envelope_271 := by
  refine finite_compose HasSnaky 3 childrenC_271 childrenD_271 finite_children_work_271 (2, 3)
    required_271 envelope_271 pivot_mem_271 child_required_sub_271 child_envelope_sub_271 ?_
  intro b hb
  exact common_sub_271 (mem_commonEnvelope childrenD_271 b hb)

theorem finite_children_work_277 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_277 j) (childrenD_277 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_69 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_277 : FiniteTemplate HasSnaky 4 required_277 envelope_277 := by
  refine finite_compose HasSnaky 3 childrenC_277 childrenD_277 finite_children_work_277 (1, 3)
    required_277 envelope_277 pivot_mem_277 child_required_sub_277 child_envelope_sub_277 ?_
  intro b hb
  exact common_sub_277 (mem_commonEnvelope childrenD_277 b hb)

theorem finite_children_work_288 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_288 j) (childrenD_288 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_68.mono (by decide +kernel)

theorem finite_row_works_288 : FiniteTemplate HasSnaky 4 required_288 envelope_288 := by
  refine finite_compose HasSnaky 3 childrenC_288 childrenD_288 finite_children_work_288 (1, 5)
    required_288 envelope_288 pivot_mem_288 child_required_sub_288 child_envelope_sub_288 ?_
  intro b hb
  exact common_sub_288 (mem_commonEnvelope childrenD_288 b hb)

theorem finite_children_work_289 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_289 j) (childrenD_289 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_22.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_28 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_126 6 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_289 : FiniteTemplate HasSnaky 4 required_289 envelope_289 := by
  refine finite_compose HasSnaky 3 childrenC_289 childrenD_289 finite_children_work_289 (1, 2)
    required_289 envelope_289 pivot_mem_289 child_required_sub_289 child_envelope_sub_289 ?_
  intro b hb
  exact common_sub_289 (mem_commonEnvelope childrenD_289 b hb)

theorem finite_children_work_291 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_291 j) (childrenD_291 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_25 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_291 : FiniteTemplate HasSnaky 4 required_291 envelope_291 := by
  refine finite_compose HasSnaky 3 childrenC_291 childrenD_291 finite_children_work_291 (3, 4)
    required_291 envelope_291 pivot_mem_291 child_required_sub_291 child_envelope_sub_291 ?_
  intro b hb
  exact common_sub_291 (mem_commonEnvelope childrenD_291 b hb)

theorem finite_children_work_304 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_304 j) (childrenD_304 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_304 : FiniteTemplate HasSnaky 4 required_304 envelope_304 := by
  refine finite_compose HasSnaky 3 childrenC_304 childrenD_304 finite_children_work_304 (1, 4)
    required_304 envelope_304 pivot_mem_304 child_required_sub_304 child_envelope_sub_304 ?_
  intro b hb
  exact common_sub_304 (mem_commonEnvelope childrenD_304 b hb)

theorem finite_children_work_305 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_305 j) (childrenD_305 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_124 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_305 : FiniteTemplate HasSnaky 4 required_305 envelope_305 := by
  refine finite_compose HasSnaky 3 childrenC_305 childrenD_305 finite_children_work_305 (1, 3)
    required_305 envelope_305 pivot_mem_305 child_required_sub_305 child_envelope_sub_305 ?_
  intro b hb
  exact common_sub_305 (mem_commonEnvelope childrenD_305 b hb)

theorem finite_children_work_307 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_307 j) (childrenD_307 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_131 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_307 : FiniteTemplate HasSnaky 4 required_307 envelope_307 := by
  refine finite_compose HasSnaky 3 childrenC_307 childrenD_307 finite_children_work_307 (4, 2)
    required_307 envelope_307 pivot_mem_307 child_required_sub_307 child_envelope_sub_307 ?_
  intro b hb
  exact common_sub_307 (mem_commonEnvelope childrenD_307 b hb)

theorem finite_children_work_311_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_311_i0 j) (childrenD_311_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_311_i0 : FiniteTemplate HasSnaky 3 required_311_i0 envelope_311_i0 := by
  refine finite_compose HasSnaky 2 childrenC_311_i0 childrenD_311_i0 finite_children_work_311_i0 (4, 1)
    required_311_i0 envelope_311_i0 pivot_mem_311_i0 child_required_sub_311_i0 child_envelope_sub_311_i0 ?_
  intro b hb
  exact common_sub_311_i0 (mem_commonEnvelope childrenD_311_i0 b hb)

theorem finite_children_work_311 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_311 j) (childrenD_311 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_311_i0.mono (by decide +kernel)

theorem finite_row_works_311 : FiniteTemplate HasSnaky 4 required_311 envelope_311 := by
  refine finite_compose HasSnaky 3 childrenC_311 childrenD_311 finite_children_work_311 (3, 1)
    required_311 envelope_311 pivot_mem_311 child_required_sub_311 child_envelope_sub_311 ?_
  intro b hb
  exact common_sub_311 (mem_commonEnvelope childrenD_311 b hb)

theorem finite_children_work_334 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_334 j) (childrenD_334 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_101 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_101 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_333 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_333 6 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_334 : FiniteTemplate HasSnaky 4 required_334 envelope_334 := by
  refine finite_compose HasSnaky 3 childrenC_334 childrenD_334 finite_children_work_334 (1, 5)
    required_334 envelope_334 pivot_mem_334 child_required_sub_334 child_envelope_sub_334 ?_
  intro b hb
  exact common_sub_334 (mem_commonEnvelope childrenD_334 b hb)

theorem finite_children_work_351 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_351 j) (childrenD_351 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_350.mono (by decide +kernel)

theorem finite_row_works_351 : FiniteTemplate HasSnaky 4 required_351 envelope_351 := by
  refine finite_compose HasSnaky 3 childrenC_351 childrenD_351 finite_children_work_351 (3, 1)
    required_351 envelope_351 pivot_mem_351 child_required_sub_351 child_envelope_sub_351 ?_
  intro b hb
  exact common_sub_351 (mem_commonEnvelope childrenD_351 b hb)

theorem finite_children_work_354_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_354_i0 j) (childrenD_354_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_70 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_354_i0 : FiniteTemplate HasSnaky 3 required_354_i0 envelope_354_i0 := by
  refine finite_compose HasSnaky 2 childrenC_354_i0 childrenD_354_i0 finite_children_work_354_i0 (3, 2)
    required_354_i0 envelope_354_i0 pivot_mem_354_i0 child_required_sub_354_i0 child_envelope_sub_354_i0 ?_
  intro b hb
  exact common_sub_354_i0 (mem_commonEnvelope childrenD_354_i0 b hb)

theorem finite_children_work_354 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_354 j) (childrenD_354 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_354_i0.mono (by decide +kernel)

theorem finite_row_works_354 : FiniteTemplate HasSnaky 4 required_354 envelope_354 := by
  refine finite_compose HasSnaky 3 childrenC_354 childrenD_354 finite_children_work_354 (3, 0)
    required_354 envelope_354 pivot_mem_354 child_required_sub_354 child_envelope_sub_354 ?_
  intro b hb
  exact common_sub_354 (mem_commonEnvelope childrenD_354 b hb)

theorem finite_children_work_365_i1 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_365_i1 j) (childrenD_365_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_0 7 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_365_i1 : FiniteTemplate HasSnaky 2 required_365_i1 envelope_365_i1 := by
  refine finite_compose HasSnaky 1 childrenC_365_i1 childrenD_365_i1 finite_children_work_365_i1 (0, 4)
    required_365_i1 envelope_365_i1 pivot_mem_365_i1 child_required_sub_365_i1 child_envelope_sub_365_i1 ?_
  intro b hb
  exact common_sub_365_i1 (mem_commonEnvelope childrenD_365_i1 b hb)

theorem finite_children_work_365_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_365_i0 j) (childrenD_365_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_365_i1.mono (by decide +kernel)

theorem finite_row_works_365_i0 : FiniteTemplate HasSnaky 3 required_365_i0 envelope_365_i0 := by
  refine finite_compose HasSnaky 2 childrenC_365_i0 childrenD_365_i0 finite_children_work_365_i0 (0, 3)
    required_365_i0 envelope_365_i0 pivot_mem_365_i0 child_required_sub_365_i0 child_envelope_sub_365_i0 ?_
  intro b hb
  exact common_sub_365_i0 (mem_commonEnvelope childrenD_365_i0 b hb)

theorem finite_children_work_365 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_365 j) (childrenD_365 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_365_i0.mono (by decide +kernel)

theorem finite_row_works_365 : FiniteTemplate HasSnaky 4 required_365 envelope_365 := by
  refine finite_compose HasSnaky 3 childrenC_365 childrenD_365 finite_children_work_365 (1, 6)
    required_365 envelope_365 pivot_mem_365 child_required_sub_365 child_envelope_sub_365 ?_
  intro b hb
  exact common_sub_365 (mem_commonEnvelope childrenD_365 b hb)

theorem finite_children_work_375 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_375 j) (childrenD_375 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_374.mono (by decide +kernel)

theorem finite_row_works_375 : FiniteTemplate HasSnaky 4 required_375 envelope_375 := by
  refine finite_compose HasSnaky 3 childrenC_375 childrenD_375 finite_children_work_375 (3, 1)
    required_375 envelope_375 pivot_mem_375 child_required_sub_375 child_envelope_sub_375 ?_
  intro b hb
  exact common_sub_375 (mem_commonEnvelope childrenD_375 b hb)

theorem finite_children_work_376_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_376_i0 j) (childrenD_376_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_77 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_376_i0 : FiniteTemplate HasSnaky 3 required_376_i0 envelope_376_i0 := by
  refine finite_compose HasSnaky 2 childrenC_376_i0 childrenD_376_i0 finite_children_work_376_i0 (2, 4)
    required_376_i0 envelope_376_i0 pivot_mem_376_i0 child_required_sub_376_i0 child_envelope_sub_376_i0 ?_
  intro b hb
  exact common_sub_376_i0 (mem_commonEnvelope childrenD_376_i0 b hb)

theorem finite_children_work_376 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_376 j) (childrenD_376 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_376_i0.mono (by decide +kernel)

theorem finite_row_works_376 : FiniteTemplate HasSnaky 4 required_376 envelope_376 := by
  refine finite_compose HasSnaky 3 childrenC_376 childrenD_376 finite_children_work_376 (3, 0)
    required_376 envelope_376 pivot_mem_376 child_required_sub_376 child_envelope_sub_376 ?_
  intro b hb
  exact common_sub_376 (mem_commonEnvelope childrenD_376 b hb)

end FiniteCongruenceChecks.SnakyFinite
