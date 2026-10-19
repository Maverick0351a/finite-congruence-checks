/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height05Part01
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part05
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_120 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_120 j) (childrenD_120 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 3 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_116.mono (by decide +kernel)

theorem finite_row_works_120 : FiniteTemplate HasSnaky 8 required_120 envelope_120 := by
  refine finite_compose HasSnaky 7 childrenC_120 childrenD_120 finite_children_work_120 (2, 3)
    required_120 envelope_120 pivot_mem_120 child_required_sub_120 child_envelope_sub_120 ?_
  intro b hb
  exact common_sub_120 (mem_commonEnvelope childrenD_120 b hb)

theorem finite_children_work_171 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_171 j) (childrenD_171 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 4 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_116 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_171 : FiniteTemplate HasSnaky 8 required_171 envelope_171 := by
  refine finite_compose HasSnaky 7 childrenC_171 childrenD_171 finite_children_work_171 (4, 3)
    required_171 envelope_171 pivot_mem_171 child_required_sub_171 child_envelope_sub_171 ?_
  intro b hb
  exact common_sub_171 (mem_commonEnvelope childrenD_171 b hb)

theorem finite_children_work_174 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_174 j) (childrenD_174 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_117 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_173 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_173 5 (6, 2)).mono (by decide +kernel)

theorem finite_row_works_174 : FiniteTemplate HasSnaky 8 required_174 envelope_174 := by
  refine finite_compose HasSnaky 7 childrenC_174 childrenD_174 finite_children_work_174 (3, 5)
    required_174 envelope_174 pivot_mem_174 child_required_sub_174 child_envelope_sub_174 ?_
  intro b hb
  exact common_sub_174 (mem_commonEnvelope childrenD_174 b hb)

theorem finite_children_work_257 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_257 j) (childrenD_257 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_256 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_257 : FiniteTemplate HasSnaky 8 required_257 envelope_257 := by
  refine finite_compose HasSnaky 7 childrenC_257 childrenD_257 finite_children_work_257 (4, 3)
    required_257 envelope_257 pivot_mem_257 child_required_sub_257 child_envelope_sub_257 ?_
  intro b hb
  exact common_sub_257 (mem_commonEnvelope childrenD_257 b hb)

theorem finite_children_work_258 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_258 j) (childrenD_258 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_161 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_162 4 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_256.mono (by decide +kernel)

theorem finite_row_works_258 : FiniteTemplate HasSnaky 8 required_258 envelope_258 := by
  refine finite_compose HasSnaky 7 childrenC_258 childrenD_258 finite_children_work_258 (3, 3)
    required_258 envelope_258 pivot_mem_258 child_required_sub_258 child_envelope_sub_258 ?_
  intro b hb
  exact common_sub_258 (mem_commonEnvelope childrenD_258 b hb)

theorem finite_children_work_285 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_285 j) (childrenD_285 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_117 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_285 : FiniteTemplate HasSnaky 8 required_285 envelope_285 := by
  refine finite_compose HasSnaky 7 childrenC_285 childrenD_285 finite_children_work_285 (4, 3)
    required_285 envelope_285 pivot_mem_285 child_required_sub_285 child_envelope_sub_285 ?_
  intro b hb
  exact common_sub_285 (mem_commonEnvelope childrenD_285 b hb)

theorem finite_children_work_319 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_319 j) (childrenD_319 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_318 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_319 : FiniteTemplate HasSnaky 8 required_319 envelope_319 := by
  refine finite_compose HasSnaky 7 childrenC_319 childrenD_319 finite_children_work_319 (3, 4)
    required_319 envelope_319 pivot_mem_319 child_required_sub_319 child_envelope_sub_319 ?_
  intro b hb
  exact common_sub_319 (mem_commonEnvelope childrenD_319 b hb)

theorem finite_children_work_321 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_321 j) (childrenD_321 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_320.mono (by decide +kernel)

theorem finite_row_works_321 : FiniteTemplate HasSnaky 8 required_321 envelope_321 := by
  refine finite_compose HasSnaky 7 childrenC_321 childrenD_321 finite_children_work_321 (3, 3)
    required_321 envelope_321 pivot_mem_321 child_required_sub_321 child_envelope_sub_321 ?_
  intro b hb
  exact common_sub_321 (mem_commonEnvelope childrenD_321 b hb)

theorem finite_children_work_323 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_323 j) (childrenD_323 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_320 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_323 : FiniteTemplate HasSnaky 8 required_323 envelope_323 := by
  refine finite_compose HasSnaky 7 childrenC_323 childrenD_323 finite_children_work_323 (2, 4)
    required_323 envelope_323 pivot_mem_323 child_required_sub_323 child_envelope_sub_323 ?_
  intro b hb
  exact common_sub_323 (mem_commonEnvelope childrenD_323 b hb)

theorem finite_children_work_338 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_338 j) (childrenD_338 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_337 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_338 : FiniteTemplate HasSnaky 8 required_338 envelope_338 := by
  refine finite_compose HasSnaky 7 childrenC_338 childrenD_338 finite_children_work_338 (2, 4)
    required_338 envelope_338 pivot_mem_338 child_required_sub_338 child_envelope_sub_338 ?_
  intro b hb
  exact common_sub_338 (mem_commonEnvelope childrenD_338 b hb)

theorem finite_children_work_345 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_345 j) (childrenD_345 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_344.mono (by decide +kernel)

theorem finite_row_works_345 : FiniteTemplate HasSnaky 8 required_345 envelope_345 := by
  refine finite_compose HasSnaky 7 childrenC_345 childrenD_345 finite_children_work_345 (4, 2)
    required_345 envelope_345 pivot_mem_345 child_required_sub_345 child_envelope_sub_345 ?_
  intro b hb
  exact common_sub_345 (mem_commonEnvelope childrenD_345 b hb)

theorem finite_children_work_373 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_373 j) (childrenD_373 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_372.mono (by decide +kernel)

theorem finite_row_works_373 : FiniteTemplate HasSnaky 8 required_373 envelope_373 := by
  refine finite_compose HasSnaky 7 childrenC_373 childrenD_373 finite_children_work_373 (1, 4)
    required_373 envelope_373 pivot_mem_373 child_required_sub_373 child_envelope_sub_373 ?_
  intro b hb
  exact common_sub_373 (mem_commonEnvelope childrenD_373 b hb)

theorem finite_children_work_395_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_395_i0 j) (childrenD_395_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_217 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_395_i0 : FiniteTemplate HasSnaky 7 required_395_i0 envelope_395_i0 := by
  refine finite_compose HasSnaky 6 childrenC_395_i0 childrenD_395_i0 finite_children_work_395_i0 (3, 1)
    required_395_i0 envelope_395_i0 pivot_mem_395_i0 child_required_sub_395_i0 child_envelope_sub_395_i0 ?_
  intro b hb
  exact common_sub_395_i0 (mem_commonEnvelope childrenD_395_i0 b hb)

theorem finite_children_work_395 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_395 j) (childrenD_395 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_395_i0.mono (by decide +kernel)

theorem finite_row_works_395 : FiniteTemplate HasSnaky 8 required_395 envelope_395 := by
  refine finite_compose HasSnaky 7 childrenC_395 childrenD_395 finite_children_work_395 (3, 3)
    required_395 envelope_395 pivot_mem_395 child_required_sub_395 child_envelope_sub_395 ?_
  intro b hb
  exact common_sub_395 (mem_commonEnvelope childrenD_395 b hb)

theorem finite_children_work_405 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_405 j) (childrenD_405 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_404.mono (by decide +kernel)

theorem finite_row_works_405 : FiniteTemplate HasSnaky 8 required_405 envelope_405 := by
  refine finite_compose HasSnaky 7 childrenC_405 childrenD_405 finite_children_work_405 (1, 4)
    required_405 envelope_405 pivot_mem_405 child_required_sub_405 child_envelope_sub_405 ?_
  intro b hb
  exact common_sub_405 (mem_commonEnvelope childrenD_405 b hb)

theorem finite_children_work_412_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_412_i0 j) (childrenD_412_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_358.mono (by decide +kernel)

theorem finite_row_works_412_i0 : FiniteTemplate HasSnaky 7 required_412_i0 envelope_412_i0 := by
  refine finite_compose HasSnaky 6 childrenC_412_i0 childrenD_412_i0 finite_children_work_412_i0 (3, 1)
    required_412_i0 envelope_412_i0 pivot_mem_412_i0 child_required_sub_412_i0 child_envelope_sub_412_i0 ?_
  intro b hb
  exact common_sub_412_i0 (mem_commonEnvelope childrenD_412_i0 b hb)

theorem finite_children_work_412 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_412 j) (childrenD_412 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_412_i0.mono (by decide +kernel)

theorem finite_row_works_412 : FiniteTemplate HasSnaky 8 required_412 envelope_412 := by
  refine finite_compose HasSnaky 7 childrenC_412 childrenD_412 finite_children_work_412 (2, 1)
    required_412 envelope_412 pivot_mem_412 child_required_sub_412 child_envelope_sub_412 ?_
  intro b hb
  exact common_sub_412 (mem_commonEnvelope childrenD_412 b hb)

theorem finite_children_work_419 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_419 j) (childrenD_419 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_418 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_419 : FiniteTemplate HasSnaky 8 required_419 envelope_419 := by
  refine finite_compose HasSnaky 7 childrenC_419 childrenD_419 finite_children_work_419 (2, 1)
    required_419 envelope_419 pivot_mem_419 child_required_sub_419 child_envelope_sub_419 ?_
  intro b hb
  exact common_sub_419 (mem_commonEnvelope childrenD_419 b hb)

theorem finite_children_work_420 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_420 j) (childrenD_420 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_418.mono (by decide +kernel)

theorem finite_row_works_420 : FiniteTemplate HasSnaky 8 required_420 envelope_420 := by
  refine finite_compose HasSnaky 7 childrenC_420 childrenD_420 finite_children_work_420 (3, 1)
    required_420 envelope_420 pivot_mem_420 child_required_sub_420 child_envelope_sub_420 ?_
  intro b hb
  exact common_sub_420 (mem_commonEnvelope childrenD_420 b hb)

theorem finite_children_work_438 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_438 j) (childrenD_438 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 7 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 6 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_436 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_438 : FiniteTemplate HasSnaky 8 required_438 envelope_438 := by
  refine finite_compose HasSnaky 7 childrenC_438 childrenD_438 finite_children_work_438 (4, 3)
    required_438 envelope_438 pivot_mem_438 child_required_sub_438 child_envelope_sub_438 ?_
  intro b hb
  exact common_sub_438 (mem_commonEnvelope childrenD_438 b hb)

theorem finite_children_work_440_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_440_i0 j) (childrenD_440_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_439 7 (5, 4)).mono (by decide +kernel)

theorem finite_row_works_440_i0 : FiniteTemplate HasSnaky 7 required_440_i0 envelope_440_i0 := by
  refine finite_compose HasSnaky 6 childrenC_440_i0 childrenD_440_i0 finite_children_work_440_i0 (1, 1)
    required_440_i0 envelope_440_i0 pivot_mem_440_i0 child_required_sub_440_i0 child_envelope_sub_440_i0 ?_
  intro b hb
  exact common_sub_440_i0 (mem_commonEnvelope childrenD_440_i0 b hb)

theorem finite_children_work_440 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_440 j) (childrenD_440 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_440_i0.mono (by decide +kernel)

theorem finite_row_works_440 : FiniteTemplate HasSnaky 8 required_440 envelope_440 := by
  refine finite_compose HasSnaky 7 childrenC_440 childrenD_440 finite_children_work_440 (0, 1)
    required_440 envelope_440 pivot_mem_440 child_required_sub_440 child_envelope_sub_440 ?_
  intro b hb
  exact common_sub_440 (mem_commonEnvelope childrenD_440 b hb)

theorem finite_children_work_448 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_448 j) (childrenD_448 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_56 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_447 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_448 : FiniteTemplate HasSnaky 8 required_448 envelope_448 := by
  refine finite_compose HasSnaky 7 childrenC_448 childrenD_448 finite_children_work_448 (1, 3)
    required_448 envelope_448 pivot_mem_448 child_required_sub_448 child_envelope_sub_448 ?_
  intro b hb
  exact common_sub_448 (mem_commonEnvelope childrenD_448 b hb)

end FiniteCongruenceChecks.SnakyFinite
