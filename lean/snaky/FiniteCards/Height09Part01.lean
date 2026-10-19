/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height08Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_322 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_322 j) (childrenD_322 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_322 : FiniteTemplate HasSnaky 9 required_322 envelope_322 := by
  refine finite_compose HasSnaky 8 childrenC_322 childrenD_322 finite_children_work_322 (4, 4)
    required_322 envelope_322 pivot_mem_322 child_required_sub_322 child_envelope_sub_322 ?_
  intro b hb
  exact common_sub_322 (mem_commonEnvelope childrenD_322 b hb)

theorem finite_children_work_325 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_325 j) (childrenD_325 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_325 : FiniteTemplate HasSnaky 9 required_325 envelope_325 := by
  refine finite_compose HasSnaky 8 childrenC_325 childrenD_325 finite_children_work_325 (3, 4)
    required_325 envelope_325 pivot_mem_325 child_required_sub_325 child_envelope_sub_325 ?_
  intro b hb
  exact common_sub_325 (mem_commonEnvelope childrenD_325 b hb)

theorem finite_children_work_326 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_326 j) (childrenD_326 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_326 : FiniteTemplate HasSnaky 9 required_326 envelope_326 := by
  refine finite_compose HasSnaky 8 childrenC_326 childrenD_326 finite_children_work_326 (2, 4)
    required_326 envelope_326 pivot_mem_326 child_required_sub_326 child_envelope_sub_326 ?_
  intro b hb
  exact common_sub_326 (mem_commonEnvelope childrenD_326 b hb)

theorem finite_children_work_327 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_327 j) (childrenD_327 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_32 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_327 : FiniteTemplate HasSnaky 9 required_327 envelope_327 := by
  refine finite_compose HasSnaky 8 childrenC_327 childrenD_327 finite_children_work_327 (4, 4)
    required_327 envelope_327 pivot_mem_327 child_required_sub_327 child_envelope_sub_327 ?_
  intro b hb
  exact common_sub_327 (mem_commonEnvelope childrenD_327 b hb)

theorem finite_children_work_328 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_328 j) (childrenD_328 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_328 : FiniteTemplate HasSnaky 9 required_328 envelope_328 := by
  refine finite_compose HasSnaky 8 childrenC_328 childrenD_328 finite_children_work_328 (3, 4)
    required_328 envelope_328 pivot_mem_328 child_required_sub_328 child_envelope_sub_328 ?_
  intro b hb
  exact common_sub_328 (mem_commonEnvelope childrenD_328 b hb)

theorem finite_children_work_330 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_330 j) (childrenD_330 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_330 : FiniteTemplate HasSnaky 9 required_330 envelope_330 := by
  refine finite_compose HasSnaky 8 childrenC_330 childrenD_330 finite_children_work_330 (3, 4)
    required_330 envelope_330 pivot_mem_330 child_required_sub_330 child_envelope_sub_330 ?_
  intro b hb
  exact common_sub_330 (mem_commonEnvelope childrenD_330 b hb)

theorem finite_children_work_368 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_368 j) (childrenD_368 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_257 5 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_355 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 6 (5, 7)).mono (by decide +kernel)

theorem finite_row_works_368 : FiniteTemplate HasSnaky 9 required_368 envelope_368 := by
  refine finite_compose HasSnaky 8 childrenC_368 childrenD_368 finite_children_work_368 (4, 5)
    required_368 envelope_368 pivot_mem_368 child_required_sub_368 child_envelope_sub_368 ?_
  intro b hb
  exact common_sub_368 (mem_commonEnvelope childrenD_368 b hb)

theorem finite_children_work_380_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_380_i0 j) (childrenD_380_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_379 1 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_380_i0 : FiniteTemplate HasSnaky 8 required_380_i0 envelope_380_i0 := by
  refine finite_compose HasSnaky 7 childrenC_380_i0 childrenD_380_i0 finite_children_work_380_i0 (3, 0)
    required_380_i0 envelope_380_i0 pivot_mem_380_i0 child_required_sub_380_i0 child_envelope_sub_380_i0 ?_
  intro b hb
  exact common_sub_380_i0 (mem_commonEnvelope childrenD_380_i0 b hb)

theorem finite_children_work_380 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_380 j) (childrenD_380 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_380_i0.mono (by decide +kernel)

theorem finite_row_works_380 : FiniteTemplate HasSnaky 9 required_380 envelope_380 := by
  refine finite_compose HasSnaky 8 childrenC_380 childrenD_380 finite_children_work_380 (3, 2)
    required_380 envelope_380 pivot_mem_380 child_required_sub_380 child_envelope_sub_380 ?_
  intro b hb
  exact common_sub_380 (mem_commonEnvelope childrenD_380 b hb)

theorem finite_children_work_396 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_396 j) (childrenD_396 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_395 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_396 : FiniteTemplate HasSnaky 9 required_396 envelope_396 := by
  refine finite_compose HasSnaky 8 childrenC_396 childrenD_396 finite_children_work_396 (2, 6)
    required_396 envelope_396 pivot_mem_396 child_required_sub_396 child_envelope_sub_396 ?_
  intro b hb
  exact common_sub_396 (mem_commonEnvelope childrenD_396 b hb)

theorem finite_children_work_397 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_397 j) (childrenD_397 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_161.mono (by decide +kernel)
  · exact finite_row_works_162.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_395 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_397 : FiniteTemplate HasSnaky 9 required_397 envelope_397 := by
  refine finite_compose HasSnaky 8 childrenC_397 childrenD_397 finite_children_work_397 (3, 3)
    required_397 envelope_397 pivot_mem_397 child_required_sub_397 child_envelope_sub_397 ?_
  intro b hb
  exact common_sub_397 (mem_commonEnvelope childrenD_397 b hb)

theorem finite_children_work_398 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_398 j) (childrenD_398 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_171.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 4 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_285.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_395 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_398 : FiniteTemplate HasSnaky 9 required_398 envelope_398 := by
  refine finite_compose HasSnaky 8 childrenC_398 childrenD_398 finite_children_work_398 (3, 3)
    required_398 envelope_398 pivot_mem_398 child_required_sub_398 child_envelope_sub_398 ?_
  intro b hb
  exact common_sub_398 (mem_commonEnvelope childrenD_398 b hb)

theorem finite_children_work_400 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_400 j) (childrenD_400 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_395 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_400 : FiniteTemplate HasSnaky 9 required_400 envelope_400 := by
  refine finite_compose HasSnaky 8 childrenC_400 childrenD_400 finite_children_work_400 (3, 2)
    required_400 envelope_400 pivot_mem_400 child_required_sub_400 child_envelope_sub_400 ?_
  intro b hb
  exact common_sub_400 (mem_commonEnvelope childrenD_400 b hb)

theorem finite_children_work_406 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_406 j) (childrenD_406 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_199.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_199 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_405 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_405 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_406 : FiniteTemplate HasSnaky 9 required_406 envelope_406 := by
  refine finite_compose HasSnaky 8 childrenC_406 childrenD_406 finite_children_work_406 (1, 4)
    required_406 envelope_406 pivot_mem_406 child_required_sub_406 child_envelope_sub_406 ?_
  intro b hb
  exact common_sub_406 (mem_commonEnvelope childrenD_406 b hb)

theorem finite_children_work_407_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_407_i0 j) (childrenD_407_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_404 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_407_i0 : FiniteTemplate HasSnaky 8 required_407_i0 envelope_407_i0 := by
  refine finite_compose HasSnaky 7 childrenC_407_i0 childrenD_407_i0 finite_children_work_407_i0 (0, 4)
    required_407_i0 envelope_407_i0 pivot_mem_407_i0 child_required_sub_407_i0 child_envelope_sub_407_i0 ?_
  intro b hb
  exact common_sub_407_i0 (mem_commonEnvelope childrenD_407_i0 b hb)

theorem finite_children_work_407 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_407 j) (childrenD_407 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_407_i0.mono (by decide +kernel)

theorem finite_row_works_407 : FiniteTemplate HasSnaky 9 required_407 envelope_407 := by
  refine finite_compose HasSnaky 8 childrenC_407 childrenD_407 finite_children_work_407 (1, 4)
    required_407 envelope_407 pivot_mem_407 child_required_sub_407 child_envelope_sub_407 ?_
  intro b hb
  exact common_sub_407 (mem_commonEnvelope childrenD_407 b hb)

theorem finite_children_work_421 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_421 j) (childrenD_421 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_419.mono (by decide +kernel)

theorem finite_row_works_421 : FiniteTemplate HasSnaky 9 required_421 envelope_421 := by
  refine finite_compose HasSnaky 8 childrenC_421 childrenD_421 finite_children_work_421 (1, 4)
    required_421 envelope_421 pivot_mem_421 child_required_sub_421 child_envelope_sub_421 ?_
  intro b hb
  exact common_sub_421 (mem_commonEnvelope childrenD_421 b hb)

theorem finite_children_work_434_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_434_i0 j) (childrenD_434_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 4 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_434_i0 : FiniteTemplate HasSnaky 5 required_434_i0 envelope_434_i0 := by
  refine finite_compose HasSnaky 4 childrenC_434_i0 childrenD_434_i0 finite_children_work_434_i0 (5, 1)
    required_434_i0 envelope_434_i0 pivot_mem_434_i0 child_required_sub_434_i0 child_envelope_sub_434_i0 ?_
  intro b hb
  exact common_sub_434_i0 (mem_commonEnvelope childrenD_434_i0 b hb)

theorem finite_children_work_434_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_434_i1 j) (childrenD_434_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 5 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_253 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_256 5 (7, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_336 0 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_434_i1 : FiniteTemplate HasSnaky 8 required_434_i1 envelope_434_i1 := by
  refine finite_compose HasSnaky 7 childrenC_434_i1 childrenD_434_i1 finite_children_work_434_i1 (4, 4)
    required_434_i1 envelope_434_i1 pivot_mem_434_i1 child_required_sub_434_i1 child_envelope_sub_434_i1 ?_
  intro b hb
  exact common_sub_434_i1 (mem_commonEnvelope childrenD_434_i1 b hb)

theorem finite_children_work_434 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_434 j) (childrenD_434 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_80 5 (5, 1)).mono (by decide +kernel)
  · exact finite_row_works_434_i0.mono (by decide +kernel)
  · exact finite_row_works_434_i1.mono (by decide +kernel)

theorem finite_row_works_434 : FiniteTemplate HasSnaky 9 required_434 envelope_434 := by
  refine finite_compose HasSnaky 8 childrenC_434 childrenD_434 finite_children_work_434 (3, 2)
    required_434 envelope_434 pivot_mem_434 child_required_sub_434 child_envelope_sub_434 ?_
  intro b hb
  exact common_sub_434 (mem_commonEnvelope childrenD_434 b hb)

theorem finite_children_work_441 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_441 j) (childrenD_441 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_440.mono (by decide +kernel)

theorem finite_row_works_441 : FiniteTemplate HasSnaky 9 required_441 envelope_441 := by
  refine finite_compose HasSnaky 8 childrenC_441 childrenD_441 finite_children_work_441 (3, 3)
    required_441 envelope_441 pivot_mem_441 child_required_sub_441 child_envelope_sub_441 ?_
  intro b hb
  exact common_sub_441 (mem_commonEnvelope childrenD_441 b hb)

theorem finite_children_work_442 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_442 j) (childrenD_442 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_149 7 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_440.mono (by decide +kernel)

theorem finite_row_works_442 : FiniteTemplate HasSnaky 9 required_442 envelope_442 := by
  refine finite_compose HasSnaky 8 childrenC_442 childrenD_442 finite_children_work_442 (3, 3)
    required_442 envelope_442 pivot_mem_442 child_required_sub_442 child_envelope_sub_442 ?_
  intro b hb
  exact common_sub_442 (mem_commonEnvelope childrenD_442 b hb)

end FiniteCongruenceChecks.SnakyFinite
