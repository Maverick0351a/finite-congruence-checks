/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height08Part01
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_399 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_399 j) (childrenD_399 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_396.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_396 4 (0, 8)).mono (by decide +kernel)

theorem finite_row_works_399 : FiniteTemplate HasSnaky 10 required_399 envelope_399 := by
  refine finite_compose HasSnaky 9 childrenC_399 childrenD_399 finite_children_work_399 (2, 5)
    required_399 envelope_399 pivot_mem_399 child_required_sub_399 child_envelope_sub_399 ?_
  intro b hb
  exact common_sub_399 (mem_commonEnvelope childrenD_399 b hb)

theorem finite_children_work_401 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_401 j) (childrenD_401 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_397 4 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_401 : FiniteTemplate HasSnaky 10 required_401 envelope_401 := by
  refine finite_compose HasSnaky 9 childrenC_401 childrenD_401 finite_children_work_401 (2, 4)
    required_401 envelope_401 pivot_mem_401 child_required_sub_401 child_envelope_sub_401 ?_
  intro b hb
  exact common_sub_401 (mem_commonEnvelope childrenD_401 b hb)

theorem finite_children_work_408 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_408 j) (childrenD_408 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_127 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_407 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_408 : FiniteTemplate HasSnaky 10 required_408 envelope_408 := by
  refine finite_compose HasSnaky 9 childrenC_408 childrenD_408 finite_children_work_408 (1, 5)
    required_408 envelope_408 pivot_mem_408 child_required_sub_408 child_envelope_sub_408 ?_
  intro b hb
  exact common_sub_408 (mem_commonEnvelope childrenD_408 b hb)

theorem finite_children_work_409 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_409 j) (childrenD_409 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_127 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_407 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_409 : FiniteTemplate HasSnaky 10 required_409 envelope_409 := by
  refine finite_compose HasSnaky 9 childrenC_409 childrenD_409 finite_children_work_409 (1, 4)
    required_409 envelope_409 pivot_mem_409 child_required_sub_409 child_envelope_sub_409 ?_
  intro b hb
  exact common_sub_409 (mem_commonEnvelope childrenD_409 b hb)

theorem finite_children_work_410 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_410 j) (childrenD_410 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_407 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_410 : FiniteTemplate HasSnaky 10 required_410 envelope_410 := by
  refine finite_compose HasSnaky 9 childrenC_410 childrenD_410 finite_children_work_410 (1, 5)
    required_410 envelope_410 pivot_mem_410 child_required_sub_410 child_envelope_sub_410 ?_
  intro b hb
  exact common_sub_410 (mem_commonEnvelope childrenD_410 b hb)

theorem finite_children_work_411 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_411 j) (childrenD_411 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_65 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_407 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_411 : FiniteTemplate HasSnaky 10 required_411 envelope_411 := by
  refine finite_compose HasSnaky 9 childrenC_411 childrenD_411 finite_children_work_411 (1, 5)
    required_411 envelope_411 pivot_mem_411 child_required_sub_411 child_envelope_sub_411 ?_
  intro b hb
  exact common_sub_411 (mem_commonEnvelope childrenD_411 b hb)

theorem finite_children_work_444 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_444 j) (childrenD_444 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_443 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_444 : FiniteTemplate HasSnaky 10 required_444 envelope_444 := by
  refine finite_compose HasSnaky 9 childrenC_444 childrenD_444 finite_children_work_444 (1, 4)
    required_444 envelope_444 pivot_mem_444 child_required_sub_444 child_envelope_sub_444 ?_
  intro b hb
  exact common_sub_444 (mem_commonEnvelope childrenD_444 b hb)

theorem finite_children_work_459 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_459 j) (childrenD_459 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_13 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 6 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 4 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_458 4 (0, 7)).mono (by decide +kernel)

theorem finite_row_works_459 : FiniteTemplate HasSnaky 10 required_459 envelope_459 := by
  refine finite_compose HasSnaky 9 childrenC_459 childrenD_459 finite_children_work_459 (1, 6)
    required_459 envelope_459 pivot_mem_459 child_required_sub_459 child_envelope_sub_459 ?_
  intro b hb
  exact common_sub_459 (mem_commonEnvelope childrenD_459 b hb)

theorem finite_children_work_460 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_460 j) (childrenD_460 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_458 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_460 : FiniteTemplate HasSnaky 10 required_460 envelope_460 := by
  refine finite_compose HasSnaky 9 childrenC_460 childrenD_460 finite_children_work_460 (1, 4)
    required_460 envelope_460 pivot_mem_460 child_required_sub_460 child_envelope_sub_460 ?_
  intro b hb
  exact common_sub_460 (mem_commonEnvelope childrenD_460 b hb)

theorem finite_children_work_461 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_461 j) (childrenD_461 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 5 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_100.mono (by decide +kernel)
  · exact finite_row_works_429.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_461 : FiniteTemplate HasSnaky 10 required_461 envelope_461 := by
  refine finite_compose HasSnaky 9 childrenC_461 childrenD_461 finite_children_work_461 (3, 3)
    required_461 envelope_461 pivot_mem_461 child_required_sub_461 child_envelope_sub_461 ?_
  intro b hb
  exact common_sub_461 (mem_commonEnvelope childrenD_461 b hb)

theorem finite_children_work_475 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_475 j) (childrenD_475 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 6 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_396 4 (0, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_475 : FiniteTemplate HasSnaky 10 required_475 envelope_475 := by
  refine finite_compose HasSnaky 9 childrenC_475 childrenD_475 finite_children_work_475 (2, 5)
    required_475 envelope_475 pivot_mem_475 child_required_sub_475 child_envelope_sub_475 ?_
  intro b hb
  exact common_sub_475 (mem_commonEnvelope childrenD_475 b hb)

theorem finite_children_work_476 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_476 j) (childrenD_476 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_264 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 3 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_476 : FiniteTemplate HasSnaky 10 required_476 envelope_476 := by
  refine finite_compose HasSnaky 9 childrenC_476 childrenD_476 finite_children_work_476 (3, 5)
    required_476 envelope_476 pivot_mem_476 child_required_sub_476 child_envelope_sub_476 ?_
  intro b hb
  exact common_sub_476 (mem_commonEnvelope childrenD_476 b hb)

theorem finite_children_work_479_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_479_i0 j) (childrenD_479_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_386 5 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_479_i0 : FiniteTemplate HasSnaky 6 required_479_i0 envelope_479_i0 := by
  refine finite_compose HasSnaky 5 childrenC_479_i0 childrenD_479_i0 finite_children_work_479_i0 (3, 2)
    required_479_i0 envelope_479_i0 pivot_mem_479_i0 child_required_sub_479_i0 child_envelope_sub_479_i0 ?_
  intro b hb
  exact common_sub_479_i0 (mem_commonEnvelope childrenD_479_i0 b hb)

theorem finite_children_work_479 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_479 j) (childrenD_479 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 4 (2, 7)).mono (by decide +kernel)
  · exact finite_row_works_479_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_479 : FiniteTemplate HasSnaky 10 required_479 envelope_479 := by
  refine finite_compose HasSnaky 9 childrenC_479 childrenD_479 finite_children_work_479 (3, 5)
    required_479 envelope_479 pivot_mem_479 child_required_sub_479 child_envelope_sub_479 ?_
  intro b hb
  exact common_sub_479 (mem_commonEnvelope childrenD_479 b hb)

theorem finite_children_work_480 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_480 j) (childrenD_480 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_298 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 7 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_477 5 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_480 : FiniteTemplate HasSnaky 10 required_480 envelope_480 := by
  refine finite_compose HasSnaky 9 childrenC_480 childrenD_480 finite_children_work_480 (3, 3)
    required_480 envelope_480 pivot_mem_480 child_required_sub_480 child_envelope_sub_480 ?_
  intro b hb
  exact common_sub_480 (mem_commonEnvelope childrenD_480 b hb)

theorem finite_children_work_481 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_481 j) (childrenD_481 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_457 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_477 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_481 : FiniteTemplate HasSnaky 10 required_481 envelope_481 := by
  refine finite_compose HasSnaky 9 childrenC_481 childrenD_481 finite_children_work_481 (2, 4)
    required_481 envelope_481 pivot_mem_481 child_required_sub_481 child_envelope_sub_481 ?_
  intro b hb
  exact common_sub_481 (mem_commonEnvelope childrenD_481 b hb)

theorem finite_children_work_483 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_483 j) (childrenD_483 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_458 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_483 : FiniteTemplate HasSnaky 10 required_483 envelope_483 := by
  refine finite_compose HasSnaky 9 childrenC_483 childrenD_483 finite_children_work_483 (2, 5)
    required_483 envelope_483 pivot_mem_483 child_required_sub_483 child_envelope_sub_483 ?_
  intro b hb
  exact common_sub_483 (mem_commonEnvelope childrenD_483 b hb)

theorem finite_children_work_491_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_491_i0 j) (childrenD_491_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_60 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_60 7 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_83 4 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_106 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_491_i0 : FiniteTemplate HasSnaky 5 required_491_i0 envelope_491_i0 := by
  refine finite_compose HasSnaky 4 childrenC_491_i0 childrenD_491_i0 finite_children_work_491_i0 (5, 3)
    required_491_i0 envelope_491_i0 pivot_mem_491_i0 child_required_sub_491_i0 child_envelope_sub_491_i0 ?_
  intro b hb
  exact common_sub_491_i0 (mem_commonEnvelope childrenD_491_i0 b hb)

theorem finite_children_work_491_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_491_i1 j) (childrenD_491_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_60 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_70 7 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_345 4 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_491_i1 : FiniteTemplate HasSnaky 9 required_491_i1 envelope_491_i1 := by
  refine finite_compose HasSnaky 8 childrenC_491_i1 childrenD_491_i1 finite_children_work_491_i1 (5, 3)
    required_491_i1 envelope_491_i1 pivot_mem_491_i1 child_required_sub_491_i1 child_envelope_sub_491_i1 ?_
  intro b hb
  exact common_sub_491_i1 (mem_commonEnvelope childrenD_491_i1 b hb)

theorem finite_children_work_491 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_491 j) (childrenD_491 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_270 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_491_i0.mono (by decide +kernel)
  · exact finite_row_works_491_i1.mono (by decide +kernel)

theorem finite_row_works_491 : FiniteTemplate HasSnaky 10 required_491 envelope_491 := by
  refine finite_compose HasSnaky 9 childrenC_491 childrenD_491 finite_children_work_491 (3, 3)
    required_491 envelope_491 pivot_mem_491 child_required_sub_491 child_envelope_sub_491 ?_
  intro b hb
  exact common_sub_491 (mem_commonEnvelope childrenD_491 b hb)

theorem finite_children_work_508 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_508 j) (childrenD_508 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_13 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_297.mono (by decide +kernel)
  · exact finite_row_works_298.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 4 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_508 : FiniteTemplate HasSnaky 10 required_508 envelope_508 := by
  refine finite_compose HasSnaky 9 childrenC_508 childrenD_508 finite_children_work_508 (4, 3)
    required_508 envelope_508 pivot_mem_508 child_required_sub_508 child_envelope_sub_508 ?_
  intro b hb
  exact common_sub_508 (mem_commonEnvelope childrenD_508 b hb)

theorem finite_children_work_509 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_509 j) (childrenD_509 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_127 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_128 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_509 : FiniteTemplate HasSnaky 10 required_509 envelope_509 := by
  refine finite_compose HasSnaky 9 childrenC_509 childrenD_509 finite_children_work_509 (4, 3)
    required_509 envelope_509 pivot_mem_509 child_required_sub_509 child_envelope_sub_509 ?_
  intro b hb
  exact common_sub_509 (mem_commonEnvelope childrenD_509 b hb)

theorem finite_children_work_520 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_520 j) (childrenD_520 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 3 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_317 6 (6, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_519 2 (6, 2)).mono (by decide +kernel)

theorem finite_row_works_520 : FiniteTemplate HasSnaky 10 required_520 envelope_520 := by
  refine finite_compose HasSnaky 9 childrenC_520 childrenD_520 finite_children_work_520 (4, 5)
    required_520 envelope_520 pivot_mem_520 child_required_sub_520 child_envelope_sub_520 ?_
  intro b hb
  exact common_sub_520 (mem_commonEnvelope childrenD_520 b hb)

end FiniteCongruenceChecks.SnakyFinite
