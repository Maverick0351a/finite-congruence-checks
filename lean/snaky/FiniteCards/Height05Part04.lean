/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height04Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_356_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_356_i0 j) (childrenD_356_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_121 7 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_356_i0 : FiniteTemplate HasSnaky 4 required_356_i0 envelope_356_i0 := by
  refine finite_compose HasSnaky 3 childrenC_356_i0 childrenD_356_i0 finite_children_work_356_i0 (2, 3)
    required_356_i0 envelope_356_i0 pivot_mem_356_i0 child_required_sub_356_i0 child_envelope_sub_356_i0 ?_
  intro b hb
  exact common_sub_356_i0 (mem_commonEnvelope childrenD_356_i0 b hb)

theorem finite_children_work_356 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_356 j) (childrenD_356 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_356_i0.mono (by decide +kernel)

theorem finite_row_works_356 : FiniteTemplate HasSnaky 5 required_356 envelope_356 := by
  refine finite_compose HasSnaky 4 childrenC_356 childrenD_356 finite_children_work_356 (3, 5)
    required_356 envelope_356 pivot_mem_356 child_required_sub_356 child_envelope_sub_356 ?_
  intro b hb
  exact common_sub_356 (mem_commonEnvelope childrenD_356 b hb)

theorem finite_children_work_357_i2 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_357_i2 j) (childrenD_357_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 2 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_357_i2 : FiniteTemplate HasSnaky 2 required_357_i2 envelope_357_i2 := by
  refine finite_compose HasSnaky 1 childrenC_357_i2 childrenD_357_i2 finite_children_work_357_i2 (1, 4)
    required_357_i2 envelope_357_i2 pivot_mem_357_i2 child_required_sub_357_i2 child_envelope_sub_357_i2 ?_
  intro b hb
  exact common_sub_357_i2 (mem_commonEnvelope childrenD_357_i2 b hb)

theorem finite_children_work_357_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_357_i1 j) (childrenD_357_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_357_i2.mono (by decide +kernel)

theorem finite_row_works_357_i1 : FiniteTemplate HasSnaky 3 required_357_i1 envelope_357_i1 := by
  refine finite_compose HasSnaky 2 childrenC_357_i1 childrenD_357_i1 finite_children_work_357_i1 (1, 3)
    required_357_i1 envelope_357_i1 pivot_mem_357_i1 child_required_sub_357_i1 child_envelope_sub_357_i1 ?_
  intro b hb
  exact common_sub_357_i1 (mem_commonEnvelope childrenD_357_i1 b hb)

theorem finite_children_work_357_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_357_i0 j) (childrenD_357_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_357_i1.mono (by decide +kernel)

theorem finite_row_works_357_i0 : FiniteTemplate HasSnaky 4 required_357_i0 envelope_357_i0 := by
  refine finite_compose HasSnaky 3 childrenC_357_i0 childrenD_357_i0 finite_children_work_357_i0 (4, 3)
    required_357_i0 envelope_357_i0 pivot_mem_357_i0 child_required_sub_357_i0 child_envelope_sub_357_i0 ?_
  intro b hb
  exact common_sub_357_i0 (mem_commonEnvelope childrenD_357_i0 b hb)

theorem finite_children_work_357 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_357 j) (childrenD_357 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_357_i0.mono (by decide +kernel)

theorem finite_row_works_357 : FiniteTemplate HasSnaky 5 required_357 envelope_357 := by
  refine finite_compose HasSnaky 4 childrenC_357 childrenD_357 finite_children_work_357 (2, 3)
    required_357 envelope_357 pivot_mem_357 child_required_sub_357 child_envelope_sub_357 ?_
  intro b hb
  exact common_sub_357 (mem_commonEnvelope childrenD_357 b hb)

theorem finite_children_work_359_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_359_i0 j) (childrenD_359_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_359_i0 : FiniteTemplate HasSnaky 4 required_359_i0 envelope_359_i0 := by
  refine finite_compose HasSnaky 3 childrenC_359_i0 childrenD_359_i0 finite_children_work_359_i0 (1, 6)
    required_359_i0 envelope_359_i0 pivot_mem_359_i0 child_required_sub_359_i0 child_envelope_sub_359_i0 ?_
  intro b hb
  exact common_sub_359_i0 (mem_commonEnvelope childrenD_359_i0 b hb)

theorem finite_children_work_359 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_359 j) (childrenD_359 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_359_i0.mono (by decide +kernel)

theorem finite_row_works_359 : FiniteTemplate HasSnaky 5 required_359 envelope_359 := by
  refine finite_compose HasSnaky 4 childrenC_359 childrenD_359 finite_children_work_359 (1, 4)
    required_359 envelope_359 pivot_mem_359 child_required_sub_359 child_envelope_sub_359 ?_
  intro b hb
  exact common_sub_359 (mem_commonEnvelope childrenD_359 b hb)

theorem finite_children_work_362_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_362_i0 j) (childrenD_362_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 6 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_362_i0 : FiniteTemplate HasSnaky 4 required_362_i0 envelope_362_i0 := by
  refine finite_compose HasSnaky 3 childrenC_362_i0 childrenD_362_i0 finite_children_work_362_i0 (1, 4)
    required_362_i0 envelope_362_i0 pivot_mem_362_i0 child_required_sub_362_i0 child_envelope_sub_362_i0 ?_
  intro b hb
  exact common_sub_362_i0 (mem_commonEnvelope childrenD_362_i0 b hb)

theorem finite_children_work_362 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_362 j) (childrenD_362 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_362_i0.mono (by decide +kernel)

theorem finite_row_works_362 : FiniteTemplate HasSnaky 5 required_362 envelope_362 := by
  refine finite_compose HasSnaky 4 childrenC_362 childrenD_362 finite_children_work_362 (1, 3)
    required_362 envelope_362 pivot_mem_362 child_required_sub_362 child_envelope_sub_362 ?_
  intro b hb
  exact common_sub_362 (mem_commonEnvelope childrenD_362 b hb)

theorem finite_children_work_366 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_366 j) (childrenD_366 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_365 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_366 : FiniteTemplate HasSnaky 5 required_366 envelope_366 := by
  refine finite_compose HasSnaky 4 childrenC_366 childrenD_366 finite_children_work_366 (1, 1)
    required_366 envelope_366 pivot_mem_366 child_required_sub_366 child_envelope_sub_366 ?_
  intro b hb
  exact common_sub_366 (mem_commonEnvelope childrenD_366 b hb)

theorem finite_children_work_370_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_370_i0 j) (childrenD_370_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_210.mono (by decide +kernel)

theorem finite_row_works_370_i0 : FiniteTemplate HasSnaky 4 required_370_i0 envelope_370_i0 := by
  refine finite_compose HasSnaky 3 childrenC_370_i0 childrenD_370_i0 finite_children_work_370_i0 (1, 2)
    required_370_i0 envelope_370_i0 pivot_mem_370_i0 child_required_sub_370_i0 child_envelope_sub_370_i0 ?_
  intro b hb
  exact common_sub_370_i0 (mem_commonEnvelope childrenD_370_i0 b hb)

theorem finite_children_work_370 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_370 j) (childrenD_370 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_370_i0.mono (by decide +kernel)

theorem finite_row_works_370 : FiniteTemplate HasSnaky 5 required_370 envelope_370 := by
  refine finite_compose HasSnaky 4 childrenC_370 childrenD_370 finite_children_work_370 (4, 1)
    required_370 envelope_370 pivot_mem_370 child_required_sub_370 child_envelope_sub_370 ?_
  intro b hb
  exact common_sub_370 (mem_commonEnvelope childrenD_370 b hb)

theorem finite_children_work_377 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_377 j) (childrenD_377 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_9.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_376 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_377 : FiniteTemplate HasSnaky 5 required_377 envelope_377 := by
  refine finite_compose HasSnaky 4 childrenC_377 childrenD_377 finite_children_work_377 (1, 4)
    required_377 envelope_377 pivot_mem_377 child_required_sub_377 child_envelope_sub_377 ?_
  intro b hb
  exact common_sub_377 (mem_commonEnvelope childrenD_377 b hb)

theorem finite_children_work_382 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_382 j) (childrenD_382 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 2 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_381 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_382 : FiniteTemplate HasSnaky 5 required_382 envelope_382 := by
  refine finite_compose HasSnaky 4 childrenC_382 childrenD_382 finite_children_work_382 (1, 4)
    required_382 envelope_382 pivot_mem_382 child_required_sub_382 child_envelope_sub_382 ?_
  intro b hb
  exact common_sub_382 (mem_commonEnvelope childrenD_382 b hb)

theorem finite_children_work_383_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_383_i0 j) (childrenD_383_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_219 4 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_383_i0 : FiniteTemplate HasSnaky 4 required_383_i0 envelope_383_i0 := by
  refine finite_compose HasSnaky 3 childrenC_383_i0 childrenD_383_i0 finite_children_work_383_i0 (3, 3)
    required_383_i0 envelope_383_i0 pivot_mem_383_i0 child_required_sub_383_i0 child_envelope_sub_383_i0 ?_
  intro b hb
  exact common_sub_383_i0 (mem_commonEnvelope childrenD_383_i0 b hb)

theorem finite_children_work_383 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_383 j) (childrenD_383 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_383_i0.mono (by decide +kernel)

theorem finite_row_works_383 : FiniteTemplate HasSnaky 5 required_383 envelope_383 := by
  refine finite_compose HasSnaky 4 childrenC_383 childrenD_383 finite_children_work_383 (3, 1)
    required_383 envelope_383 pivot_mem_383 child_required_sub_383 child_envelope_sub_383 ?_
  intro b hb
  exact common_sub_383 (mem_commonEnvelope childrenD_383 b hb)

theorem finite_children_work_386_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_386_i1 j) (childrenD_386_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_386_i1 : FiniteTemplate HasSnaky 3 required_386_i1 envelope_386_i1 := by
  refine finite_compose HasSnaky 2 childrenC_386_i1 childrenD_386_i1 finite_children_work_386_i1 (3, 4)
    required_386_i1 envelope_386_i1 pivot_mem_386_i1 child_required_sub_386_i1 child_envelope_sub_386_i1 ?_
  intro b hb
  exact common_sub_386_i1 (mem_commonEnvelope childrenD_386_i1 b hb)

theorem finite_children_work_386_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_386_i0 j) (childrenD_386_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_386_i1.mono (by decide +kernel)

theorem finite_row_works_386_i0 : FiniteTemplate HasSnaky 4 required_386_i0 envelope_386_i0 := by
  refine finite_compose HasSnaky 3 childrenC_386_i0 childrenD_386_i0 finite_children_work_386_i0 (3, 3)
    required_386_i0 envelope_386_i0 pivot_mem_386_i0 child_required_sub_386_i0 child_envelope_sub_386_i0 ?_
  intro b hb
  exact common_sub_386_i0 (mem_commonEnvelope childrenD_386_i0 b hb)

theorem finite_children_work_386 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_386 j) (childrenD_386 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_386_i0.mono (by decide +kernel)

theorem finite_row_works_386 : FiniteTemplate HasSnaky 5 required_386 envelope_386 := by
  refine finite_compose HasSnaky 4 childrenC_386 childrenD_386 finite_children_work_386 (3, 1)
    required_386 envelope_386 pivot_mem_386 child_required_sub_386 child_envelope_sub_386 ?_
  intro b hb
  exact common_sub_386 (mem_commonEnvelope childrenD_386 b hb)

theorem finite_children_work_389_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_389_i0 j) (childrenD_389_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_389_i0 : FiniteTemplate HasSnaky 3 required_389_i0 envelope_389_i0 := by
  refine finite_compose HasSnaky 2 childrenC_389_i0 childrenD_389_i0 finite_children_work_389_i0 (1, 3)
    required_389_i0 envelope_389_i0 pivot_mem_389_i0 child_required_sub_389_i0 child_envelope_sub_389_i0 ?_
  intro b hb
  exact common_sub_389_i0 (mem_commonEnvelope childrenD_389_i0 b hb)

theorem finite_children_work_389 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_389 j) (childrenD_389 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_6.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_21 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_389_i0.mono (by decide +kernel)

theorem finite_row_works_389 : FiniteTemplate HasSnaky 5 required_389 envelope_389 := by
  refine finite_compose HasSnaky 4 childrenC_389 childrenD_389 finite_children_work_389 (0, 4)
    required_389 envelope_389 pivot_mem_389 child_required_sub_389 child_envelope_sub_389 ?_
  intro b hb
  exact common_sub_389 (mem_commonEnvelope childrenD_389 b hb)

end FiniteCongruenceChecks.SnakyFinite
