/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_336_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_336_i1 j) (childrenD_336_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 2 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_336_i1 : FiniteTemplate HasSnaky 4 required_336_i1 envelope_336_i1 := by
  refine finite_compose HasSnaky 3 childrenC_336_i1 childrenD_336_i1 finite_children_work_336_i1 (1, 5)
    required_336_i1 envelope_336_i1 pivot_mem_336_i1 child_required_sub_336_i1 child_envelope_sub_336_i1 ?_
  intro b hb
  exact common_sub_336_i1 (mem_commonEnvelope childrenD_336_i1 b hb)

theorem finite_children_work_336_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_336_i0 j) (childrenD_336_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_336_i1.mono (by decide +kernel)

theorem finite_row_works_336_i0 : FiniteTemplate HasSnaky 5 required_336_i0 envelope_336_i0 := by
  refine finite_compose HasSnaky 4 childrenC_336_i0 childrenD_336_i0 finite_children_work_336_i0 (2, 3)
    required_336_i0 envelope_336_i0 pivot_mem_336_i0 child_required_sub_336_i0 child_envelope_sub_336_i0 ?_
  intro b hb
  exact common_sub_336_i0 (mem_commonEnvelope childrenD_336_i0 b hb)

theorem finite_children_work_336 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_336 j) (childrenD_336 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_336_i0.mono (by decide +kernel)

theorem finite_row_works_336 : FiniteTemplate HasSnaky 6 required_336 envelope_336 := by
  refine finite_compose HasSnaky 5 childrenC_336 childrenD_336 finite_children_work_336 (1, 4)
    required_336 envelope_336 pivot_mem_336 child_required_sub_336 child_envelope_sub_336 ?_
  intro b hb
  exact common_sub_336 (mem_commonEnvelope childrenD_336 b hb)

theorem finite_children_work_340_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_340_i0 j) (childrenD_340_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_91 0 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_340_i0 : FiniteTemplate HasSnaky 5 required_340_i0 envelope_340_i0 := by
  refine finite_compose HasSnaky 4 childrenC_340_i0 childrenD_340_i0 finite_children_work_340_i0 (1, 6)
    required_340_i0 envelope_340_i0 pivot_mem_340_i0 child_required_sub_340_i0 child_envelope_sub_340_i0 ?_
  intro b hb
  exact common_sub_340_i0 (mem_commonEnvelope childrenD_340_i0 b hb)

theorem finite_children_work_340 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_340 j) (childrenD_340 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_139 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_148 4 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_340_i0.mono (by decide +kernel)

theorem finite_row_works_340 : FiniteTemplate HasSnaky 6 required_340 envelope_340 := by
  refine finite_compose HasSnaky 5 childrenC_340 childrenD_340 finite_children_work_340 (0, 6)
    required_340 envelope_340 pivot_mem_340 child_required_sub_340 child_envelope_sub_340 ?_
  intro b hb
  exact common_sub_340 (mem_commonEnvelope childrenD_340 b hb)

theorem finite_children_work_343 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_343 j) (childrenD_343 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_342.mono (by decide +kernel)

theorem finite_row_works_343 : FiniteTemplate HasSnaky 6 required_343 envelope_343 := by
  refine finite_compose HasSnaky 5 childrenC_343 childrenD_343 finite_children_work_343 (3, 3)
    required_343 envelope_343 pivot_mem_343 child_required_sub_343 child_envelope_sub_343 ?_
  intro b hb
  exact common_sub_343 (mem_commonEnvelope childrenD_343 b hb)

theorem finite_children_work_346 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_346 j) (childrenD_346 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_342 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_346 : FiniteTemplate HasSnaky 6 required_346 envelope_346 := by
  refine finite_compose HasSnaky 5 childrenC_346 childrenD_346 finite_children_work_346 (2, 3)
    required_346 envelope_346 pivot_mem_346 child_required_sub_346 child_envelope_sub_346 ?_
  intro b hb
  exact common_sub_346 (mem_commonEnvelope childrenD_346 b hb)

theorem finite_children_work_348_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_348_i0 j) (childrenD_348_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_311 1 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_348_i0 : FiniteTemplate HasSnaky 5 required_348_i0 envelope_348_i0 := by
  refine finite_compose HasSnaky 4 childrenC_348_i0 childrenD_348_i0 finite_children_work_348_i0 (3, 0)
    required_348_i0 envelope_348_i0 pivot_mem_348_i0 child_required_sub_348_i0 child_envelope_sub_348_i0 ?_
  intro b hb
  exact common_sub_348_i0 (mem_commonEnvelope childrenD_348_i0 b hb)

theorem finite_children_work_348 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_348 j) (childrenD_348 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_348_i0.mono (by decide +kernel)

theorem finite_row_works_348 : FiniteTemplate HasSnaky 6 required_348 envelope_348 := by
  refine finite_compose HasSnaky 5 childrenC_348 childrenD_348 finite_children_work_348 (3, 1)
    required_348 envelope_348 pivot_mem_348 child_required_sub_348 child_envelope_sub_348 ?_
  intro b hb
  exact common_sub_348 (mem_commonEnvelope childrenD_348 b hb)

theorem finite_children_work_349_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_349_i0 j) (childrenD_349_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_54 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_349_i0 : FiniteTemplate HasSnaky 5 required_349_i0 envelope_349_i0 := by
  refine finite_compose HasSnaky 4 childrenC_349_i0 childrenD_349_i0 finite_children_work_349_i0 (4, 3)
    required_349_i0 envelope_349_i0 pivot_mem_349_i0 child_required_sub_349_i0 child_envelope_sub_349_i0 ?_
  intro b hb
  exact common_sub_349_i0 (mem_commonEnvelope childrenD_349_i0 b hb)

theorem finite_children_work_349 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_349 j) (childrenD_349 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_165 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_216 4 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_349_i0.mono (by decide +kernel)

theorem finite_row_works_349 : FiniteTemplate HasSnaky 6 required_349 envelope_349 := by
  refine finite_compose HasSnaky 5 childrenC_349 childrenD_349 finite_children_work_349 (3, 5)
    required_349 envelope_349 pivot_mem_349 child_required_sub_349 child_envelope_sub_349 ?_
  intro b hb
  exact common_sub_349 (mem_commonEnvelope childrenD_349 b hb)

theorem finite_children_work_358 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_358 j) (childrenD_358 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_357 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_358 : FiniteTemplate HasSnaky 6 required_358 envelope_358 := by
  refine finite_compose HasSnaky 5 childrenC_358 childrenD_358 finite_children_work_358 (2, 4)
    required_358 envelope_358 pivot_mem_358 child_required_sub_358 child_envelope_sub_358 ?_
  intro b hb
  exact common_sub_358 (mem_commonEnvelope childrenD_358 b hb)

theorem finite_children_work_360_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_360_i0 j) (childrenD_360_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_45 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_360_i0 : FiniteTemplate HasSnaky 4 required_360_i0 envelope_360_i0 := by
  refine finite_compose HasSnaky 3 childrenC_360_i0 childrenD_360_i0 finite_children_work_360_i0 (2, 3)
    required_360_i0 envelope_360_i0 pivot_mem_360_i0 child_required_sub_360_i0 child_envelope_sub_360_i0 ?_
  intro b hb
  exact common_sub_360_i0 (mem_commonEnvelope childrenD_360_i0 b hb)

theorem finite_children_work_360 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_360 j) (childrenD_360 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_347 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_360_i0.mono (by decide +kernel)

theorem finite_row_works_360 : FiniteTemplate HasSnaky 6 required_360 envelope_360 := by
  refine finite_compose HasSnaky 5 childrenC_360 childrenD_360 finite_children_work_360 (2, 4)
    required_360 envelope_360 pivot_mem_360 child_required_sub_360 child_envelope_sub_360 ?_
  intro b hb
  exact common_sub_360 (mem_commonEnvelope childrenD_360 b hb)

theorem finite_children_work_363 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_363 j) (childrenD_363 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_362.mono (by decide +kernel)

theorem finite_row_works_363 : FiniteTemplate HasSnaky 6 required_363 envelope_363 := by
  refine finite_compose HasSnaky 5 childrenC_363 childrenD_363 finite_children_work_363 (4, 4)
    required_363 envelope_363 pivot_mem_363 child_required_sub_363 child_envelope_sub_363 ?_
  intro b hb
  exact common_sub_363 (mem_commonEnvelope childrenD_363 b hb)

theorem finite_children_work_364 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_364 j) (childrenD_364 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_362.mono (by decide +kernel)

theorem finite_row_works_364 : FiniteTemplate HasSnaky 6 required_364 envelope_364 := by
  refine finite_compose HasSnaky 5 childrenC_364 childrenD_364 finite_children_work_364 (4, 4)
    required_364 envelope_364 pivot_mem_364 child_required_sub_364 child_envelope_sub_364 ?_
  intro b hb
  exact common_sub_364 (mem_commonEnvelope childrenD_364 b hb)

theorem finite_children_work_367 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_367 j) (childrenD_367 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 6 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_366.mono (by decide +kernel)

theorem finite_row_works_367 : FiniteTemplate HasSnaky 6 required_367 envelope_367 := by
  refine finite_compose HasSnaky 5 childrenC_367 childrenD_367 finite_children_work_367 (1, 5)
    required_367 envelope_367 pivot_mem_367 child_required_sub_367 child_envelope_sub_367 ?_
  intro b hb
  exact common_sub_367 (mem_commonEnvelope childrenD_367 b hb)

theorem finite_children_work_369_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_369_i0 j) (childrenD_369_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_365 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_369_i0 : FiniteTemplate HasSnaky 5 required_369_i0 envelope_369_i0 := by
  refine finite_compose HasSnaky 4 childrenC_369_i0 childrenD_369_i0 finite_children_work_369_i0 (1, 7)
    required_369_i0 envelope_369_i0 pivot_mem_369_i0 child_required_sub_369_i0 child_envelope_sub_369_i0 ?_
  intro b hb
  exact common_sub_369_i0 (mem_commonEnvelope childrenD_369_i0 b hb)

theorem finite_children_work_369 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_369 j) (childrenD_369 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 6 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 6 (1, 8)).mono (by decide +kernel)
  · exact finite_row_works_369_i0.mono (by decide +kernel)

theorem finite_row_works_369 : FiniteTemplate HasSnaky 6 required_369 envelope_369 := by
  refine finite_compose HasSnaky 5 childrenC_369 childrenD_369 finite_children_work_369 (1, 6)
    required_369 envelope_369 pivot_mem_369 child_required_sub_369 child_envelope_sub_369 ?_
  intro b hb
  exact common_sub_369 (mem_commonEnvelope childrenD_369 b hb)

theorem finite_children_work_371_i2 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_371_i2 j) (childrenD_371_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_371_i2 : FiniteTemplate HasSnaky 2 required_371_i2 envelope_371_i2 := by
  refine finite_compose HasSnaky 1 childrenC_371_i2 childrenD_371_i2 finite_children_work_371_i2 (3, 2)
    required_371_i2 envelope_371_i2 pivot_mem_371_i2 child_required_sub_371_i2 child_envelope_sub_371_i2 ?_
  intro b hb
  exact common_sub_371_i2 (mem_commonEnvelope childrenD_371_i2 b hb)

theorem finite_children_work_371_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_371_i1 j) (childrenD_371_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_210 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_371_i2.mono (by decide +kernel)

theorem finite_row_works_371_i1 : FiniteTemplate HasSnaky 3 required_371_i1 envelope_371_i1 := by
  refine finite_compose HasSnaky 2 childrenC_371_i1 childrenD_371_i1 finite_children_work_371_i1 (2, 2)
    required_371_i1 envelope_371_i1 pivot_mem_371_i1 child_required_sub_371_i1 child_envelope_sub_371_i1 ?_
  intro b hb
  exact common_sub_371_i1 (mem_commonEnvelope childrenD_371_i1 b hb)

theorem finite_children_work_371_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_371_i0 j) (childrenD_371_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_371_i1.mono (by decide +kernel)

theorem finite_row_works_371_i0 : FiniteTemplate HasSnaky 4 required_371_i0 envelope_371_i0 := by
  refine finite_compose HasSnaky 3 childrenC_371_i0 childrenD_371_i0 finite_children_work_371_i0 (5, 1)
    required_371_i0 envelope_371_i0 pivot_mem_371_i0 child_required_sub_371_i0 child_envelope_sub_371_i0 ?_
  intro b hb
  exact common_sub_371_i0 (mem_commonEnvelope childrenD_371_i0 b hb)

theorem finite_children_work_371 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_371 j) (childrenD_371 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_370 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_371_i0.mono (by decide +kernel)

theorem finite_row_works_371 : FiniteTemplate HasSnaky 6 required_371 envelope_371 := by
  refine finite_compose HasSnaky 5 childrenC_371 childrenD_371 finite_children_work_371 (4, 1)
    required_371 envelope_371 pivot_mem_371 child_required_sub_371 child_envelope_sub_371 ?_
  intro b hb
  exact common_sub_371 (mem_commonEnvelope childrenD_371 b hb)

end FiniteCongruenceChecks.SnakyFinite
