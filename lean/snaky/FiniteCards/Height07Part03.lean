/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_447_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_447_i0 j) (childrenD_447_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_445 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_447_i0 : FiniteTemplate HasSnaky 6 required_447_i0 envelope_447_i0 := by
  refine finite_compose HasSnaky 5 childrenC_447_i0 childrenD_447_i0 finite_children_work_447_i0 (2, 3)
    required_447_i0 envelope_447_i0 pivot_mem_447_i0 child_required_sub_447_i0 child_envelope_sub_447_i0 ?_
  intro b hb
  exact common_sub_447_i0 (mem_commonEnvelope childrenD_447_i0 b hb)

theorem finite_children_work_447 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_447 j) (childrenD_447 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_447_i0.mono (by decide +kernel)

theorem finite_row_works_447 : FiniteTemplate HasSnaky 7 required_447 envelope_447 := by
  refine finite_compose HasSnaky 6 childrenC_447 childrenD_447 finite_children_work_447 (2, 4)
    required_447 envelope_447 pivot_mem_447 child_required_sub_447 child_envelope_sub_447 ?_
  intro b hb
  exact common_sub_447 (mem_commonEnvelope childrenD_447 b hb)

theorem finite_children_work_453_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_453_i1 j) (childrenD_453_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_354 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_453_i1 : FiniteTemplate HasSnaky 5 required_453_i1 envelope_453_i1 := by
  refine finite_compose HasSnaky 4 childrenC_453_i1 childrenD_453_i1 finite_children_work_453_i1 (3, 3)
    required_453_i1 envelope_453_i1 pivot_mem_453_i1 child_required_sub_453_i1 child_envelope_sub_453_i1 ?_
  intro b hb
  exact common_sub_453_i1 (mem_commonEnvelope childrenD_453_i1 b hb)

theorem finite_children_work_453_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_453_i0 j) (childrenD_453_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_453_i1.mono (by decide +kernel)

theorem finite_row_works_453_i0 : FiniteTemplate HasSnaky 6 required_453_i0 envelope_453_i0 := by
  refine finite_compose HasSnaky 5 childrenC_453_i0 childrenD_453_i0 finite_children_work_453_i0 (3, 0)
    required_453_i0 envelope_453_i0 pivot_mem_453_i0 child_required_sub_453_i0 child_envelope_sub_453_i0 ?_
  intro b hb
  exact common_sub_453_i0 (mem_commonEnvelope childrenD_453_i0 b hb)

theorem finite_children_work_453 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_453 j) (childrenD_453 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_453_i0.mono (by decide +kernel)

theorem finite_row_works_453 : FiniteTemplate HasSnaky 7 required_453 envelope_453 := by
  refine finite_compose HasSnaky 6 childrenC_453 childrenD_453 finite_children_work_453 (3, 2)
    required_453 envelope_453 pivot_mem_453 child_required_sub_453 child_envelope_sub_453 ?_
  intro b hb
  exact common_sub_453 (mem_commonEnvelope childrenD_453 b hb)

theorem finite_children_work_466 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_466 j) (childrenD_466 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_9.mono (by decide +kernel)
  · exact finite_row_works_465.mono (by decide +kernel)

theorem finite_row_works_466 : FiniteTemplate HasSnaky 7 required_466 envelope_466 := by
  refine finite_compose HasSnaky 6 childrenC_466 childrenD_466 finite_children_work_466 (1, 4)
    required_466 envelope_466 pivot_mem_466 child_required_sub_466 child_envelope_sub_466 ?_
  intro b hb
  exact common_sub_466 (mem_commonEnvelope childrenD_466 b hb)

theorem finite_children_work_469_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_469_i0 j) (childrenD_469_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_101 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 5 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_469_i0 : FiniteTemplate HasSnaky 6 required_469_i0 envelope_469_i0 := by
  refine finite_compose HasSnaky 5 childrenC_469_i0 childrenD_469_i0 finite_children_work_469_i0 (2, 3)
    required_469_i0 envelope_469_i0 pivot_mem_469_i0 child_required_sub_469_i0 child_envelope_sub_469_i0 ?_
  intro b hb
  exact common_sub_469_i0 (mem_commonEnvelope childrenD_469_i0 b hb)

theorem finite_children_work_469 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_469 j) (childrenD_469 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_78 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_469_i0.mono (by decide +kernel)

theorem finite_row_works_469 : FiniteTemplate HasSnaky 7 required_469 envelope_469 := by
  refine finite_compose HasSnaky 6 childrenC_469 childrenD_469 finite_children_work_469 (3, 2)
    required_469 envelope_469 pivot_mem_469 child_required_sub_469 child_envelope_sub_469 ?_
  intro b hb
  exact common_sub_469 (mem_commonEnvelope childrenD_469 b hb)

theorem finite_children_work_472 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_472 j) (childrenD_472 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_471 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_472 : FiniteTemplate HasSnaky 7 required_472 envelope_472 := by
  refine finite_compose HasSnaky 6 childrenC_472 childrenD_472 finite_children_work_472 (4, 3)
    required_472 envelope_472 pivot_mem_472 child_required_sub_472 child_envelope_sub_472 ?_
  intro b hb
  exact common_sub_472 (mem_commonEnvelope childrenD_472 b hb)

theorem finite_children_work_487 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_487 j) (childrenD_487 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_486.mono (by decide +kernel)

theorem finite_row_works_487 : FiniteTemplate HasSnaky 7 required_487 envelope_487 := by
  refine finite_compose HasSnaky 6 childrenC_487 childrenD_487 finite_children_work_487 (2, 3)
    required_487 envelope_487 pivot_mem_487 child_required_sub_487 child_envelope_sub_487 ?_
  intro b hb
  exact common_sub_487 (mem_commonEnvelope childrenD_487 b hb)

theorem finite_children_work_488_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_488_i1 j) (childrenD_488_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_34 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_488_i1 : FiniteTemplate HasSnaky 3 required_488_i1 envelope_488_i1 := by
  refine finite_compose HasSnaky 2 childrenC_488_i1 childrenD_488_i1 finite_children_work_488_i1 (1, 6)
    required_488_i1 envelope_488_i1 pivot_mem_488_i1 child_required_sub_488_i1 child_envelope_sub_488_i1 ?_
  intro b hb
  exact common_sub_488_i1 (mem_commonEnvelope childrenD_488_i1 b hb)

theorem finite_children_work_488_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_488_i0 j) (childrenD_488_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_488_i1.mono (by decide +kernel)

theorem finite_row_works_488_i0 : FiniteTemplate HasSnaky 4 required_488_i0 envelope_488_i0 := by
  refine finite_compose HasSnaky 3 childrenC_488_i0 childrenD_488_i0 finite_children_work_488_i0 (2, 6)
    required_488_i0 envelope_488_i0 pivot_mem_488_i0 child_required_sub_488_i0 child_envelope_sub_488_i0 ?_
  intro b hb
  exact common_sub_488_i0 (mem_commonEnvelope childrenD_488_i0 b hb)

theorem finite_children_work_488_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_488_i2 j) (childrenD_488_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_357 0 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_488_i2 : FiniteTemplate HasSnaky 6 required_488_i2 envelope_488_i2 := by
  refine finite_compose HasSnaky 5 childrenC_488_i2 childrenD_488_i2 finite_children_work_488_i2 (4, 4)
    required_488_i2 envelope_488_i2 pivot_mem_488_i2 child_required_sub_488_i2 child_envelope_sub_488_i2 ?_
  intro b hb
  exact common_sub_488_i2 (mem_commonEnvelope childrenD_488_i2 b hb)

theorem finite_children_work_488 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_488 j) (childrenD_488 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_95 6 (5, 9)).mono (by decide +kernel)
  · exact finite_row_works_488_i0.mono (by decide +kernel)
  · exact finite_row_works_488_i2.mono (by decide +kernel)

theorem finite_row_works_488 : FiniteTemplate HasSnaky 7 required_488 envelope_488 := by
  refine finite_compose HasSnaky 6 childrenC_488 childrenD_488 finite_children_work_488 (4, 6)
    required_488 envelope_488 pivot_mem_488 child_required_sub_488 child_envelope_sub_488 ?_
  intro b hb
  exact common_sub_488 (mem_commonEnvelope childrenD_488 b hb)

theorem finite_children_work_499_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_499_i0 j) (childrenD_499_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_347 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_499_i0 : FiniteTemplate HasSnaky 6 required_499_i0 envelope_499_i0 := by
  refine finite_compose HasSnaky 5 childrenC_499_i0 childrenD_499_i0 finite_children_work_499_i0 (4, 3)
    required_499_i0 envelope_499_i0 pivot_mem_499_i0 child_required_sub_499_i0 child_envelope_sub_499_i0 ?_
  intro b hb
  exact common_sub_499_i0 (mem_commonEnvelope childrenD_499_i0 b hb)

theorem finite_children_work_499_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_499_i1 j) (childrenD_499_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_43 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_499_i1 : FiniteTemplate HasSnaky 4 required_499_i1 envelope_499_i1 := by
  refine finite_compose HasSnaky 3 childrenC_499_i1 childrenD_499_i1 finite_children_work_499_i1 (3, 3)
    required_499_i1 envelope_499_i1 pivot_mem_499_i1 child_required_sub_499_i1 child_envelope_sub_499_i1 ?_
  intro b hb
  exact common_sub_499_i1 (mem_commonEnvelope childrenD_499_i1 b hb)

theorem finite_children_work_499 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_499 j) (childrenD_499 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 2 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_499_i0.mono (by decide +kernel)
  · exact finite_row_works_499_i1.mono (by decide +kernel)

theorem finite_row_works_499 : FiniteTemplate HasSnaky 7 required_499 envelope_499 := by
  refine finite_compose HasSnaky 6 childrenC_499 childrenD_499 finite_children_work_499 (2, 1)
    required_499 envelope_499 pivot_mem_499 child_required_sub_499 child_envelope_sub_499 ?_
  intro b hb
  exact common_sub_499 (mem_commonEnvelope childrenD_499 b hb)

theorem finite_children_work_504_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_504_i1 j) (childrenD_504_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_504_i1 : FiniteTemplate HasSnaky 5 required_504_i1 envelope_504_i1 := by
  refine finite_compose HasSnaky 4 childrenC_504_i1 childrenD_504_i1 finite_children_work_504_i1 (2, 3)
    required_504_i1 envelope_504_i1 pivot_mem_504_i1 child_required_sub_504_i1 child_envelope_sub_504_i1 ?_
  intro b hb
  exact common_sub_504_i1 (mem_commonEnvelope childrenD_504_i1 b hb)

theorem finite_children_work_504_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_504_i0 j) (childrenD_504_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_504_i1.mono (by decide +kernel)

theorem finite_row_works_504_i0 : FiniteTemplate HasSnaky 6 required_504_i0 envelope_504_i0 := by
  refine finite_compose HasSnaky 5 childrenC_504_i0 childrenD_504_i0 finite_children_work_504_i0 (3, 5)
    required_504_i0 envelope_504_i0 pivot_mem_504_i0 child_required_sub_504_i0 child_envelope_sub_504_i0 ?_
  intro b hb
  exact common_sub_504_i0 (mem_commonEnvelope childrenD_504_i0 b hb)

theorem finite_children_work_504 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_504 j) (childrenD_504 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_32 7 (4, 4)).mono (by decide +kernel)
  · exact finite_row_works_504_i0.mono (by decide +kernel)

theorem finite_row_works_504 : FiniteTemplate HasSnaky 7 required_504 envelope_504 := by
  refine finite_compose HasSnaky 6 childrenC_504 childrenD_504 finite_children_work_504 (3, 1)
    required_504 envelope_504 pivot_mem_504 child_required_sub_504 child_envelope_sub_504 ?_
  intro b hb
  exact common_sub_504 (mem_commonEnvelope childrenD_504 b hb)

theorem finite_children_work_507_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_507_i0 j) (childrenD_507_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_33 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_507_i0 : FiniteTemplate HasSnaky 6 required_507_i0 envelope_507_i0 := by
  refine finite_compose HasSnaky 5 childrenC_507_i0 childrenD_507_i0 finite_children_work_507_i0 (3, 5)
    required_507_i0 envelope_507_i0 pivot_mem_507_i0 child_required_sub_507_i0 child_envelope_sub_507_i0 ?_
  intro b hb
  exact common_sub_507_i0 (mem_commonEnvelope childrenD_507_i0 b hb)

theorem finite_children_work_507 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_507 j) (childrenD_507 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_274.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_506 2 (4, 0)).mono (by decide +kernel)
  · exact finite_row_works_507_i0.mono (by decide +kernel)

theorem finite_row_works_507 : FiniteTemplate HasSnaky 7 required_507 envelope_507 := by
  refine finite_compose HasSnaky 6 childrenC_507 childrenD_507 finite_children_work_507 (3, 4)
    required_507 envelope_507 pivot_mem_507 child_required_sub_507 child_envelope_sub_507 ?_
  intro b hb
  exact common_sub_507 (mem_commonEnvelope childrenD_507 b hb)

end FiniteCongruenceChecks.SnakyFinite
