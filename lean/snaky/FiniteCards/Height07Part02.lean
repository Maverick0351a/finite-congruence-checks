/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_361 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_361 j) (childrenD_361 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_57 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_360 1 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_361 : FiniteTemplate HasSnaky 7 required_361 envelope_361 := by
  refine finite_compose HasSnaky 6 childrenC_361 childrenD_361 finite_children_work_361 (3, 1)
    required_361 envelope_361 pivot_mem_361 child_required_sub_361 child_envelope_sub_361 ?_
  intro b hb
  exact common_sub_361 (mem_commonEnvelope childrenD_361 b hb)

theorem finite_children_work_372_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_372_i0 j) (childrenD_372_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_81 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_351 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_372_i0 : FiniteTemplate HasSnaky 6 required_372_i0 envelope_372_i0 := by
  refine finite_compose HasSnaky 5 childrenC_372_i0 childrenD_372_i0 finite_children_work_372_i0 (4, 4)
    required_372_i0 envelope_372_i0 pivot_mem_372_i0 child_required_sub_372_i0 child_envelope_sub_372_i0 ?_
  intro b hb
  exact common_sub_372_i0 (mem_commonEnvelope childrenD_372_i0 b hb)

theorem finite_children_work_372 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_372 j) (childrenD_372 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_96 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_372_i0.mono (by decide +kernel)

theorem finite_row_works_372 : FiniteTemplate HasSnaky 7 required_372 envelope_372 := by
  refine finite_compose HasSnaky 6 childrenC_372 childrenD_372 finite_children_work_372 (4, 2)
    required_372 envelope_372 pivot_mem_372 child_required_sub_372 child_envelope_sub_372 ?_
  intro b hb
  exact common_sub_372 (mem_commonEnvelope childrenD_372 b hb)

theorem finite_children_work_379 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_379 j) (childrenD_379 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 3 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_378.mono (by decide +kernel)

theorem finite_row_works_379 : FiniteTemplate HasSnaky 7 required_379 envelope_379 := by
  refine finite_compose HasSnaky 6 childrenC_379 childrenD_379 finite_children_work_379 (3, 2)
    required_379 envelope_379 pivot_mem_379 child_required_sub_379 child_envelope_sub_379 ?_
  intro b hb
  exact common_sub_379 (mem_commonEnvelope childrenD_379 b hb)

theorem finite_children_work_385 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_385 j) (childrenD_385 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_115 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_383 7 (5, 4)).mono (by decide +kernel)

theorem finite_row_works_385 : FiniteTemplate HasSnaky 7 required_385 envelope_385 := by
  refine finite_compose HasSnaky 6 childrenC_385 childrenD_385 finite_children_work_385 (3, 3)
    required_385 envelope_385 pivot_mem_385 child_required_sub_385 child_envelope_sub_385 ?_
  intro b hb
  exact common_sub_385 (mem_commonEnvelope childrenD_385 b hb)

theorem finite_children_work_388 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_388 j) (childrenD_388 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_387 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_388 : FiniteTemplate HasSnaky 7 required_388 envelope_388 := by
  refine finite_compose HasSnaky 6 childrenC_388 childrenD_388 finite_children_work_388 (2, 4)
    required_388 envelope_388 pivot_mem_388 child_required_sub_388 child_envelope_sub_388 ?_
  intro b hb
  exact common_sub_388 (mem_commonEnvelope childrenD_388 b hb)

theorem finite_children_work_394 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_394 j) (childrenD_394 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_241.mono (by decide +kernel)
  · exact finite_row_works_392.mono (by decide +kernel)

theorem finite_row_works_394 : FiniteTemplate HasSnaky 7 required_394 envelope_394 := by
  refine finite_compose HasSnaky 6 childrenC_394 childrenD_394 finite_children_work_394 (1, 4)
    required_394 envelope_394 pivot_mem_394 child_required_sub_394 child_envelope_sub_394 ?_
  intro b hb
  exact common_sub_394 (mem_commonEnvelope childrenD_394 b hb)

theorem finite_children_work_404_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_404_i1 j) (childrenD_404_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_354.mono (by decide +kernel)

theorem finite_row_works_404_i1 : FiniteTemplate HasSnaky 5 required_404_i1 envelope_404_i1 := by
  refine finite_compose HasSnaky 4 childrenC_404_i1 childrenD_404_i1 finite_children_work_404_i1 (3, 1)
    required_404_i1 envelope_404_i1 pivot_mem_404_i1 child_required_sub_404_i1 child_envelope_sub_404_i1 ?_
  intro b hb
  exact common_sub_404_i1 (mem_commonEnvelope childrenD_404_i1 b hb)

theorem finite_children_work_404_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_404_i0 j) (childrenD_404_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_404_i1.mono (by decide +kernel)

theorem finite_row_works_404_i0 : FiniteTemplate HasSnaky 6 required_404_i0 envelope_404_i0 := by
  refine finite_compose HasSnaky 5 childrenC_404_i0 childrenD_404_i0 finite_children_work_404_i0 (2, 1)
    required_404_i0 envelope_404_i0 pivot_mem_404_i0 child_required_sub_404_i0 child_envelope_sub_404_i0 ?_
  intro b hb
  exact common_sub_404_i0 (mem_commonEnvelope childrenD_404_i0 b hb)

theorem finite_children_work_404 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_404 j) (childrenD_404 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_404_i0.mono (by decide +kernel)

theorem finite_row_works_404 : FiniteTemplate HasSnaky 7 required_404 envelope_404 := by
  refine finite_compose HasSnaky 6 childrenC_404 childrenD_404 finite_children_work_404 (2, 4)
    required_404 envelope_404 pivot_mem_404 child_required_sub_404 child_envelope_sub_404 ?_
  intro b hb
  exact common_sub_404 (mem_commonEnvelope childrenD_404 b hb)

theorem finite_children_work_415 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_415 j) (childrenD_415 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_414 2 (5, 0)).mono (by decide +kernel)

theorem finite_row_works_415 : FiniteTemplate HasSnaky 7 required_415 envelope_415 := by
  refine finite_compose HasSnaky 6 childrenC_415 childrenD_415 finite_children_work_415 (3, 2)
    required_415 envelope_415 pivot_mem_415 child_required_sub_415 child_envelope_sub_415 ?_
  intro b hb
  exact common_sub_415 (mem_commonEnvelope childrenD_415 b hb)

theorem finite_children_work_418_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_418_i2 j) (childrenD_418_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_418_i2 : FiniteTemplate HasSnaky 4 required_418_i2 envelope_418_i2 := by
  refine finite_compose HasSnaky 3 childrenC_418_i2 childrenD_418_i2 finite_children_work_418_i2 (2, 2)
    required_418_i2 envelope_418_i2 pivot_mem_418_i2 child_required_sub_418_i2 child_envelope_sub_418_i2 ?_
  intro b hb
  exact common_sub_418_i2 (mem_commonEnvelope childrenD_418_i2 b hb)

theorem finite_children_work_418_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_418_i1 j) (childrenD_418_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_25 5 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_418_i2.mono (by decide +kernel)

theorem finite_row_works_418_i1 : FiniteTemplate HasSnaky 5 required_418_i1 envelope_418_i1 := by
  refine finite_compose HasSnaky 4 childrenC_418_i1 childrenD_418_i1 finite_children_work_418_i1 (3, 3)
    required_418_i1 envelope_418_i1 pivot_mem_418_i1 child_required_sub_418_i1 child_envelope_sub_418_i1 ?_
  intro b hb
  exact common_sub_418_i1 (mem_commonEnvelope childrenD_418_i1 b hb)

theorem finite_children_work_418_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_418_i0 j) (childrenD_418_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_418_i1.mono (by decide +kernel)

theorem finite_row_works_418_i0 : FiniteTemplate HasSnaky 6 required_418_i0 envelope_418_i0 := by
  refine finite_compose HasSnaky 5 childrenC_418_i0 childrenD_418_i0 finite_children_work_418_i0 (3, 2)
    required_418_i0 envelope_418_i0 pivot_mem_418_i0 child_required_sub_418_i0 child_envelope_sub_418_i0 ?_
  intro b hb
  exact common_sub_418_i0 (mem_commonEnvelope childrenD_418_i0 b hb)

theorem finite_children_work_418 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_418 j) (childrenD_418 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_418_i0.mono (by decide +kernel)

theorem finite_row_works_418 : FiniteTemplate HasSnaky 7 required_418 envelope_418 := by
  refine finite_compose HasSnaky 6 childrenC_418 childrenD_418 finite_children_work_418 (3, 0)
    required_418 envelope_418 pivot_mem_418 child_required_sub_418 child_envelope_sub_418 ?_
  intro b hb
  exact common_sub_418 (mem_commonEnvelope childrenD_418 b hb)

theorem finite_children_work_422_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_422_i0 j) (childrenD_422_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_69 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_413 5 (5, 1)).mono (by decide +kernel)

theorem finite_row_works_422_i0 : FiniteTemplate HasSnaky 6 required_422_i0 envelope_422_i0 := by
  refine finite_compose HasSnaky 5 childrenC_422_i0 childrenD_422_i0 finite_children_work_422_i0 (4, 2)
    required_422_i0 envelope_422_i0 pivot_mem_422_i0 child_required_sub_422_i0 child_envelope_sub_422_i0 ?_
  intro b hb
  exact common_sub_422_i0 (mem_commonEnvelope childrenD_422_i0 b hb)

theorem finite_children_work_422 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_422 j) (childrenD_422 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_422_i0.mono (by decide +kernel)

theorem finite_row_works_422 : FiniteTemplate HasSnaky 7 required_422 envelope_422 := by
  refine finite_compose HasSnaky 6 childrenC_422 childrenD_422 finite_children_work_422 (2, 2)
    required_422 envelope_422 pivot_mem_422 child_required_sub_422 child_envelope_sub_422 ?_
  intro b hb
  exact common_sub_422 (mem_commonEnvelope childrenD_422 b hb)

theorem finite_children_work_430 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_430 j) (childrenD_430 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_100 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_429 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_430 : FiniteTemplate HasSnaky 7 required_430 envelope_430 := by
  refine finite_compose HasSnaky 6 childrenC_430 childrenD_430 finite_children_work_430 (3, 5)
    required_430 envelope_430 pivot_mem_430 child_required_sub_430 child_envelope_sub_430 ?_
  intro b hb
  exact common_sub_430 (mem_commonEnvelope childrenD_430 b hb)

theorem finite_children_work_431 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_431 j) (childrenD_431 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_160 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_243 2 (5, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_429 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_431 : FiniteTemplate HasSnaky 7 required_431 envelope_431 := by
  refine finite_compose HasSnaky 6 childrenC_431 childrenD_431 finite_children_work_431 (4, 4)
    required_431 envelope_431 pivot_mem_431 child_required_sub_431 child_envelope_sub_431 ?_
  intro b hb
  exact common_sub_431 (mem_commonEnvelope childrenD_431 b hb)

theorem finite_children_work_436 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_436 j) (childrenD_436 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (6, 2)).mono (by decide +kernel)

theorem finite_row_works_436 : FiniteTemplate HasSnaky 7 required_436 envelope_436 := by
  refine finite_compose HasSnaky 6 childrenC_436 childrenD_436 finite_children_work_436 (3, 5)
    required_436 envelope_436 pivot_mem_436 child_required_sub_436 child_envelope_sub_436 ?_
  intro b hb
  exact common_sub_436 (mem_commonEnvelope childrenD_436 b hb)

theorem finite_children_work_437 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_437 j) (childrenD_437 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (6, 2)).mono (by decide +kernel)

theorem finite_row_works_437 : FiniteTemplate HasSnaky 7 required_437 envelope_437 := by
  refine finite_compose HasSnaky 6 childrenC_437 childrenD_437 finite_children_work_437 (3, 4)
    required_437 envelope_437 pivot_mem_437 child_required_sub_437 child_envelope_sub_437 ?_
  intro b hb
  exact common_sub_437 (mem_commonEnvelope childrenD_437 b hb)

theorem finite_children_work_446_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_446_i0 j) (childrenD_446_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_72 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_446_i0 : FiniteTemplate HasSnaky 6 required_446_i0 envelope_446_i0 := by
  refine finite_compose HasSnaky 5 childrenC_446_i0 childrenD_446_i0 finite_children_work_446_i0 (2, 4)
    required_446_i0 envelope_446_i0 pivot_mem_446_i0 child_required_sub_446_i0 child_envelope_sub_446_i0 ?_
  intro b hb
  exact common_sub_446_i0 (mem_commonEnvelope childrenD_446_i0 b hb)

theorem finite_children_work_446 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_446 j) (childrenD_446 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_446_i0.mono (by decide +kernel)

theorem finite_row_works_446 : FiniteTemplate HasSnaky 7 required_446 envelope_446 := by
  refine finite_compose HasSnaky 6 childrenC_446 childrenD_446 finite_children_work_446 (2, 3)
    required_446 envelope_446 pivot_mem_446 child_required_sub_446 child_envelope_sub_446 ?_
  intro b hb
  exact common_sub_446 (mem_commonEnvelope childrenD_446 b hb)

end FiniteCongruenceChecks.SnakyFinite
