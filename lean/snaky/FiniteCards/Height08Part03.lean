/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height08Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height06Part06
import FiniteCards.Height07Part02
import FiniteCards.Height07Part03
import FiniteCards.Height07Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_518_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_518_i1 j) (childrenD_518_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_213 5 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_278 1 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_518_i1 : FiniteTemplate HasSnaky 6 required_518_i1 envelope_518_i1 := by
  refine finite_compose HasSnaky 5 childrenC_518_i1 childrenD_518_i1 finite_children_work_518_i1 (3, 7)
    required_518_i1 envelope_518_i1 pivot_mem_518_i1 child_required_sub_518_i1 child_envelope_sub_518_i1 ?_
  intro b hb
  exact common_sub_518_i1 (mem_commonEnvelope childrenD_518_i1 b hb)

theorem finite_children_work_518_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_518_i0 j) (childrenD_518_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 3)).mono (by decide +kernel)
  · exact finite_row_works_518_i1.mono (by decide +kernel)

theorem finite_row_works_518_i0 : FiniteTemplate HasSnaky 7 required_518_i0 envelope_518_i0 := by
  refine finite_compose HasSnaky 6 childrenC_518_i0 childrenD_518_i0 finite_children_work_518_i0 (3, 6)
    required_518_i0 envelope_518_i0 pivot_mem_518_i0 child_required_sub_518_i0 child_envelope_sub_518_i0 ?_
  intro b hb
  exact common_sub_518_i0 (mem_commonEnvelope childrenD_518_i0 b hb)

theorem finite_children_work_518 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_518 j) (childrenD_518 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_61 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_89 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_183 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_518_i0.mono (by decide +kernel)

theorem finite_row_works_518 : FiniteTemplate HasSnaky 8 required_518 envelope_518 := by
  refine finite_compose HasSnaky 7 childrenC_518 childrenD_518 finite_children_work_518 (4, 6)
    required_518 envelope_518 pivot_mem_518 child_required_sub_518 child_envelope_sub_518 ?_
  intro b hb
  exact common_sub_518 (mem_commonEnvelope childrenD_518 b hb)

theorem finite_children_work_523 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_523 j) (childrenD_523 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_122 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_136 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_522 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_523 : FiniteTemplate HasSnaky 8 required_523 envelope_523 := by
  refine finite_compose HasSnaky 7 childrenC_523 childrenD_523 finite_children_work_523 (3, 5)
    required_523 envelope_523 pivot_mem_523 child_required_sub_523 child_envelope_sub_523 ?_
  intro b hb
  exact common_sub_523 (mem_commonEnvelope childrenD_523 b hb)

theorem finite_children_work_524 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_524 j) (childrenD_524 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_88 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_213 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_254 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_522 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_524 : FiniteTemplate HasSnaky 8 required_524 envelope_524 := by
  refine finite_compose HasSnaky 7 childrenC_524 childrenD_524 finite_children_work_524 (3, 5)
    required_524 envelope_524 pivot_mem_524 child_required_sub_524 child_envelope_sub_524 ?_
  intro b hb
  exact common_sub_524 (mem_commonEnvelope childrenD_524 b hb)

theorem finite_children_work_530_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_530_i2 j) (childrenD_530_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_20 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_530_i2 : FiniteTemplate HasSnaky 4 required_530_i2 envelope_530_i2 := by
  refine finite_compose HasSnaky 3 childrenC_530_i2 childrenD_530_i2 finite_children_work_530_i2 (2, 5)
    required_530_i2 envelope_530_i2 pivot_mem_530_i2 child_required_sub_530_i2 child_envelope_sub_530_i2 ?_
  intro b hb
  exact common_sub_530_i2 (mem_commonEnvelope childrenD_530_i2 b hb)

theorem finite_children_work_530_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_530_i1 j) (childrenD_530_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_51 3 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_530_i2.mono (by decide +kernel)

theorem finite_row_works_530_i1 : FiniteTemplate HasSnaky 5 required_530_i1 envelope_530_i1 := by
  refine finite_compose HasSnaky 4 childrenC_530_i1 childrenD_530_i1 finite_children_work_530_i1 (3, 2)
    required_530_i1 envelope_530_i1 pivot_mem_530_i1 child_required_sub_530_i1 child_envelope_sub_530_i1 ?_
  intro b hb
  exact common_sub_530_i1 (mem_commonEnvelope childrenD_530_i1 b hb)

theorem finite_children_work_530_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_530_i0 j) (childrenD_530_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 6 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_530_i1.mono (by decide +kernel)

theorem finite_row_works_530_i0 : FiniteTemplate HasSnaky 6 required_530_i0 envelope_530_i0 := by
  refine finite_compose HasSnaky 5 childrenC_530_i0 childrenD_530_i0 finite_children_work_530_i0 (2, 2)
    required_530_i0 envelope_530_i0 pivot_mem_530_i0 child_required_sub_530_i0 child_envelope_sub_530_i0 ?_
  intro b hb
  exact common_sub_530_i0 (mem_commonEnvelope childrenD_530_i0 b hb)

theorem finite_children_work_530 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_530 j) (childrenD_530 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_72 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_360 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_499 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_530_i0.mono (by decide +kernel)

theorem finite_row_works_530 : FiniteTemplate HasSnaky 8 required_530 envelope_530 := by
  refine finite_compose HasSnaky 7 childrenC_530 childrenD_530 finite_children_work_530 (2, 4)
    required_530 envelope_530 pivot_mem_530 child_required_sub_530 child_envelope_sub_530 ?_
  intro b hb
  exact common_sub_530 (mem_commonEnvelope childrenD_530 b hb)

theorem finite_children_work_532_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_532_i0 j) (childrenD_532_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_84 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 5 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_521 4 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_532_i0 : FiniteTemplate HasSnaky 7 required_532_i0 envelope_532_i0 := by
  refine finite_compose HasSnaky 6 childrenC_532_i0 childrenD_532_i0 finite_children_work_532_i0 (2, 6)
    required_532_i0 envelope_532_i0 pivot_mem_532_i0 child_required_sub_532_i0 child_envelope_sub_532_i0 ?_
  intro b hb
  exact common_sub_532_i0 (mem_commonEnvelope childrenD_532_i0 b hb)

theorem finite_children_work_532 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_532 j) (childrenD_532 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 3 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_532_i0.mono (by decide +kernel)

theorem finite_row_works_532 : FiniteTemplate HasSnaky 8 required_532 envelope_532 := by
  refine finite_compose HasSnaky 7 childrenC_532 childrenD_532 finite_children_work_532 (2, 3)
    required_532 envelope_532 pivot_mem_532 child_required_sub_532 child_envelope_sub_532 ?_
  intro b hb
  exact common_sub_532 (mem_commonEnvelope childrenD_532 b hb)

theorem finite_children_work_533_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_533_i0 j) (childrenD_533_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_392 7 (5, 4)).mono (by decide +kernel)

theorem finite_row_works_533_i0 : FiniteTemplate HasSnaky 7 required_533_i0 envelope_533_i0 := by
  refine finite_compose HasSnaky 6 childrenC_533_i0 childrenD_533_i0 finite_children_work_533_i0 (3, 4)
    required_533_i0 envelope_533_i0 pivot_mem_533_i0 child_required_sub_533_i0 child_envelope_sub_533_i0 ?_
  intro b hb
  exact common_sub_533_i0 (mem_commonEnvelope childrenD_533_i0 b hb)

theorem finite_children_work_533 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_533 j) (childrenD_533 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_279 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_533_i0.mono (by decide +kernel)

theorem finite_row_works_533 : FiniteTemplate HasSnaky 8 required_533 envelope_533 := by
  refine finite_compose HasSnaky 7 childrenC_533 childrenD_533 finite_children_work_533 (4, 3)
    required_533 envelope_533 pivot_mem_533 child_required_sub_533 child_envelope_sub_533 ?_
  intro b hb
  exact common_sub_533 (mem_commonEnvelope childrenD_533 b hb)

theorem finite_children_work_534_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_534_i1 j) (childrenD_534_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_177 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_534_i1 : FiniteTemplate HasSnaky 4 required_534_i1 envelope_534_i1 := by
  refine finite_compose HasSnaky 3 childrenC_534_i1 childrenD_534_i1 finite_children_work_534_i1 (2, 6)
    required_534_i1 envelope_534_i1 pivot_mem_534_i1 child_required_sub_534_i1 child_envelope_sub_534_i1 ?_
  intro b hb
  exact common_sub_534_i1 (mem_commonEnvelope childrenD_534_i1 b hb)

theorem finite_children_work_534_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_534_i2 j) (childrenD_534_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_239 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_534_i2 : FiniteTemplate HasSnaky 4 required_534_i2 envelope_534_i2 := by
  refine finite_compose HasSnaky 3 childrenC_534_i2 childrenD_534_i2 finite_children_work_534_i2 (3, 5)
    required_534_i2 envelope_534_i2 pivot_mem_534_i2 child_required_sub_534_i2 child_envelope_sub_534_i2 ?_
  intro b hb
  exact common_sub_534_i2 (mem_commonEnvelope childrenD_534_i2 b hb)

theorem finite_children_work_534_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_534_i0 j) (childrenD_534_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_139 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_534_i1.mono (by decide +kernel)
  · exact finite_row_works_534_i2.mono (by decide +kernel)

theorem finite_row_works_534_i0 : FiniteTemplate HasSnaky 5 required_534_i0 envelope_534_i0 := by
  refine finite_compose HasSnaky 4 childrenC_534_i0 childrenD_534_i0 finite_children_work_534_i0 (3, 6)
    required_534_i0 envelope_534_i0 pivot_mem_534_i0 child_required_sub_534_i0 child_envelope_sub_534_i0 ?_
  intro b hb
  exact common_sub_534_i0 (mem_commonEnvelope childrenD_534_i0 b hb)

theorem finite_children_work_534 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_534 j) (childrenD_534 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_388 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_534_i0.mono (by decide +kernel)

theorem finite_row_works_534 : FiniteTemplate HasSnaky 8 required_534 envelope_534 := by
  refine finite_compose HasSnaky 7 childrenC_534 childrenD_534 finite_children_work_534 (2, 5)
    required_534 envelope_534 pivot_mem_534 child_required_sub_534 child_envelope_sub_534 ?_
  intro b hb
  exact common_sub_534 (mem_commonEnvelope childrenD_534 b hb)

theorem finite_children_work_547_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_547_i0 j) (childrenD_547_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 2 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_547_i0 : FiniteTemplate HasSnaky 5 required_547_i0 envelope_547_i0 := by
  refine finite_compose HasSnaky 4 childrenC_547_i0 childrenD_547_i0 finite_children_work_547_i0 (1, 5)
    required_547_i0 envelope_547_i0 pivot_mem_547_i0 child_required_sub_547_i0 child_envelope_sub_547_i0 ?_
  intro b hb
  exact common_sub_547_i0 (mem_commonEnvelope childrenD_547_i0 b hb)

theorem finite_children_work_547_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_547_i1 j) (childrenD_547_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_525 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_547_i1 : FiniteTemplate HasSnaky 7 required_547_i1 envelope_547_i1 := by
  refine finite_compose HasSnaky 6 childrenC_547_i1 childrenD_547_i1 finite_children_work_547_i1 (2, 4)
    required_547_i1 envelope_547_i1 pivot_mem_547_i1 child_required_sub_547_i1 child_envelope_sub_547_i1 ?_
  intro b hb
  exact common_sub_547_i1 (mem_commonEnvelope childrenD_547_i1 b hb)

theorem finite_children_work_547 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_547 j) (childrenD_547 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_19.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 5 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_547_i0.mono (by decide +kernel)
  · exact finite_row_works_547_i1.mono (by decide +kernel)

theorem finite_row_works_547 : FiniteTemplate HasSnaky 8 required_547 envelope_547 := by
  refine finite_compose HasSnaky 7 childrenC_547 childrenD_547 finite_children_work_547 (1, 4)
    required_547 envelope_547 pivot_mem_547 child_required_sub_547 child_envelope_sub_547 ?_
  intro b hb
  exact common_sub_547 (mem_commonEnvelope childrenD_547 b hb)

theorem finite_children_work_558_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_558_i0 j) (childrenD_558_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_471.mono (by decide +kernel)

theorem finite_row_works_558_i0 : FiniteTemplate HasSnaky 7 required_558_i0 envelope_558_i0 := by
  refine finite_compose HasSnaky 6 childrenC_558_i0 childrenD_558_i0 finite_children_work_558_i0 (3, 1)
    required_558_i0 envelope_558_i0 pivot_mem_558_i0 child_required_sub_558_i0 child_envelope_sub_558_i0 ?_
  intro b hb
  exact common_sub_558_i0 (mem_commonEnvelope childrenD_558_i0 b hb)

theorem finite_children_work_558 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_558 j) (childrenD_558 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 4 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_558_i0.mono (by decide +kernel)

theorem finite_row_works_558 : FiniteTemplate HasSnaky 8 required_558 envelope_558 := by
  refine finite_compose HasSnaky 7 childrenC_558 childrenD_558 finite_children_work_558 (3, 2)
    required_558 envelope_558 pivot_mem_558 child_required_sub_558 child_envelope_sub_558 ?_
  intro b hb
  exact common_sub_558 (mem_commonEnvelope childrenD_558 b hb)

end FiniteCongruenceChecks.SnakyFinite
