/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part04
import FiniteCards.Height04Part05
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_439_i1 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_439_i1 j) (childrenD_439_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 3 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_439_i1 : FiniteTemplate HasSnaky 2 required_439_i1 envelope_439_i1 := by
  refine finite_compose HasSnaky 1 childrenC_439_i1 childrenD_439_i1 finite_children_work_439_i1 (4, 2)
    required_439_i1 envelope_439_i1 pivot_mem_439_i1 child_required_sub_439_i1 child_envelope_sub_439_i1 ?_
  intro b hb
  exact common_sub_439_i1 (mem_commonEnvelope childrenD_439_i1 b hb)

theorem finite_children_work_439_i4 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_439_i4 j) (childrenD_439_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 2 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_439_i4 : FiniteTemplate HasSnaky 2 required_439_i4 envelope_439_i4 := by
  refine finite_compose HasSnaky 1 childrenC_439_i4 childrenD_439_i4 finite_children_work_439_i4 (4, 1)
    required_439_i4 envelope_439_i4 pivot_mem_439_i4 child_required_sub_439_i4 child_envelope_sub_439_i4 ?_
  intro b hb
  exact common_sub_439_i4 (mem_commonEnvelope childrenD_439_i4 b hb)

theorem finite_children_work_439_i3 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_439_i3 j) (childrenD_439_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_439_i4.mono (by decide +kernel)

theorem finite_row_works_439_i3 : FiniteTemplate HasSnaky 3 required_439_i3 envelope_439_i3 := by
  refine finite_compose HasSnaky 2 childrenC_439_i3 childrenD_439_i3 finite_children_work_439_i3 (3, 1)
    required_439_i3 envelope_439_i3 pivot_mem_439_i3 child_required_sub_439_i3 child_envelope_sub_439_i3 ?_
  intro b hb
  exact common_sub_439_i3 (mem_commonEnvelope childrenD_439_i3 b hb)

theorem finite_children_work_439_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_439_i2 j) (childrenD_439_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_439_i3.mono (by decide +kernel)

theorem finite_row_works_439_i2 : FiniteTemplate HasSnaky 4 required_439_i2 envelope_439_i2 := by
  refine finite_compose HasSnaky 3 childrenC_439_i2 childrenD_439_i2 finite_children_work_439_i2 (2, 1)
    required_439_i2 envelope_439_i2 pivot_mem_439_i2 child_required_sub_439_i2 child_envelope_sub_439_i2 ?_
  intro b hb
  exact common_sub_439_i2 (mem_commonEnvelope childrenD_439_i2 b hb)

theorem finite_children_work_439_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_439_i0 j) (childrenD_439_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_251 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_432 7 (4, 5)).mono (by decide +kernel)
  · exact finite_row_works_439_i1.mono (by decide +kernel)
  · exact finite_row_works_439_i2.mono (by decide +kernel)

theorem finite_row_works_439_i0 : FiniteTemplate HasSnaky 5 required_439_i0 envelope_439_i0 := by
  refine finite_compose HasSnaky 4 childrenC_439_i0 childrenD_439_i0 finite_children_work_439_i0 (3, 2)
    required_439_i0 envelope_439_i0 pivot_mem_439_i0 child_required_sub_439_i0 child_envelope_sub_439_i0 ?_
  intro b hb
  exact common_sub_439_i0 (mem_commonEnvelope childrenD_439_i0 b hb)

theorem finite_children_work_439 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_439 j) (childrenD_439 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_439_i0.mono (by decide +kernel)

theorem finite_row_works_439 : FiniteTemplate HasSnaky 6 required_439 envelope_439 := by
  refine finite_compose HasSnaky 5 childrenC_439 childrenD_439 finite_children_work_439 (3, 3)
    required_439 envelope_439 pivot_mem_439 child_required_sub_439 child_envelope_sub_439 ?_
  intro b hb
  exact common_sub_439 (mem_commonEnvelope childrenD_439 b hb)

theorem finite_children_work_465_i3 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_465_i3 j) (childrenD_465_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_4 0 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_465_i3 : FiniteTemplate HasSnaky 2 required_465_i3 envelope_465_i3 := by
  refine finite_compose HasSnaky 1 childrenC_465_i3 childrenD_465_i3 finite_children_work_465_i3 (3, 4)
    required_465_i3 envelope_465_i3 pivot_mem_465_i3 child_required_sub_465_i3 child_envelope_sub_465_i3 ?_
  intro b hb
  exact common_sub_465_i3 (mem_commonEnvelope childrenD_465_i3 b hb)

theorem finite_children_work_465_i2 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_465_i2 j) (childrenD_465_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_465_i3.mono (by decide +kernel)

theorem finite_row_works_465_i2 : FiniteTemplate HasSnaky 3 required_465_i2 envelope_465_i2 := by
  refine finite_compose HasSnaky 2 childrenC_465_i2 childrenD_465_i2 finite_children_work_465_i2 (2, 4)
    required_465_i2 envelope_465_i2 pivot_mem_465_i2 child_required_sub_465_i2 child_envelope_sub_465_i2 ?_
  intro b hb
  exact common_sub_465_i2 (mem_commonEnvelope childrenD_465_i2 b hb)

theorem finite_children_work_465_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_465_i1 j) (childrenD_465_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_465_i2.mono (by decide +kernel)

theorem finite_row_works_465_i1 : FiniteTemplate HasSnaky 4 required_465_i1 envelope_465_i1 := by
  refine finite_compose HasSnaky 3 childrenC_465_i1 childrenD_465_i1 finite_children_work_465_i1 (0, 4)
    required_465_i1 envelope_465_i1 pivot_mem_465_i1 child_required_sub_465_i1 child_envelope_sub_465_i1 ?_
  intro b hb
  exact common_sub_465_i1 (mem_commonEnvelope childrenD_465_i1 b hb)

theorem finite_children_work_465_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_465_i0 j) (childrenD_465_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_42 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_465_i1.mono (by decide +kernel)

theorem finite_row_works_465_i0 : FiniteTemplate HasSnaky 5 required_465_i0 envelope_465_i0 := by
  refine finite_compose HasSnaky 4 childrenC_465_i0 childrenD_465_i0 finite_children_work_465_i0 (4, 5)
    required_465_i0 envelope_465_i0 pivot_mem_465_i0 child_required_sub_465_i0 child_envelope_sub_465_i0 ?_
  intro b hb
  exact common_sub_465_i0 (mem_commonEnvelope childrenD_465_i0 b hb)

theorem finite_children_work_465 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_465 j) (childrenD_465 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_465_i0.mono (by decide +kernel)

theorem finite_row_works_465 : FiniteTemplate HasSnaky 6 required_465 envelope_465 := by
  refine finite_compose HasSnaky 5 childrenC_465 childrenD_465 finite_children_work_465 (3, 2)
    required_465 envelope_465 pivot_mem_465 child_required_sub_465 child_envelope_sub_465 ?_
  intro b hb
  exact common_sub_465 (mem_commonEnvelope childrenD_465 b hb)

theorem finite_children_work_471_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_471_i0 j) (childrenD_471_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_354 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_471_i0 : FiniteTemplate HasSnaky 5 required_471_i0 envelope_471_i0 := by
  refine finite_compose HasSnaky 4 childrenC_471_i0 childrenD_471_i0 finite_children_work_471_i0 (3, 4)
    required_471_i0 envelope_471_i0 pivot_mem_471_i0 child_required_sub_471_i0 child_envelope_sub_471_i0 ?_
  intro b hb
  exact common_sub_471_i0 (mem_commonEnvelope childrenD_471_i0 b hb)

theorem finite_children_work_471 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_471 j) (childrenD_471 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_471_i0.mono (by decide +kernel)

theorem finite_row_works_471 : FiniteTemplate HasSnaky 6 required_471 envelope_471 := by
  refine finite_compose HasSnaky 5 childrenC_471 childrenD_471 finite_children_work_471 (3, 3)
    required_471 envelope_471 pivot_mem_471 child_required_sub_471 child_envelope_sub_471 ?_
  intro b hb
  exact common_sub_471 (mem_commonEnvelope childrenD_471 b hb)

theorem finite_children_work_486_i2 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_486_i2 j) (childrenD_486_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_156 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_486_i2 : FiniteTemplate HasSnaky 3 required_486_i2 envelope_486_i2 := by
  refine finite_compose HasSnaky 2 childrenC_486_i2 childrenD_486_i2 finite_children_work_486_i2 (1, 4)
    required_486_i2 envelope_486_i2 pivot_mem_486_i2 child_required_sub_486_i2 child_envelope_sub_486_i2 ?_
  intro b hb
  exact common_sub_486_i2 (mem_commonEnvelope childrenD_486_i2 b hb)

theorem finite_children_work_486_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_486_i1 j) (childrenD_486_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_486_i2.mono (by decide +kernel)

theorem finite_row_works_486_i1 : FiniteTemplate HasSnaky 4 required_486_i1 envelope_486_i1 := by
  refine finite_compose HasSnaky 3 childrenC_486_i1 childrenD_486_i1 finite_children_work_486_i1 (4, 2)
    required_486_i1 envelope_486_i1 pivot_mem_486_i1 child_required_sub_486_i1 child_envelope_sub_486_i1 ?_
  intro b hb
  exact common_sub_486_i1 (mem_commonEnvelope childrenD_486_i1 b hb)

theorem finite_children_work_486_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_486_i0 j) (childrenD_486_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_486_i1.mono (by decide +kernel)

theorem finite_row_works_486_i0 : FiniteTemplate HasSnaky 5 required_486_i0 envelope_486_i0 := by
  refine finite_compose HasSnaky 4 childrenC_486_i0 childrenD_486_i0 finite_children_work_486_i0 (1, 2)
    required_486_i0 envelope_486_i0 pivot_mem_486_i0 child_required_sub_486_i0 child_envelope_sub_486_i0 ?_
  intro b hb
  exact common_sub_486_i0 (mem_commonEnvelope childrenD_486_i0 b hb)

theorem finite_children_work_486 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_486 j) (childrenD_486 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_84 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_486_i0.mono (by decide +kernel)

theorem finite_row_works_486 : FiniteTemplate HasSnaky 6 required_486 envelope_486 := by
  refine finite_compose HasSnaky 5 childrenC_486 childrenD_486 finite_children_work_486 (4, 3)
    required_486 envelope_486 pivot_mem_486 child_required_sub_486 child_envelope_sub_486 ?_
  intro b hb
  exact common_sub_486 (mem_commonEnvelope childrenD_486 b hb)

theorem finite_children_work_493 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_493 j) (childrenD_493 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_87.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 5 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_492.mono (by decide +kernel)

theorem finite_row_works_493 : FiniteTemplate HasSnaky 6 required_493 envelope_493 := by
  refine finite_compose HasSnaky 5 childrenC_493 childrenD_493 finite_children_work_493 (3, 3)
    required_493 envelope_493 pivot_mem_493 child_required_sub_493 child_envelope_sub_493 ?_
  intro b hb
  exact common_sub_493 (mem_commonEnvelope childrenD_493 b hb)

theorem finite_children_work_498 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_498 j) (childrenD_498 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_114 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_496 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_498 : FiniteTemplate HasSnaky 6 required_498 envelope_498 := by
  refine finite_compose HasSnaky 5 childrenC_498 childrenD_498 finite_children_work_498 (4, 3)
    required_498 envelope_498 pivot_mem_498 child_required_sub_498 child_envelope_sub_498 ?_
  intro b hb
  exact common_sub_498 (mem_commonEnvelope childrenD_498 b hb)

theorem finite_children_work_503 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_503 j) (childrenD_503 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 4 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_502.mono (by decide +kernel)

theorem finite_row_works_503 : FiniteTemplate HasSnaky 6 required_503 envelope_503 := by
  refine finite_compose HasSnaky 5 childrenC_503 childrenD_503 finite_children_work_503 (2, 3)
    required_503 envelope_503 pivot_mem_503 child_required_sub_503 child_envelope_sub_503 ?_
  intro b hb
  exact common_sub_503 (mem_commonEnvelope childrenD_503 b hb)

theorem finite_children_work_516_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_516_i0 j) (childrenD_516_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_83 6 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_516_i0 : FiniteTemplate HasSnaky 3 required_516_i0 envelope_516_i0 := by
  refine finite_compose HasSnaky 2 childrenC_516_i0 childrenD_516_i0 finite_children_work_516_i0 (2, 3)
    required_516_i0 envelope_516_i0 pivot_mem_516_i0 child_required_sub_516_i0 child_envelope_sub_516_i0 ?_
  intro b hb
  exact common_sub_516_i0 (mem_commonEnvelope childrenD_516_i0 b hb)

theorem finite_children_work_516 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_516 j) (childrenD_516 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_516_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_515 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_516 : FiniteTemplate HasSnaky 6 required_516 envelope_516 := by
  refine finite_compose HasSnaky 5 childrenC_516 childrenD_516 finite_children_work_516 (4, 3)
    required_516 envelope_516 pivot_mem_516 child_required_sub_516 child_envelope_sub_516 ?_
  intro b hb
  exact common_sub_516 (mem_commonEnvelope childrenD_516 b hb)

end FiniteCongruenceChecks.SnakyFinite
