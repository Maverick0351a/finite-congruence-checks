/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height17Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part03
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part04
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part05
import FiniteCards.Height11Part01
import FiniteCards.Height12Part03
import FiniteCards.Height13Part03
import FiniteCards.Height16Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_623_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_623_i0 j) (childrenD_623_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_444 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_606 4 (4, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_610 4 (4, 9)).mono (by decide +kernel)

theorem finite_row_works_623_i0 : FiniteTemplate HasSnaky 11 required_623_i0 envelope_623_i0 := by
  refine finite_compose HasSnaky 10 childrenC_623_i0 childrenD_623_i0 finite_children_work_623_i0 (5, 5)
    required_623_i0 envelope_623_i0 pivot_mem_623_i0 child_required_sub_623_i0 child_envelope_sub_623_i0 ?_
  intro b hb
  exact common_sub_623_i0 (mem_commonEnvelope childrenD_623_i0 b hb)

theorem finite_children_work_623_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_623_i1 j) (childrenD_623_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_137 7 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 7 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_363 6 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 7 (7, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_606 4 (4, 9)).mono (by decide +kernel)

theorem finite_row_works_623_i1 : FiniteTemplate HasSnaky 10 required_623_i1 envelope_623_i1 := by
  refine finite_compose HasSnaky 9 childrenC_623_i1 childrenD_623_i1 finite_children_work_623_i1 (5, 5)
    required_623_i1 envelope_623_i1 pivot_mem_623_i1 child_required_sub_623_i1 child_envelope_sub_623_i1 ?_
  intro b hb
  exact common_sub_623_i1 (mem_commonEnvelope childrenD_623_i1 b hb)

theorem finite_children_work_623_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_623_i4 j) (childrenD_623_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 2 (5, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_35 3 (4, 9)).mono (by decide +kernel)

theorem finite_row_works_623_i4 : FiniteTemplate HasSnaky 5 required_623_i4 envelope_623_i4 := by
  refine finite_compose HasSnaky 4 childrenC_623_i4 childrenD_623_i4 finite_children_work_623_i4 (4, 7)
    required_623_i4 envelope_623_i4 pivot_mem_623_i4 child_required_sub_623_i4 child_envelope_sub_623_i4 ?_
  intro b hb
  exact common_sub_623_i4 (mem_commonEnvelope childrenD_623_i4 b hb)

theorem finite_children_work_623_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_623_i3 j) (childrenD_623_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 4 (4, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_151 2 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 2 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 2 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_623_i4.mono (by decide +kernel)

theorem finite_row_works_623_i3 : FiniteTemplate HasSnaky 6 required_623_i3 envelope_623_i3 := by
  refine finite_compose HasSnaky 5 childrenC_623_i3 childrenD_623_i3 finite_children_work_623_i3 (5, 9)
    required_623_i3 envelope_623_i3 pivot_mem_623_i3 child_required_sub_623_i3 child_envelope_sub_623_i3 ?_
  intro b hb
  exact common_sub_623_i3 (mem_commonEnvelope childrenD_623_i3 b hb)

theorem finite_children_work_623_i5 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_623_i5 j) (childrenD_623_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_179 3 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_371 3 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_443 4 (4, 9)).mono (by decide +kernel)

theorem finite_row_works_623_i5 : FiniteTemplate HasSnaky 10 required_623_i5 envelope_623_i5 := by
  refine finite_compose HasSnaky 9 childrenC_623_i5 childrenD_623_i5 finite_children_work_623_i5 (5, 5)
    required_623_i5 envelope_623_i5 pivot_mem_623_i5 child_required_sub_623_i5 child_envelope_sub_623_i5 ?_
  intro b hb
  exact common_sub_623_i5 (mem_commonEnvelope childrenD_623_i5 b hb)

theorem finite_children_work_623_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_623_i2 j) (childrenD_623_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 2 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_211 2 (8, 4)).mono (by decide +kernel)
  · exact finite_row_works_623_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_619 1 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_623_i5.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_620 2 (8, 2)).mono (by decide +kernel)

theorem finite_row_works_623_i2 : FiniteTemplate HasSnaky 11 required_623_i2 envelope_623_i2 := by
  refine finite_compose HasSnaky 10 childrenC_623_i2 childrenD_623_i2 finite_children_work_623_i2 (5, 8)
    required_623_i2 envelope_623_i2 pivot_mem_623_i2 child_required_sub_623_i2 child_envelope_sub_623_i2 ?_
  intro b hb
  exact common_sub_623_i2 (mem_commonEnvelope childrenD_623_i2 b hb)

theorem finite_children_work_623_i7 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_623_i7 j) (childrenD_623_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_179 3 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 3 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_465 0 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_623_i7 : FiniteTemplate HasSnaky 7 required_623_i7 envelope_623_i7 := by
  refine finite_compose HasSnaky 6 childrenC_623_i7 childrenD_623_i7 finite_children_work_623_i7 (5, 5)
    required_623_i7 envelope_623_i7 pivot_mem_623_i7 child_required_sub_623_i7 child_envelope_sub_623_i7 ?_
  intro b hb
  exact common_sub_623_i7 (mem_commonEnvelope childrenD_623_i7 b hb)

theorem finite_children_work_623_i6 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_623_i6 j) (childrenD_623_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 1 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 4 (4, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 1 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_623_i7.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_622 6 (8, 11)).mono (by decide +kernel)

theorem finite_row_works_623_i6 : FiniteTemplate HasSnaky 10 required_623_i6 envelope_623_i6 := by
  refine finite_compose HasSnaky 9 childrenC_623_i6 childrenD_623_i6 finite_children_work_623_i6 (5, 8)
    required_623_i6 envelope_623_i6 pivot_mem_623_i6 child_required_sub_623_i6 child_envelope_sub_623_i6 ?_
  intro b hb
  exact common_sub_623_i6 (mem_commonEnvelope childrenD_623_i6 b hb)

theorem finite_children_work_623 : ∀ j, FiniteTemplate HasSnaky 16 (childrenC_623 j) (childrenD_623 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_467 6 (9, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_602 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_603 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_607 6 (9, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_608 6 (9, 11)).mono (by decide +kernel)
  · exact finite_row_works_623_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_618 6 (10, 10)).mono (by decide +kernel)
  · exact finite_row_works_623_i1.mono (by decide +kernel)
  · exact finite_row_works_623_i2.mono (by decide +kernel)
  · exact finite_row_works_623_i6.mono (by decide +kernel)

theorem finite_row_works_623 : FiniteTemplate HasSnaky 17 required_623 envelope_623 := by
  refine finite_compose HasSnaky 16 childrenC_623 childrenD_623 finite_children_work_623 (5, 6)
    required_623 envelope_623 pivot_mem_623 child_required_sub_623 child_envelope_sub_623 ?_
  intro b hb
  exact common_sub_623 (mem_commonEnvelope childrenD_623 b hb)

theorem finite_children_work_630_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_630_i0 j) (childrenD_630_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_13 6 (5, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_355 6 (7, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_356 6 (7, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_434 2 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_441 4 (3, 10)).mono (by decide +kernel)

theorem finite_row_works_630_i0 : FiniteTemplate HasSnaky 10 required_630_i0 envelope_630_i0 := by
  refine finite_compose HasSnaky 9 childrenC_630_i0 childrenD_630_i0 finite_children_work_630_i0 (4, 8)
    required_630_i0 envelope_630_i0 pivot_mem_630_i0 child_required_sub_630_i0 child_envelope_sub_630_i0 ?_
  intro b hb
  exact common_sub_630_i0 (mem_commonEnvelope childrenD_630_i0 b hb)

theorem finite_children_work_630_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_630_i1 j) (childrenD_630_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_112 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_363 6 (7, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_364 6 (7, 9)).mono (by decide +kernel)

theorem finite_row_works_630_i1 : FiniteTemplate HasSnaky 7 required_630_i1 envelope_630_i1 := by
  refine finite_compose HasSnaky 6 childrenC_630_i1 childrenD_630_i1 finite_children_work_630_i1 (4, 5)
    required_630_i1 envelope_630_i1 pivot_mem_630_i1 child_required_sub_630_i1 child_envelope_sub_630_i1 ?_
  intro b hb
  exact common_sub_630_i1 (mem_commonEnvelope childrenD_630_i1 b hb)

theorem finite_children_work_630_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_630_i2 j) (childrenD_630_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_112 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 5 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_295 6 (8, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_466 0 (3, 4)).mono (by decide +kernel)

theorem finite_row_works_630_i2 : FiniteTemplate HasSnaky 8 required_630_i2 envelope_630_i2 := by
  refine finite_compose HasSnaky 7 childrenC_630_i2 childrenD_630_i2 finite_children_work_630_i2 (4, 5)
    required_630_i2 envelope_630_i2 pivot_mem_630_i2 child_required_sub_630_i2 child_envelope_sub_630_i2 ?_
  intro b hb
  exact common_sub_630_i2 (mem_commonEnvelope childrenD_630_i2 b hb)

theorem finite_children_work_630_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_630_i4 j) (childrenD_630_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 6 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_34 3 (3, 7)).mono (by decide +kernel)

theorem finite_row_works_630_i4 : FiniteTemplate HasSnaky 5 required_630_i4 envelope_630_i4 := by
  refine finite_compose HasSnaky 4 childrenC_630_i4 childrenD_630_i4 finite_children_work_630_i4 (5, 7)
    required_630_i4 envelope_630_i4 pivot_mem_630_i4 child_required_sub_630_i4 child_envelope_sub_630_i4 ?_
  intro b hb
  exact common_sub_630_i4 (mem_commonEnvelope childrenD_630_i4 b hb)

theorem finite_children_work_630_i3 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_630_i3 j) (childrenD_630_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_112 0 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_257 3 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_398 7 (7, 7)).mono (by decide +kernel)
  · exact finite_row_works_630_i4.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_628 0 (3, 3)).mono (by decide +kernel)

theorem finite_row_works_630_i3 : FiniteTemplate HasSnaky 10 required_630_i3 envelope_630_i3 := by
  refine finite_compose HasSnaky 9 childrenC_630_i3 childrenD_630_i3 finite_children_work_630_i3 (4, 5)
    required_630_i3 envelope_630_i3 pivot_mem_630_i3 child_required_sub_630_i3 child_envelope_sub_630_i3 ?_
  intro b hb
  exact common_sub_630_i3 (mem_commonEnvelope childrenD_630_i3 b hb)

theorem finite_children_work_630 : ∀ j, FiniteTemplate HasSnaky 16 (childrenC_630 j) (childrenD_630 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_368 2 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_368 6 (8, 10)).mono (by decide +kernel)
  · exact finite_row_works_630_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_467 6 (8, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_627 0 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_630_i1.mono (by decide +kernel)
  · exact finite_row_works_630_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_629 4 (1, 10)).mono (by decide +kernel)
  · exact finite_row_works_630_i3.mono (by decide +kernel)

theorem finite_row_works_630 : FiniteTemplate HasSnaky 17 required_630 envelope_630 := by
  refine finite_compose HasSnaky 16 childrenC_630 childrenD_630 finite_children_work_630 (4, 6)
    required_630 envelope_630 pivot_mem_630 child_required_sub_630 child_envelope_sub_630 ?_
  intro b hb
  exact common_sub_630 (mem_commonEnvelope childrenD_630 b hb)

end FiniteCongruenceChecks.SnakyFinite
