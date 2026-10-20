/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height05Part01
import FiniteCards.Height06Part01
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part04
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part05
import FiniteCards.Height10Part01
import FiniteCards.Height10Part04
import FiniteCards.Height10Part05
import FiniteCards.Height11Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_599_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_599_i6 j) (childrenD_599_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_64 0 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_599_i6 : FiniteTemplate HasSnaky 4 required_599_i6 envelope_599_i6 := by
  refine finite_compose HasSnaky 3 childrenC_599_i6 childrenD_599_i6 finite_children_work_599_i6 (5, 6)
    required_599_i6 envelope_599_i6 pivot_mem_599_i6 child_required_sub_599_i6 child_envelope_sub_599_i6 ?_
  intro b hb
  exact common_sub_599_i6 (mem_commonEnvelope childrenD_599_i6 b hb)

theorem finite_children_work_599_i8 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_599_i8 j) (childrenD_599_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 0 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_599_i8 : FiniteTemplate HasSnaky 4 required_599_i8 envelope_599_i8 := by
  refine finite_compose HasSnaky 3 childrenC_599_i8 childrenD_599_i8 finite_children_work_599_i8 (4, 4)
    required_599_i8 envelope_599_i8 pivot_mem_599_i8 child_required_sub_599_i8 child_envelope_sub_599_i8 ?_
  intro b hb
  exact common_sub_599_i8 (mem_commonEnvelope childrenD_599_i8 b hb)

theorem finite_children_work_599_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_599_i7 j) (childrenD_599_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 3 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_599_i8.mono (by decide +kernel)

theorem finite_row_works_599_i7 : FiniteTemplate HasSnaky 5 required_599_i7 envelope_599_i7 := by
  refine finite_compose HasSnaky 4 childrenC_599_i7 childrenD_599_i7 finite_children_work_599_i7 (6, 5)
    required_599_i7 envelope_599_i7 pivot_mem_599_i7 child_required_sub_599_i7 child_envelope_sub_599_i7 ?_
  intro b hb
  exact common_sub_599_i7 (mem_commonEnvelope childrenD_599_i7 b hb)

theorem finite_children_work_599_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_599_i5 j) (childrenD_599_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 0 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 1 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_599_i6.mono (by decide +kernel)
  · exact finite_row_works_599_i7.mono (by decide +kernel)

theorem finite_row_works_599_i5 : FiniteTemplate HasSnaky 6 required_599_i5 envelope_599_i5 := by
  refine finite_compose HasSnaky 5 childrenC_599_i5 childrenD_599_i5 finite_children_work_599_i5 (5, 5)
    required_599_i5 envelope_599_i5 pivot_mem_599_i5 child_required_sub_599_i5 child_envelope_sub_599_i5 ?_
  intro b hb
  exact common_sub_599_i5 (mem_commonEnvelope childrenD_599_i5 b hb)

theorem finite_children_work_599_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_599_i4 j) (childrenD_599_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_599_i5.mono (by decide +kernel)

theorem finite_row_works_599_i4 : FiniteTemplate HasSnaky 7 required_599_i4 envelope_599_i4 := by
  refine finite_compose HasSnaky 6 childrenC_599_i4 childrenD_599_i4 finite_children_work_599_i4 (2, 5)
    required_599_i4 envelope_599_i4 pivot_mem_599_i4 child_required_sub_599_i4 child_envelope_sub_599_i4 ?_
  intro b hb
  exact common_sub_599_i4 (mem_commonEnvelope childrenD_599_i4 b hb)

theorem finite_children_work_599_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_599_i3 j) (childrenD_599_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_599_i4.mono (by decide +kernel)

theorem finite_row_works_599_i3 : FiniteTemplate HasSnaky 8 required_599_i3 envelope_599_i3 := by
  refine finite_compose HasSnaky 7 childrenC_599_i3 childrenD_599_i3 finite_children_work_599_i3 (4, 5)
    required_599_i3 envelope_599_i3 pivot_mem_599_i3 child_required_sub_599_i3 child_envelope_sub_599_i3 ?_
  intro b hb
  exact common_sub_599_i3 (mem_commonEnvelope childrenD_599_i3 b hb)

theorem finite_children_work_599_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_599_i2 j) (childrenD_599_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_251 7 (4, 5)).mono (by decide +kernel)
  · exact finite_row_works_599_i3.mono (by decide +kernel)

theorem finite_row_works_599_i2 : FiniteTemplate HasSnaky 9 required_599_i2 envelope_599_i2 := by
  refine finite_compose HasSnaky 8 childrenC_599_i2 childrenD_599_i2 finite_children_work_599_i2 (3, 2)
    required_599_i2 envelope_599_i2 pivot_mem_599_i2 child_required_sub_599_i2 child_envelope_sub_599_i2 ?_
  intro b hb
  exact common_sub_599_i2 (mem_commonEnvelope childrenD_599_i2 b hb)

theorem finite_children_work_599_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_599_i1 j) (childrenD_599_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_27 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_48 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_599_i2.mono (by decide +kernel)

theorem finite_row_works_599_i1 : FiniteTemplate HasSnaky 10 required_599_i1 envelope_599_i1 := by
  refine finite_compose HasSnaky 9 childrenC_599_i1 childrenD_599_i1 finite_children_work_599_i1 (3, 5)
    required_599_i1 envelope_599_i1 pivot_mem_599_i1 child_required_sub_599_i1 child_envelope_sub_599_i1 ?_
  intro b hb
  exact common_sub_599_i1 (mem_commonEnvelope childrenD_599_i1 b hb)

theorem finite_children_work_599_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_599_i0 j) (childrenD_599_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_599_i1.mono (by decide +kernel)

theorem finite_row_works_599_i0 : FiniteTemplate HasSnaky 11 required_599_i0 envelope_599_i0 := by
  refine finite_compose HasSnaky 10 childrenC_599_i0 childrenD_599_i0 finite_children_work_599_i0 (3, 4)
    required_599_i0 envelope_599_i0 pivot_mem_599_i0 child_required_sub_599_i0 child_envelope_sub_599_i0 ?_
  intro b hb
  exact common_sub_599_i0 (mem_commonEnvelope childrenD_599_i0 b hb)

theorem finite_children_work_599 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_599 j) (childrenD_599 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_107 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_163 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_401 4 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_599_i0.mono (by decide +kernel)

theorem finite_row_works_599 : FiniteTemplate HasSnaky 12 required_599 envelope_599 := by
  refine finite_compose HasSnaky 11 childrenC_599 childrenD_599 finite_children_work_599 (4, 3)
    required_599 envelope_599 pivot_mem_599 child_required_sub_599 child_envelope_sub_599 ?_
  intro b hb
  exact common_sub_599 (mem_commonEnvelope childrenD_599 b hb)

theorem finite_children_work_605_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_605_i0 j) (childrenD_605_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_115 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_585 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_604 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_605_i0 : FiniteTemplate HasSnaky 11 required_605_i0 envelope_605_i0 := by
  refine finite_compose HasSnaky 10 childrenC_605_i0 childrenD_605_i0 finite_children_work_605_i0 (1, 3)
    required_605_i0 envelope_605_i0 pivot_mem_605_i0 child_required_sub_605_i0 child_envelope_sub_605_i0 ?_
  intro b hb
  exact common_sub_605_i0 (mem_commonEnvelope childrenD_605_i0 b hb)

theorem finite_children_work_605 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_605 j) (childrenD_605 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_182 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_605_i0.mono (by decide +kernel)

theorem finite_row_works_605 : FiniteTemplate HasSnaky 12 required_605 envelope_605 := by
  refine finite_compose HasSnaky 11 childrenC_605 childrenD_605 finite_children_work_605 (4, 3)
    required_605 envelope_605 pivot_mem_605 child_required_sub_605 child_envelope_sub_605 ?_
  intro b hb
  exact common_sub_605 (mem_commonEnvelope childrenD_605 b hb)

theorem finite_children_work_618_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_618_i2 j) (childrenD_618_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 6 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_378 1 (3, 3)).mono (by decide +kernel)

theorem finite_row_works_618_i2 : FiniteTemplate HasSnaky 7 required_618_i2 envelope_618_i2 := by
  refine finite_compose HasSnaky 6 childrenC_618_i2 childrenD_618_i2 finite_children_work_618_i2 (3, 5)
    required_618_i2 envelope_618_i2 pivot_mem_618_i2 child_required_sub_618_i2 child_envelope_sub_618_i2 ?_
  intro b hb
  exact common_sub_618_i2 (mem_commonEnvelope childrenD_618_i2 b hb)

theorem finite_children_work_618_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_618_i1 j) (childrenD_618_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 7 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_618_i2.mono (by decide +kernel)

theorem finite_row_works_618_i1 : FiniteTemplate HasSnaky 8 required_618_i1 envelope_618_i1 := by
  refine finite_compose HasSnaky 7 childrenC_618_i1 childrenD_618_i1 finite_children_work_618_i1 (3, 4)
    required_618_i1 envelope_618_i1 pivot_mem_618_i1 child_required_sub_618_i1 child_envelope_sub_618_i1 ?_
  intro b hb
  exact common_sub_618_i1 (mem_commonEnvelope childrenD_618_i1 b hb)

theorem finite_children_work_618_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_618_i0 j) (childrenD_618_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact finite_row_works_618_i1.mono (by decide +kernel)

theorem finite_row_works_618_i0 : FiniteTemplate HasSnaky 9 required_618_i0 envelope_618_i0 := by
  refine finite_compose HasSnaky 8 childrenC_618_i0 childrenD_618_i0 finite_children_work_618_i0 (5, 6)
    required_618_i0 envelope_618_i0 pivot_mem_618_i0 child_required_sub_618_i0 child_envelope_sub_618_i0 ?_
  intro b hb
  exact common_sub_618_i0 (mem_commonEnvelope childrenD_618_i0 b hb)

theorem finite_children_work_618_i3 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_618_i3 j) (childrenD_618_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_604 1 (2, 3)).mono (by decide +kernel)

theorem finite_row_works_618_i3 : FiniteTemplate HasSnaky 9 required_618_i3 envelope_618_i3 := by
  refine finite_compose HasSnaky 8 childrenC_618_i3 childrenD_618_i3 finite_children_work_618_i3 (5, 6)
    required_618_i3 envelope_618_i3 pivot_mem_618_i3 child_required_sub_618_i3 child_envelope_sub_618_i3 ?_
  intro b hb
  exact common_sub_618_i3 (mem_commonEnvelope childrenD_618_i3 b hb)

theorem finite_children_work_618_i4 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_618_i4 j) (childrenD_618_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_171 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_577 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_609 6 (6, 7)).mono (by decide +kernel)

theorem finite_row_works_618_i4 : FiniteTemplate HasSnaky 10 required_618_i4 envelope_618_i4 := by
  refine finite_compose HasSnaky 9 childrenC_618_i4 childrenD_618_i4 finite_children_work_618_i4 (5, 6)
    required_618_i4 envelope_618_i4 pivot_mem_618_i4 child_required_sub_618_i4 child_envelope_sub_618_i4 ?_
  intro b hb
  exact common_sub_618_i4 (mem_commonEnvelope childrenD_618_i4 b hb)

theorem finite_children_work_618_i5 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_618_i5 j) (childrenD_618_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_256 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_577 3 (3, 7)).mono (by decide +kernel)

theorem finite_row_works_618_i5 : FiniteTemplate HasSnaky 10 required_618_i5 envelope_618_i5 := by
  refine finite_compose HasSnaky 9 childrenC_618_i5 childrenD_618_i5 finite_children_work_618_i5 (5, 6)
    required_618_i5 envelope_618_i5 pivot_mem_618_i5 child_required_sub_618_i5 child_envelope_sub_618_i5 ?_
  intro b hb
  exact common_sub_618_i5 (mem_commonEnvelope childrenD_618_i5 b hb)

theorem finite_children_work_618_i8 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_618_i8 j) (childrenD_618_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 6 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_113 1 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_618_i8 : FiniteTemplate HasSnaky 4 required_618_i8 envelope_618_i8 := by
  refine finite_compose HasSnaky 3 childrenC_618_i8 childrenD_618_i8 finite_children_work_618_i8 (6, 4)
    required_618_i8 envelope_618_i8 pivot_mem_618_i8 child_required_sub_618_i8 child_envelope_sub_618_i8 ?_
  intro b hb
  exact common_sub_618_i8 (mem_commonEnvelope childrenD_618_i8 b hb)

theorem finite_children_work_618_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_618_i7 j) (childrenD_618_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_618_i8.mono (by decide +kernel)

theorem finite_row_works_618_i7 : FiniteTemplate HasSnaky 5 required_618_i7 envelope_618_i7 := by
  refine finite_compose HasSnaky 4 childrenC_618_i7 childrenD_618_i7 finite_children_work_618_i7 (3, 4)
    required_618_i7 envelope_618_i7 pivot_mem_618_i7 child_required_sub_618_i7 child_envelope_sub_618_i7 ?_
  intro b hb
  exact common_sub_618_i7 (mem_commonEnvelope childrenD_618_i7 b hb)

theorem finite_children_work_618_i6 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_618_i6 j) (childrenD_618_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_80 5 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_111 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_616 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_618_i7.mono (by decide +kernel)

theorem finite_row_works_618_i6 : FiniteTemplate HasSnaky 11 required_618_i6 envelope_618_i6 := by
  refine finite_compose HasSnaky 10 childrenC_618_i6 childrenD_618_i6 finite_children_work_618_i6 (4, 4)
    required_618_i6 envelope_618_i6 pivot_mem_618_i6 child_required_sub_618_i6 child_envelope_sub_618_i6 ?_
  intro b hb
  exact common_sub_618_i6 (mem_commonEnvelope childrenD_618_i6 b hb)

theorem finite_children_work_618 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_618 j) (childrenD_618 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_398 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_434 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_610 2 (6, 1)).mono (by decide +kernel)
  · exact finite_row_works_618_i0.mono (by decide +kernel)
  · exact finite_row_works_618_i3.mono (by decide +kernel)
  · exact finite_row_works_618_i4.mono (by decide +kernel)
  · exact finite_row_works_618_i5.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_615 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_618_i6.mono (by decide +kernel)

theorem finite_row_works_618 : FiniteTemplate HasSnaky 12 required_618 envelope_618 := by
  refine finite_compose HasSnaky 11 childrenC_618 childrenD_618 finite_children_work_618 (5, 5)
    required_618 envelope_618 pivot_mem_618 child_required_sub_618 child_envelope_sub_618 ?_
  intro b hb
  exact common_sub_618 (mem_commonEnvelope childrenD_618 b hb)

end FiniteCongruenceChecks.SnakyFinite
