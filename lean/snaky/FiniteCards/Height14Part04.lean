/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part04
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part04
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part05
import FiniteCards.Height06Part06
import FiniteCards.Height07Part02
import FiniteCards.Height07Part05
import FiniteCards.Height07Part06
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height09Part02
import FiniteCards.Height10Part01
import FiniteCards.Height11Part03
import FiniteCards.Height13Part03
import FiniteCards.Height13Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_697_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_697_i4 j) (childrenD_697_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 7 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_374 0 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_697_i4 : FiniteTemplate HasSnaky 4 required_697_i4 envelope_697_i4 := by
  refine finite_compose HasSnaky 3 childrenC_697_i4 childrenD_697_i4 finite_children_work_697_i4 (5, 2)
    required_697_i4 envelope_697_i4 pivot_mem_697_i4 child_required_sub_697_i4 child_envelope_sub_697_i4 ?_
  intro b hb
  exact common_sub_697_i4 (mem_commonEnvelope childrenD_697_i4 b hb)

theorem finite_children_work_697_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_697_i3 j) (childrenD_697_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_95 7 (9, 7)).mono (by decide +kernel)
  · exact finite_row_works_697_i4.mono (by decide +kernel)

theorem finite_row_works_697_i3 : FiniteTemplate HasSnaky 7 required_697_i3 envelope_697_i3 := by
  refine finite_compose HasSnaky 6 childrenC_697_i3 childrenD_697_i3 finite_children_work_697_i3 (6, 6)
    required_697_i3 envelope_697_i3 pivot_mem_697_i3 child_required_sub_697_i3 child_envelope_sub_697_i3 ?_
  intro b hb
  exact common_sub_697_i3 (mem_commonEnvelope childrenD_697_i3 b hb)

theorem finite_children_work_697_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_697_i2 j) (childrenD_697_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_151 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_460 5 (8, 5)).mono (by decide +kernel)
  · exact finite_row_works_697_i3.mono (by decide +kernel)

theorem finite_row_works_697_i2 : FiniteTemplate HasSnaky 11 required_697_i2 envelope_697_i2 := by
  refine finite_compose HasSnaky 10 childrenC_697_i2 childrenD_697_i2 finite_children_work_697_i2 (5, 6)
    required_697_i2 envelope_697_i2 pivot_mem_697_i2 child_required_sub_697_i2 child_envelope_sub_697_i2 ?_
  intro b hb
  exact common_sub_697_i2 (mem_commonEnvelope childrenD_697_i2 b hb)

theorem finite_children_work_697_i1 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_697_i1 j) (childrenD_697_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_121 2 (5, 2)).mono (by decide +kernel)
  · exact finite_row_works_697_i2.mono (by decide +kernel)

theorem finite_row_works_697_i1 : FiniteTemplate HasSnaky 12 required_697_i1 envelope_697_i1 := by
  refine finite_compose HasSnaky 11 childrenC_697_i1 childrenD_697_i1 finite_children_work_697_i1 (3, 6)
    required_697_i1 envelope_697_i1 pivot_mem_697_i1 child_required_sub_697_i1 child_envelope_sub_697_i1 ?_
  intro b hb
  exact common_sub_697_i1 (mem_commonEnvelope childrenD_697_i1 b hb)

theorem finite_children_work_697_i0 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_697_i0 j) (childrenD_697_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 6 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_697_i1.mono (by decide +kernel)

theorem finite_row_works_697_i0 : FiniteTemplate HasSnaky 13 required_697_i0 envelope_697_i0 := by
  refine finite_compose HasSnaky 12 childrenC_697_i0 childrenD_697_i0 finite_children_work_697_i0 (3, 4)
    required_697_i0 envelope_697_i0 pivot_mem_697_i0 child_required_sub_697_i0 child_envelope_sub_697_i0 ?_
  intro b hb
  exact common_sub_697_i0 (mem_commonEnvelope childrenD_697_i0 b hb)

theorem finite_children_work_697 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_697 j) (childrenD_697 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 7 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_690.mono (by decide +kernel)
  · exact finite_row_works_697_i0.mono (by decide +kernel)

theorem finite_row_works_697 : FiniteTemplate HasSnaky 14 required_697 envelope_697 := by
  refine finite_compose HasSnaky 13 childrenC_697 childrenD_697 finite_children_work_697 (5, 3)
    required_697 envelope_697 pivot_mem_697 child_required_sub_697 child_envelope_sub_697 ?_
  intro b hb
  exact common_sub_697 (mem_commonEnvelope childrenD_697 b hb)

theorem finite_children_work_705_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_705_i1 j) (childrenD_705_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_181 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 4 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 1 (3, 3)).mono (by decide +kernel)

theorem finite_row_works_705_i1 : FiniteTemplate HasSnaky 10 required_705_i1 envelope_705_i1 := by
  refine finite_compose HasSnaky 9 childrenC_705_i1 childrenD_705_i1 finite_children_work_705_i1 (5, 6)
    required_705_i1 envelope_705_i1 pivot_mem_705_i1 child_required_sub_705_i1 child_envelope_sub_705_i1 ?_
  intro b hb
  exact common_sub_705_i1 (mem_commonEnvelope childrenD_705_i1 b hb)

theorem finite_children_work_705_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_705_i0 j) (childrenD_705_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_59 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_105 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_323 2 (6, 1)).mono (by decide +kernel)
  · exact finite_row_works_705_i1.mono (by decide +kernel)

theorem finite_row_works_705_i0 : FiniteTemplate HasSnaky 11 required_705_i0 envelope_705_i0 := by
  refine finite_compose HasSnaky 10 childrenC_705_i0 childrenD_705_i0 finite_children_work_705_i0 (5, 5)
    required_705_i0 envelope_705_i0 pivot_mem_705_i0 child_required_sub_705_i0 child_envelope_sub_705_i0 ?_
  intro b hb
  exact common_sub_705_i0 (mem_commonEnvelope childrenD_705_i0 b hb)

theorem finite_children_work_705_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_705_i4 j) (childrenD_705_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_242 2 (6, 2)).mono (by decide +kernel)

theorem finite_row_works_705_i4 : FiniteTemplate HasSnaky 5 required_705_i4 envelope_705_i4 := by
  refine finite_compose HasSnaky 4 childrenC_705_i4 childrenD_705_i4 finite_children_work_705_i4 (4, 4)
    required_705_i4 envelope_705_i4 pivot_mem_705_i4 child_required_sub_705_i4 child_envelope_sub_705_i4 ?_
  intro b hb
  exact common_sub_705_i4 (mem_commonEnvelope childrenD_705_i4 b hb)

theorem finite_children_work_705_i3 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_705_i3 j) (childrenD_705_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_79 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_243 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_518 2 (8, 1)).mono (by decide +kernel)
  · exact finite_row_works_705_i4.mono (by decide +kernel)

theorem finite_row_works_705_i3 : FiniteTemplate HasSnaky 9 required_705_i3 envelope_705_i3 := by
  refine finite_compose HasSnaky 8 childrenC_705_i3 childrenD_705_i3 finite_children_work_705_i3 (5, 6)
    required_705_i3 envelope_705_i3 pivot_mem_705_i3 child_required_sub_705_i3 child_envelope_sub_705_i3 ?_
  intro b hb
  exact common_sub_705_i3 (mem_commonEnvelope childrenD_705_i3 b hb)

theorem finite_children_work_705_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_705_i2 j) (childrenD_705_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_323 2 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_430 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_431 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_592 7 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_681 4 (1, 9)).mono (by decide +kernel)
  · exact finite_row_works_705_i3.mono (by decide +kernel)

theorem finite_row_works_705_i2 : FiniteTemplate HasSnaky 10 required_705_i2 envelope_705_i2 := by
  refine finite_compose HasSnaky 9 childrenC_705_i2 childrenD_705_i2 finite_children_work_705_i2 (5, 5)
    required_705_i2 envelope_705_i2 pivot_mem_705_i2 child_required_sub_705_i2 child_envelope_sub_705_i2 ?_
  intro b hb
  exact common_sub_705_i2 (mem_commonEnvelope childrenD_705_i2 b hb)

theorem finite_children_work_705 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_705 j) (childrenD_705 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_422 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_450 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_503 6 (6, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_642 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_680 4 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_705_i0.mono (by decide +kernel)
  · exact finite_row_works_705_i2.mono (by decide +kernel)

theorem finite_row_works_705 : FiniteTemplate HasSnaky 14 required_705 envelope_705 := by
  refine finite_compose HasSnaky 13 childrenC_705 childrenD_705 finite_children_work_705 (5, 4)
    required_705 envelope_705 pivot_mem_705 child_required_sub_705 child_envelope_sub_705 ?_
  intro b hb
  exact common_sub_705 (mem_commonEnvelope childrenD_705 b hb)

theorem finite_children_work_711_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_711_i0 j) (childrenD_711_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_104 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_359 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_452 4 (1, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_476 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_479 4 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_520 2 (9, 0)).mono (by decide +kernel)

theorem finite_row_works_711_i0 : FiniteTemplate HasSnaky 11 required_711_i0 envelope_711_i0 := by
  refine finite_compose HasSnaky 10 childrenC_711_i0 childrenD_711_i0 finite_children_work_711_i0 (6, 5)
    required_711_i0 envelope_711_i0 pivot_mem_711_i0 child_required_sub_711_i0 child_envelope_sub_711_i0 ?_
  intro b hb
  exact common_sub_711_i0 (mem_commonEnvelope childrenD_711_i0 b hb)

theorem finite_children_work_711 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_711 j) (childrenD_711 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_120 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_338 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_437 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_611 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_613 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_634 4 (1, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_642 4 (3, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_643 4 (3, 10)).mono (by decide +kernel)
  · exact finite_row_works_711_i0.mono (by decide +kernel)

theorem finite_row_works_711 : FiniteTemplate HasSnaky 14 required_711 envelope_711 := by
  refine finite_compose HasSnaky 13 childrenC_711 childrenD_711 finite_children_work_711 (6, 6)
    required_711 envelope_711 pivot_mem_711 child_required_sub_711 child_envelope_sub_711 ?_
  intro b hb
  exact common_sub_711 (mem_commonEnvelope childrenD_711 b hb)

end FiniteCongruenceChecks.SnakyFinite
