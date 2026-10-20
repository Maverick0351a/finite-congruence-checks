/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height15Part03
import FiniteCards.Height01Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part04
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part04
import FiniteCards.Height08Part05
import FiniteCards.Height09Part04
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height10Part03
import FiniteCards.Height11Part06
import FiniteCards.Height12Part02
import FiniteCards.Height12Part03
import FiniteCards.Height12Part04
import FiniteCards.Height13Part01
import FiniteCards.Height13Part03
import FiniteCards.Height13Part04
import FiniteCards.Height13Part05
import FiniteCards.Height14Part03
import FiniteCards.Height14Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_698 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_698 j) (childrenD_698 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_182 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_619 5 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_620 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_622 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_687 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_697 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_698 : FiniteTemplate HasSnaky 15 required_698 envelope_698 := by
  refine finite_compose HasSnaky 14 childrenC_698 childrenD_698 finite_children_work_698 (4, 6)
    required_698 envelope_698 pivot_mem_698 child_required_sub_698 child_envelope_sub_698 ?_
  intro b hb
  exact common_sub_698 (mem_commonEnvelope childrenD_698 b hb)

theorem finite_children_work_699_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_699_i3 j) (childrenD_699_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_42 0 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 1 (4, 5)).mono (by decide +kernel)

theorem finite_row_works_699_i3 : FiniteTemplate HasSnaky 5 required_699_i3 envelope_699_i3 := by
  refine finite_compose HasSnaky 4 childrenC_699_i3 childrenD_699_i3 finite_children_work_699_i3 (7, 6)
    required_699_i3 envelope_699_i3 pivot_mem_699_i3 child_required_sub_699_i3 child_envelope_sub_699_i3 ?_
  intro b hb
  exact common_sub_699_i3 (mem_commonEnvelope childrenD_699_i3 b hb)

theorem finite_children_work_699_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_699_i2 j) (childrenD_699_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_95 7 (10, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_112 1 (4, 4)).mono (by decide +kernel)
  · exact finite_row_works_699_i3.mono (by decide +kernel)

theorem finite_row_works_699_i2 : FiniteTemplate HasSnaky 7 required_699_i2 envelope_699_i2 := by
  refine finite_compose HasSnaky 6 childrenC_699_i2 childrenD_699_i2 finite_children_work_699_i2 (7, 8)
    required_699_i2 envelope_699_i2 pivot_mem_699_i2 child_required_sub_699_i2 child_envelope_sub_699_i2 ?_
  intro b hb
  exact common_sub_699_i2 (mem_commonEnvelope childrenD_699_i2 b hb)

theorem finite_children_work_699_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_699_i1 j) (childrenD_699_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_371 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_460 5 (9, 7)).mono (by decide +kernel)
  · exact finite_row_works_699_i2.mono (by decide +kernel)

theorem finite_row_works_699_i1 : FiniteTemplate HasSnaky 11 required_699_i1 envelope_699_i1 := by
  refine finite_compose HasSnaky 10 childrenC_699_i1 childrenD_699_i1 finite_children_work_699_i1 (6, 8)
    required_699_i1 envelope_699_i1 pivot_mem_699_i1 child_required_sub_699_i1 child_envelope_sub_699_i1 ?_
  intro b hb
  exact common_sub_699_i1 (mem_commonEnvelope childrenD_699_i1 b hb)

theorem finite_children_work_699_i0 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_699_i0 j) (childrenD_699_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_147 2 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_249 3 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_692 5 (9, 5)).mono (by decide +kernel)
  · exact finite_row_works_699_i1.mono (by decide +kernel)

theorem finite_row_works_699_i0 : FiniteTemplate HasSnaky 14 required_699_i0 envelope_699_i0 := by
  refine finite_compose HasSnaky 13 childrenC_699_i0 childrenD_699_i0 finite_children_work_699_i0 (4, 8)
    required_699_i0 envelope_699_i0 pivot_mem_699_i0 child_required_sub_699_i0 child_envelope_sub_699_i0 ?_
  intro b hb
  exact common_sub_699_i0 (mem_commonEnvelope childrenD_699_i0 b hb)

theorem finite_children_work_699_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_699_i6 j) (childrenD_699_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_259 4 (5, 7)).mono (by decide +kernel)

theorem finite_row_works_699_i6 : FiniteTemplate HasSnaky 5 required_699_i6 envelope_699_i6 := by
  refine finite_compose HasSnaky 4 childrenC_699_i6 childrenD_699_i6 finite_children_work_699_i6 (7, 4)
    required_699_i6 envelope_699_i6 pivot_mem_699_i6 child_required_sub_699_i6 child_envelope_sub_699_i6 ?_
  intro b hb
  exact common_sub_699_i6 (mem_commonEnvelope childrenD_699_i6 b hb)

theorem finite_children_work_699_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_699_i5 j) (childrenD_699_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 6 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_48 6 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 3 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_699_i6.mono (by decide +kernel)

theorem finite_row_works_699_i5 : FiniteTemplate HasSnaky 7 required_699_i5 envelope_699_i5 := by
  refine finite_compose HasSnaky 6 childrenC_699_i5 childrenD_699_i5 finite_children_work_699_i5 (6, 3)
    required_699_i5 envelope_699_i5 pivot_mem_699_i5 child_required_sub_699_i5 child_envelope_sub_699_i5 ?_
  intro b hb
  exact common_sub_699_i5 (mem_commonEnvelope childrenD_699_i5 b hb)

theorem finite_children_work_699_i4 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_699_i4 j) (childrenD_699_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_389 3 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 0 (5, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_546 4 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_549 0 (5, 0)).mono (by decide +kernel)
  · exact finite_row_works_699_i5.mono (by decide +kernel)

theorem finite_row_works_699_i4 : FiniteTemplate HasSnaky 11 required_699_i4 envelope_699_i4 := by
  refine finite_compose HasSnaky 10 childrenC_699_i4 childrenD_699_i4 finite_children_work_699_i4 (6, 4)
    required_699_i4 envelope_699_i4 pivot_mem_699_i4 child_required_sub_699_i4 child_envelope_sub_699_i4 ?_
  intro b hb
  exact common_sub_699_i4 (mem_commonEnvelope childrenD_699_i4 b hb)

theorem finite_children_work_699 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_699 j) (childrenD_699 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_197 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_693 2 (11, 0)).mono (by decide +kernel)
  · exact finite_row_works_699_i0.mono (by decide +kernel)
  · exact finite_row_works_699_i4.mono (by decide +kernel)

theorem finite_row_works_699 : FiniteTemplate HasSnaky 15 required_699 envelope_699 := by
  refine finite_compose HasSnaky 14 childrenC_699 childrenD_699 finite_children_work_699 (7, 5)
    required_699 envelope_699 pivot_mem_699 child_required_sub_699 child_envelope_sub_699 ?_
  intro b hb
  exact common_sub_699 (mem_commonEnvelope childrenD_699 b hb)

theorem finite_children_work_712_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_712_i1 j) (childrenD_712_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 4 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 5 (10, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_655 7 (10, 7)).mono (by decide +kernel)

theorem finite_row_works_712_i1 : FiniteTemplate HasSnaky 11 required_712_i1 envelope_712_i1 := by
  refine finite_compose HasSnaky 10 childrenC_712_i1 childrenD_712_i1 finite_children_work_712_i1 (6, 4)
    required_712_i1 envelope_712_i1 pivot_mem_712_i1 child_required_sub_712_i1 child_envelope_sub_712_i1 ?_
  intro b hb
  exact common_sub_712_i1 (mem_commonEnvelope childrenD_712_i1 b hb)

theorem finite_children_work_712_i0 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_712_i0 j) (childrenD_712_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_297 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_649 7 (10, 8)).mono (by decide +kernel)
  · exact finite_row_works_712_i1.mono (by decide +kernel)

theorem finite_row_works_712_i0 : FiniteTemplate HasSnaky 13 required_712_i0 envelope_712_i0 := by
  refine finite_compose HasSnaky 12 childrenC_712_i0 childrenD_712_i0 finite_children_work_712_i0 (5, 4)
    required_712_i0 envelope_712_i0 pivot_mem_712_i0 child_required_sub_712_i0 child_envelope_sub_712_i0 ?_
  intro b hb
  exact common_sub_712_i0 (mem_commonEnvelope childrenD_712_i0 b hb)

theorem finite_children_work_712 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_712 j) (childrenD_712 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_174 4 (2, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_508 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_508 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_566 4 (2, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_647 4 (1, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 5 (10, 2)).mono (by decide +kernel)
  · exact finite_row_works_712_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_661 2 (9, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_710 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_711 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_712 : FiniteTemplate HasSnaky 15 required_712 envelope_712 := by
  refine finite_compose HasSnaky 14 childrenC_712 childrenD_712 finite_children_work_712 (5, 6)
    required_712 envelope_712 pivot_mem_712 child_required_sub_712 child_envelope_sub_712 ?_
  intro b hb
  exact common_sub_712 (mem_commonEnvelope childrenD_712 b hb)

theorem finite_children_work_713 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_713 j) (childrenD_713 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_508 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_508 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_605 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_645 4 (1, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_647 4 (1, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_650 5 (10, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_654 4 (2, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_654 6 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_711 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_713 : FiniteTemplate HasSnaky 15 required_713 envelope_713 := by
  refine finite_compose HasSnaky 14 childrenC_713 childrenD_713 finite_children_work_713 (5, 6)
    required_713 envelope_713 pivot_mem_713 child_required_sub_713 child_envelope_sub_713 ?_
  intro b hb
  exact common_sub_713 (mem_commonEnvelope childrenD_713 b hb)

theorem finite_children_work_718_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_718_i0 j) (childrenD_718_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_155 6 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_341 3 (2, 8)).mono (by decide +kernel)

theorem finite_row_works_718_i0 : FiniteTemplate HasSnaky 8 required_718_i0 envelope_718_i0 := by
  refine finite_compose HasSnaky 7 childrenC_718_i0 childrenD_718_i0 finite_children_work_718_i0 (6, 5)
    required_718_i0 envelope_718_i0 pivot_mem_718_i0 child_required_sub_718_i0 child_envelope_sub_718_i0 ?_
  intro b hb
  exact common_sub_718_i0 (mem_commonEnvelope childrenD_718_i0 b hb)

theorem finite_children_work_718_i1 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_718_i1 j) (childrenD_718_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_452 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_520 2 (10, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 4 (5, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_612 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_633 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_718_i1 : FiniteTemplate HasSnaky 13 required_718_i1 envelope_718_i1 := by
  refine finite_compose HasSnaky 12 childrenC_718_i1 childrenD_718_i1 finite_children_work_718_i1 (7, 6)
    required_718_i1 envelope_718_i1 pivot_mem_718_i1 child_required_sub_718_i1 child_envelope_sub_718_i1 ?_
  intro b hb
  exact common_sub_718_i1 (mem_commonEnvelope childrenD_718_i1 b hb)

theorem finite_children_work_718_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_718_i3 j) (childrenD_718_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_232 1 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_232 5 (8, 5)).mono (by decide +kernel)

theorem finite_row_works_718_i3 : FiniteTemplate HasSnaky 6 required_718_i3 envelope_718_i3 := by
  refine finite_compose HasSnaky 5 childrenC_718_i3 childrenD_718_i3 finite_children_work_718_i3 (6, 6)
    required_718_i3 envelope_718_i3 pivot_mem_718_i3 child_required_sub_718_i3 child_envelope_sub_718_i3 ?_
  intro b hb
  exact common_sub_718_i3 (mem_commonEnvelope childrenD_718_i3 b hb)

theorem finite_children_work_718_i5 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_718_i5 j) (childrenD_718_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 3 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_229 5 (9, 3)).mono (by decide +kernel)

theorem finite_row_works_718_i5 : FiniteTemplate HasSnaky 5 required_718_i5 envelope_718_i5 := by
  refine finite_compose HasSnaky 4 childrenC_718_i5 childrenD_718_i5 finite_children_work_718_i5 (7, 3)
    required_718_i5 envelope_718_i5 pivot_mem_718_i5 child_required_sub_718_i5 child_envelope_sub_718_i5 ?_
  intro b hb
  exact common_sub_718_i5 (mem_commonEnvelope childrenD_718_i5 b hb)

theorem finite_children_work_718_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_718_i4 j) (childrenD_718_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 4 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 6 (8, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 0 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_377 2 (8, 3)).mono (by decide +kernel)
  · exact finite_row_works_718_i5.mono (by decide +kernel)

theorem finite_row_works_718_i4 : FiniteTemplate HasSnaky 6 required_718_i4 envelope_718_i4 := by
  refine finite_compose HasSnaky 5 childrenC_718_i4 childrenD_718_i4 finite_children_work_718_i4 (7, 4)
    required_718_i4 envelope_718_i4 pivot_mem_718_i4 child_required_sub_718_i4 child_envelope_sub_718_i4 ?_
  intro b hb
  exact common_sub_718_i4 (mem_commonEnvelope childrenD_718_i4 b hb)

theorem finite_children_work_718_i6 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_718_i6 j) (childrenD_718_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_315 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_317 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_640 4 (3, 9)).mono (by decide +kernel)

theorem finite_row_works_718_i6 : FiniteTemplate HasSnaky 10 required_718_i6 envelope_718_i6 := by
  refine finite_compose HasSnaky 9 childrenC_718_i6 childrenD_718_i6 finite_children_work_718_i6 (6, 6)
    required_718_i6 envelope_718_i6 pivot_mem_718_i6 child_required_sub_718_i6 child_envelope_sub_718_i6 ?_
  intro b hb
  exact common_sub_718_i6 (mem_commonEnvelope childrenD_718_i6 b hb)

theorem finite_children_work_718_i2 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_718_i2 j) (childrenD_718_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_329 5 (10, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_452 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_462 4 (6, 9)).mono (by decide +kernel)
  · exact finite_row_works_718_i3.mono (by decide +kernel)
  · exact finite_row_works_718_i4.mono (by decide +kernel)
  · exact finite_row_works_718_i6.mono (by decide +kernel)

theorem finite_row_works_718_i2 : FiniteTemplate HasSnaky 14 required_718_i2 envelope_718_i2 := by
  refine finite_compose HasSnaky 13 childrenC_718_i2 childrenD_718_i2 finite_children_work_718_i2 (7, 6)
    required_718_i2 envelope_718_i2 pivot_mem_718_i2 child_required_sub_718_i2 child_envelope_sub_718_i2 ?_
  intro b hb
  exact common_sub_718_i2 (mem_commonEnvelope childrenD_718_i2 b hb)

theorem finite_children_work_718 : ∀ j, FiniteTemplate HasSnaky 14 (childrenC_718 j) (childrenD_718 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_120 6 (8, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_276 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_338 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_437 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_611 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_642 0 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_643 0 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_718_i0.mono (by decide +kernel)
  · exact finite_row_works_718_i1.mono (by decide +kernel)
  · exact finite_row_works_718_i2.mono (by decide +kernel)

theorem finite_row_works_718 : FiniteTemplate HasSnaky 15 required_718 envelope_718 := by
  refine finite_compose HasSnaky 14 childrenC_718 childrenD_718 finite_children_work_718 (7, 5)
    required_718 envelope_718 pivot_mem_718 child_required_sub_718 child_envelope_sub_718 ?_
  intro b hb
  exact common_sub_718 (mem_commonEnvelope childrenD_718 b hb)

end FiniteCongruenceChecks.SnakyFinite
