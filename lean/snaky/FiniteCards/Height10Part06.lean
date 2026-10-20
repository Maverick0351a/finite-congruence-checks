/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height10Part06
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height06Part05
import FiniteCards.Height07Part04
import FiniteCards.Height08Part03
import FiniteCards.Height08Part05
import FiniteCards.Height09Part01
import FiniteCards.Height09Part08

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_652_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_652_i3 j) (childrenD_652_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_245 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_652_i3 : FiniteTemplate HasSnaky 4 required_652_i3 envelope_652_i3 := by
  refine finite_compose HasSnaky 3 childrenC_652_i3 childrenD_652_i3 finite_children_work_652_i3 (3, 5)
    required_652_i3 envelope_652_i3 pivot_mem_652_i3 child_required_sub_652_i3 child_envelope_sub_652_i3 ?_
  intro b hb
  exact common_sub_652_i3 (mem_commonEnvelope childrenD_652_i3 b hb)

theorem finite_children_work_652_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_652_i2 j) (childrenD_652_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_36 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 6 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_652_i3.mono (by decide +kernel)

theorem finite_row_works_652_i2 : FiniteTemplate HasSnaky 5 required_652_i2 envelope_652_i2 := by
  refine finite_compose HasSnaky 4 childrenC_652_i2 childrenD_652_i2 finite_children_work_652_i2 (4, 5)
    required_652_i2 envelope_652_i2 pivot_mem_652_i2 child_required_sub_652_i2 child_envelope_sub_652_i2 ?_
  intro b hb
  exact common_sub_652_i2 (mem_commonEnvelope childrenD_652_i2 b hb)

theorem finite_children_work_652_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_652_i1 j) (childrenD_652_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_222 3 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_652_i2.mono (by decide +kernel)

theorem finite_row_works_652_i1 : FiniteTemplate HasSnaky 6 required_652_i1 envelope_652_i1 := by
  refine finite_compose HasSnaky 5 childrenC_652_i1 childrenD_652_i1 finite_children_work_652_i1 (4, 4)
    required_652_i1 envelope_652_i1 pivot_mem_652_i1 child_required_sub_652_i1 child_envelope_sub_652_i1 ?_
  intro b hb
  exact common_sub_652_i1 (mem_commonEnvelope childrenD_652_i1 b hb)

theorem finite_children_work_652_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_652_i0 j) (childrenD_652_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_652_i1.mono (by decide +kernel)

theorem finite_row_works_652_i0 : FiniteTemplate HasSnaky 9 required_652_i0 envelope_652_i0 := by
  refine finite_compose HasSnaky 8 childrenC_652_i0 childrenD_652_i0 finite_children_work_652_i0 (2, 5)
    required_652_i0 envelope_652_i0 pivot_mem_652_i0 child_required_sub_652_i0 child_envelope_sub_652_i0 ?_
  intro b hb
  exact common_sub_652_i0 (mem_commonEnvelope childrenD_652_i0 b hb)

theorem finite_children_work_652 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_652 j) (childrenD_652 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_652_i0.mono (by decide +kernel)

theorem finite_row_works_652 : FiniteTemplate HasSnaky 10 required_652 envelope_652 := by
  refine finite_compose HasSnaky 9 childrenC_652 childrenD_652 finite_children_work_652 (4, 3)
    required_652 envelope_652 pivot_mem_652 child_required_sub_652 child_envelope_sub_652 ?_
  intro b hb
  exact common_sub_652 (mem_commonEnvelope childrenD_652 b hb)

theorem finite_children_work_674 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_674 j) (childrenD_674 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_149 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_673.mono (by decide +kernel)

theorem finite_row_works_674 : FiniteTemplate HasSnaky 10 required_674 envelope_674 := by
  refine finite_compose HasSnaky 9 childrenC_674 childrenD_674 finite_children_work_674 (2, 4)
    required_674 envelope_674 pivot_mem_674 child_required_sub_674 child_envelope_sub_674 ?_
  intro b hb
  exact common_sub_674 (mem_commonEnvelope childrenD_674 b hb)

theorem finite_children_work_702_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_702_i1 j) (childrenD_702_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_40 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_702_i1 : FiniteTemplate HasSnaky 3 required_702_i1 envelope_702_i1 := by
  refine finite_compose HasSnaky 2 childrenC_702_i1 childrenD_702_i1 finite_children_work_702_i1 (1, 1)
    required_702_i1 envelope_702_i1 pivot_mem_702_i1 child_required_sub_702_i1 child_envelope_sub_702_i1 ?_
  intro b hb
  exact common_sub_702_i1 (mem_commonEnvelope childrenD_702_i1 b hb)

theorem finite_children_work_702_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_702_i0 j) (childrenD_702_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_108.mono (by decide +kernel)
  · exact finite_row_works_702_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_511 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_702_i0 : FiniteTemplate HasSnaky 8 required_702_i0 envelope_702_i0 := by
  refine finite_compose HasSnaky 7 childrenC_702_i0 childrenD_702_i0 finite_children_work_702_i0 (4, 2)
    required_702_i0 envelope_702_i0 pivot_mem_702_i0 child_required_sub_702_i0 child_envelope_sub_702_i0 ?_
  intro b hb
  exact common_sub_702_i0 (mem_commonEnvelope childrenD_702_i0 b hb)

theorem finite_children_work_702 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_702 j) (childrenD_702 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_400 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_702_i0.mono (by decide +kernel)

theorem finite_row_works_702 : FiniteTemplate HasSnaky 10 required_702 envelope_702 := by
  refine finite_compose HasSnaky 9 childrenC_702 childrenD_702 finite_children_work_702 (4, 3)
    required_702 envelope_702 pivot_mem_702 child_required_sub_702 child_envelope_sub_702 ?_
  intro b hb
  exact common_sub_702 (mem_commonEnvelope childrenD_702 b hb)

theorem finite_children_work_704_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_704_i1 j) (childrenD_704_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 5 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_306 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_704_i1 : FiniteTemplate HasSnaky 6 required_704_i1 envelope_704_i1 := by
  refine finite_compose HasSnaky 5 childrenC_704_i1 childrenD_704_i1 finite_children_work_704_i1 (4, 6)
    required_704_i1 envelope_704_i1 pivot_mem_704_i1 child_required_sub_704_i1 child_envelope_sub_704_i1 ?_
  intro b hb
  exact common_sub_704_i1 (mem_commonEnvelope childrenD_704_i1 b hb)

theorem finite_children_work_704_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_704_i3 j) (childrenD_704_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_704_i3 : FiniteTemplate HasSnaky 4 required_704_i3 envelope_704_i3 := by
  refine finite_compose HasSnaky 3 childrenC_704_i3 childrenD_704_i3 finite_children_work_704_i3 (5, 5)
    required_704_i3 envelope_704_i3 pivot_mem_704_i3 child_required_sub_704_i3 child_envelope_sub_704_i3 ?_
  intro b hb
  exact common_sub_704_i3 (mem_commonEnvelope childrenD_704_i3 b hb)

theorem finite_children_work_704_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_704_i4 j) (childrenD_704_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 6 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_704_i4 : FiniteTemplate HasSnaky 5 required_704_i4 envelope_704_i4 := by
  refine finite_compose HasSnaky 4 childrenC_704_i4 childrenD_704_i4 finite_children_work_704_i4 (5, 5)
    required_704_i4 envelope_704_i4 pivot_mem_704_i4 child_required_sub_704_i4 child_envelope_sub_704_i4 ?_
  intro b hb
  exact common_sub_704_i4 (mem_commonEnvelope childrenD_704_i4 b hb)

theorem finite_children_work_704_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_704_i5 j) (childrenD_704_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_704_i5 : FiniteTemplate HasSnaky 4 required_704_i5 envelope_704_i5 := by
  refine finite_compose HasSnaky 3 childrenC_704_i5 childrenD_704_i5 finite_children_work_704_i5 (4, 6)
    required_704_i5 envelope_704_i5 pivot_mem_704_i5 child_required_sub_704_i5 child_envelope_sub_704_i5 ?_
  intro b hb
  exact common_sub_704_i5 (mem_commonEnvelope childrenD_704_i5 b hb)

theorem finite_children_work_704_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_704_i2 j) (childrenD_704_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_516 4 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_704_i3.mono (by decide +kernel)
  · exact finite_row_works_704_i4.mono (by decide +kernel)
  · exact finite_row_works_704_i5.mono (by decide +kernel)

theorem finite_row_works_704_i2 : FiniteTemplate HasSnaky 7 required_704_i2 envelope_704_i2 := by
  refine finite_compose HasSnaky 6 childrenC_704_i2 childrenD_704_i2 finite_children_work_704_i2 (4, 3)
    required_704_i2 envelope_704_i2 pivot_mem_704_i2 child_required_sub_704_i2 child_envelope_sub_704_i2 ?_
  intro b hb
  exact common_sub_704_i2 (mem_commonEnvelope childrenD_704_i2 b hb)

theorem finite_children_work_704_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_704_i0 j) (childrenD_704_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 3 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_704_i1.mono (by decide +kernel)
  · exact finite_row_works_703.mono (by decide +kernel)
  · exact finite_row_works_704_i2.mono (by decide +kernel)

theorem finite_row_works_704_i0 : FiniteTemplate HasSnaky 9 required_704_i0 envelope_704_i0 := by
  refine finite_compose HasSnaky 8 childrenC_704_i0 childrenD_704_i0 finite_children_work_704_i0 (4, 5)
    required_704_i0 envelope_704_i0 pivot_mem_704_i0 child_required_sub_704_i0 child_envelope_sub_704_i0 ?_
  intro b hb
  exact common_sub_704_i0 (mem_commonEnvelope childrenD_704_i0 b hb)

theorem finite_children_work_704 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_704 j) (childrenD_704 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_400 4 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_704_i0.mono (by decide +kernel)

theorem finite_row_works_704 : FiniteTemplate HasSnaky 10 required_704 envelope_704 := by
  refine finite_compose HasSnaky 9 childrenC_704 childrenD_704 finite_children_work_704 (4, 4)
    required_704 envelope_704 pivot_mem_704 child_required_sub_704 child_envelope_sub_704 ?_
  intro b hb
  exact common_sub_704 (mem_commonEnvelope childrenD_704 b hb)

theorem finite_children_work_721_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_721_i4 j) (childrenD_721_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_208 6 (5, 7)).mono (by decide +kernel)

theorem finite_row_works_721_i4 : FiniteTemplate HasSnaky 5 required_721_i4 envelope_721_i4 := by
  refine finite_compose HasSnaky 4 childrenC_721_i4 childrenD_721_i4 finite_children_work_721_i4 (2, 6)
    required_721_i4 envelope_721_i4 pivot_mem_721_i4 child_required_sub_721_i4 child_envelope_sub_721_i4 ?_
  intro b hb
  exact common_sub_721_i4 (mem_commonEnvelope childrenD_721_i4 b hb)

theorem finite_children_work_721_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_721_i3 j) (childrenD_721_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_721_i4.mono (by decide +kernel)

theorem finite_row_works_721_i3 : FiniteTemplate HasSnaky 6 required_721_i3 envelope_721_i3 := by
  refine finite_compose HasSnaky 5 childrenC_721_i3 childrenD_721_i3 finite_children_work_721_i3 (4, 6)
    required_721_i3 envelope_721_i3 pivot_mem_721_i3 child_required_sub_721_i3 child_envelope_sub_721_i3 ?_
  intro b hb
  exact common_sub_721_i3 (mem_commonEnvelope childrenD_721_i3 b hb)

theorem finite_children_work_721_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_721_i2 j) (childrenD_721_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 2 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_721_i3.mono (by decide +kernel)

theorem finite_row_works_721_i2 : FiniteTemplate HasSnaky 7 required_721_i2 envelope_721_i2 := by
  refine finite_compose HasSnaky 6 childrenC_721_i2 childrenD_721_i2 finite_children_work_721_i2 (3, 6)
    required_721_i2 envelope_721_i2 pivot_mem_721_i2 child_required_sub_721_i2 child_envelope_sub_721_i2 ?_
  intro b hb
  exact common_sub_721_i2 (mem_commonEnvelope childrenD_721_i2 b hb)

theorem finite_children_work_721_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_721_i1 j) (childrenD_721_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 7 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_721_i2.mono (by decide +kernel)

theorem finite_row_works_721_i1 : FiniteTemplate HasSnaky 8 required_721_i1 envelope_721_i1 := by
  refine finite_compose HasSnaky 7 childrenC_721_i1 childrenD_721_i1 finite_children_work_721_i1 (2, 4)
    required_721_i1 envelope_721_i1 pivot_mem_721_i1 child_required_sub_721_i1 child_envelope_sub_721_i1 ?_
  intro b hb
  exact common_sub_721_i1 (mem_commonEnvelope childrenD_721_i1 b hb)

theorem finite_children_work_721_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_721_i0 j) (childrenD_721_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 5 (6, 3)).mono (by decide +kernel)
  · exact finite_row_works_721_i1.mono (by decide +kernel)

theorem finite_row_works_721_i0 : FiniteTemplate HasSnaky 9 required_721_i0 envelope_721_i0 := by
  refine finite_compose HasSnaky 8 childrenC_721_i0 childrenD_721_i0 finite_children_work_721_i0 (5, 6)
    required_721_i0 envelope_721_i0 pivot_mem_721_i0 child_required_sub_721_i0 child_envelope_sub_721_i0 ?_
  intro b hb
  exact common_sub_721_i0 (mem_commonEnvelope childrenD_721_i0 b hb)

theorem finite_children_work_721 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_721 j) (childrenD_721 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 2 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_176 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_216 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_218 1 (2, 3)).mono (by decide +kernel)
  · exact finite_row_works_721_i0.mono (by decide +kernel)

theorem finite_row_works_721 : FiniteTemplate HasSnaky 10 required_721 envelope_721 := by
  refine finite_compose HasSnaky 9 childrenC_721 childrenD_721 finite_children_work_721 (5, 4)
    required_721 envelope_721 pivot_mem_721 child_required_sub_721 child_envelope_sub_721 ?_
  intro b hb
  exact common_sub_721 (mem_commonEnvelope childrenD_721 b hb)

end FiniteCongruenceChecks.SnakyFinite
