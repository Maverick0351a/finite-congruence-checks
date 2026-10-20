/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height07Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part05
import FiniteCards.Height05Part06
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_593_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_593_i0 j) (childrenD_593_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_36 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_105 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_250 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_592 4 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_593_i0 : FiniteTemplate HasSnaky 6 required_593_i0 envelope_593_i0 := by
  refine finite_compose HasSnaky 5 childrenC_593_i0 childrenD_593_i0 finite_children_work_593_i0 (4, 5)
    required_593_i0 envelope_593_i0 pivot_mem_593_i0 child_required_sub_593_i0 child_envelope_sub_593_i0 ?_
  intro b hb
  exact common_sub_593_i0 (mem_commonEnvelope childrenD_593_i0 b hb)

theorem finite_children_work_593 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_593 j) (childrenD_593 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_593_i0.mono (by decide +kernel)

theorem finite_row_works_593 : FiniteTemplate HasSnaky 7 required_593 envelope_593 := by
  refine finite_compose HasSnaky 6 childrenC_593 childrenD_593 finite_children_work_593 (4, 3)
    required_593 envelope_593 pivot_mem_593 child_required_sub_593 child_envelope_sub_593 ?_
  intro b hb
  exact common_sub_593 (mem_commonEnvelope childrenD_593 b hb)

theorem finite_children_work_610 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_610 j) (childrenD_610 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 5 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_225 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_609 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_610 : FiniteTemplate HasSnaky 7 required_610 envelope_610 := by
  refine finite_compose HasSnaky 6 childrenC_610 childrenD_610 finite_children_work_610 (1, 5)
    required_610 envelope_610 pivot_mem_610 child_required_sub_610 child_envelope_sub_610 ?_
  intro b hb
  exact common_sub_610 (mem_commonEnvelope childrenD_610 b hb)

theorem finite_children_work_620_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_620_i0 j) (childrenD_620_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_233 5 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_620_i0 : FiniteTemplate HasSnaky 6 required_620_i0 envelope_620_i0 := by
  refine finite_compose HasSnaky 5 childrenC_620_i0 childrenD_620_i0 finite_children_work_620_i0 (3, 3)
    required_620_i0 envelope_620_i0 pivot_mem_620_i0 child_required_sub_620_i0 child_envelope_sub_620_i0 ?_
  intro b hb
  exact common_sub_620_i0 (mem_commonEnvelope childrenD_620_i0 b hb)

theorem finite_children_work_620 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_620 j) (childrenD_620 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_57 5 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_57 7 (6, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_293 5 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_293 7 (6, 7)).mono (by decide +kernel)
  · exact finite_row_works_620_i0.mono (by decide +kernel)

theorem finite_row_works_620 : FiniteTemplate HasSnaky 7 required_620 envelope_620 := by
  refine finite_compose HasSnaky 6 childrenC_620 childrenD_620 finite_children_work_620 (4, 5)
    required_620 envelope_620 pivot_mem_620 child_required_sub_620 child_envelope_sub_620 ?_
  intro b hb
  exact common_sub_620 (mem_commonEnvelope childrenD_620 b hb)

theorem finite_children_work_621_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_621_i0 j) (childrenD_621_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_159 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_164 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_621_i0 : FiniteTemplate HasSnaky 6 required_621_i0 envelope_621_i0 := by
  refine finite_compose HasSnaky 5 childrenC_621_i0 childrenD_621_i0 finite_children_work_621_i0 (2, 3)
    required_621_i0 envelope_621_i0 pivot_mem_621_i0 child_required_sub_621_i0 child_envelope_sub_621_i0 ?_
  intro b hb
  exact common_sub_621_i0 (mem_commonEnvelope childrenD_621_i0 b hb)

theorem finite_children_work_621_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_621_i1 j) (childrenD_621_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 4 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_621_i1 : FiniteTemplate HasSnaky 6 required_621_i1 envelope_621_i1 := by
  refine finite_compose HasSnaky 5 childrenC_621_i1 childrenD_621_i1 finite_children_work_621_i1 (1, 4)
    required_621_i1 envelope_621_i1 pivot_mem_621_i1 child_required_sub_621_i1 child_envelope_sub_621_i1 ?_
  intro b hb
  exact common_sub_621_i1 (mem_commonEnvelope childrenD_621_i1 b hb)

theorem finite_children_work_621 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_621 j) (childrenD_621 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_206 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_238 5 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_414 7 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_417 6 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_621_i0.mono (by decide +kernel)
  · exact finite_row_works_621_i1.mono (by decide +kernel)

theorem finite_row_works_621 : FiniteTemplate HasSnaky 7 required_621 envelope_621 := by
  refine finite_compose HasSnaky 6 childrenC_621 childrenD_621 finite_children_work_621 (2, 4)
    required_621 envelope_621 pivot_mem_621 child_required_sub_621 child_envelope_sub_621 ?_
  intro b hb
  exact common_sub_621 (mem_commonEnvelope childrenD_621 b hb)

theorem finite_children_work_628_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_628_i0 j) (childrenD_628_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_36 7 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_628_i0 : FiniteTemplate HasSnaky 4 required_628_i0 envelope_628_i0 := by
  refine finite_compose HasSnaky 3 childrenC_628_i0 childrenD_628_i0 finite_children_work_628_i0 (3, 2)
    required_628_i0 envelope_628_i0 pivot_mem_628_i0 child_required_sub_628_i0 child_envelope_sub_628_i0 ?_
  intro b hb
  exact common_sub_628_i0 (mem_commonEnvelope childrenD_628_i0 b hb)

theorem finite_children_work_628_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_628_i1 j) (childrenD_628_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_464 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_628_i1 : FiniteTemplate HasSnaky 6 required_628_i1 envelope_628_i1 := by
  refine finite_compose HasSnaky 5 childrenC_628_i1 childrenD_628_i1 finite_children_work_628_i1 (3, 4)
    required_628_i1 envelope_628_i1 pivot_mem_628_i1 child_required_sub_628_i1 child_envelope_sub_628_i1 ?_
  intro b hb
  exact common_sub_628_i1 (mem_commonEnvelope childrenD_628_i1 b hb)

theorem finite_children_work_628_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_628_i2 j) (childrenD_628_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_265 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_628_i2 : FiniteTemplate HasSnaky 6 required_628_i2 envelope_628_i2 := by
  refine finite_compose HasSnaky 5 childrenC_628_i2 childrenD_628_i2 finite_children_work_628_i2 (2, 3)
    required_628_i2 envelope_628_i2 pivot_mem_628_i2 child_required_sub_628_i2 child_envelope_sub_628_i2 ?_
  intro b hb
  exact common_sub_628_i2 (mem_commonEnvelope childrenD_628_i2 b hb)

theorem finite_children_work_628 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_628 j) (childrenD_628 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_126 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_270 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_628_i0.mono (by decide +kernel)
  · exact finite_row_works_628_i1.mono (by decide +kernel)
  · exact finite_row_works_628_i2.mono (by decide +kernel)

theorem finite_row_works_628 : FiniteTemplate HasSnaky 7 required_628 envelope_628 := by
  refine finite_compose HasSnaky 6 childrenC_628 childrenD_628 finite_children_work_628 (3, 3)
    required_628 envelope_628 pivot_mem_628 child_required_sub_628 child_envelope_sub_628 ?_
  intro b hb
  exact common_sub_628 (mem_commonEnvelope childrenD_628 b hb)

theorem finite_children_work_633_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_633_i1 j) (childrenD_633_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_93 3 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_633_i1 : FiniteTemplate HasSnaky 5 required_633_i1 envelope_633_i1 := by
  refine finite_compose HasSnaky 4 childrenC_633_i1 childrenD_633_i1 finite_children_work_633_i1 (5, 3)
    required_633_i1 envelope_633_i1 pivot_mem_633_i1 child_required_sub_633_i1 child_envelope_sub_633_i1 ?_
  intro b hb
  exact common_sub_633_i1 (mem_commonEnvelope childrenD_633_i1 b hb)

theorem finite_children_work_633_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_633_i0 j) (childrenD_633_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_27 2 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_144 3 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_633_i1.mono (by decide +kernel)

theorem finite_row_works_633_i0 : FiniteTemplate HasSnaky 6 required_633_i0 envelope_633_i0 := by
  refine finite_compose HasSnaky 5 childrenC_633_i0 childrenD_633_i0 finite_children_work_633_i0 (5, 6)
    required_633_i0 envelope_633_i0 pivot_mem_633_i0 child_required_sub_633_i0 child_envelope_sub_633_i0 ?_
  intro b hb
  exact common_sub_633_i0 (mem_commonEnvelope childrenD_633_i0 b hb)

theorem finite_children_work_633 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_633 j) (childrenD_633 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_47 6 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_144 6 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_633_i0.mono (by decide +kernel)

theorem finite_row_works_633 : FiniteTemplate HasSnaky 7 required_633 envelope_633 := by
  refine finite_compose HasSnaky 6 childrenC_633 childrenD_633 finite_children_work_633 (4, 4)
    required_633 envelope_633 pivot_mem_633 child_required_sub_633 child_envelope_sub_633 ?_
  intro b hb
  exact common_sub_633 (mem_commonEnvelope childrenD_633 b hb)

theorem finite_children_work_637_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_637_i2 j) (childrenD_637_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 6 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 1 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_637_i2 : FiniteTemplate HasSnaky 4 required_637_i2 envelope_637_i2 := by
  refine finite_compose HasSnaky 3 childrenC_637_i2 childrenD_637_i2 finite_children_work_637_i2 (4, 4)
    required_637_i2 envelope_637_i2 pivot_mem_637_i2 child_required_sub_637_i2 child_envelope_sub_637_i2 ?_
  intro b hb
  exact common_sub_637_i2 (mem_commonEnvelope childrenD_637_i2 b hb)

theorem finite_children_work_637_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_637_i1 j) (childrenD_637_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_637_i2.mono (by decide +kernel)

theorem finite_row_works_637_i1 : FiniteTemplate HasSnaky 5 required_637_i1 envelope_637_i1 := by
  refine finite_compose HasSnaky 4 childrenC_637_i1 childrenD_637_i1 finite_children_work_637_i1 (3, 3)
    required_637_i1 envelope_637_i1 pivot_mem_637_i1 child_required_sub_637_i1 child_envelope_sub_637_i1 ?_
  intro b hb
  exact common_sub_637_i1 (mem_commonEnvelope childrenD_637_i1 b hb)

theorem finite_children_work_637_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_637_i0 j) (childrenD_637_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_637_i1.mono (by decide +kernel)

theorem finite_row_works_637_i0 : FiniteTemplate HasSnaky 6 required_637_i0 envelope_637_i0 := by
  refine finite_compose HasSnaky 5 childrenC_637_i0 childrenD_637_i0 finite_children_work_637_i0 (4, 3)
    required_637_i0 envelope_637_i0 pivot_mem_637_i0 child_required_sub_637_i0 child_envelope_sub_637_i0 ?_
  intro b hb
  exact common_sub_637_i0 (mem_commonEnvelope childrenD_637_i0 b hb)

theorem finite_children_work_637 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_637 j) (childrenD_637 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 3 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_48 3 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_637_i0.mono (by decide +kernel)

theorem finite_row_works_637 : FiniteTemplate HasSnaky 7 required_637 envelope_637 := by
  refine finite_compose HasSnaky 6 childrenC_637 childrenD_637 finite_children_work_637 (4, 2)
    required_637 envelope_637 pivot_mem_637 child_required_sub_637 child_envelope_sub_637 ?_
  intro b hb
  exact common_sub_637 (mem_commonEnvelope childrenD_637 b hb)

theorem finite_children_work_671_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_671_i0 j) (childrenD_671_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 7 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_464 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_671_i0 : FiniteTemplate HasSnaky 6 required_671_i0 envelope_671_i0 := by
  refine finite_compose HasSnaky 5 childrenC_671_i0 childrenD_671_i0 finite_children_work_671_i0 (3, 4)
    required_671_i0 envelope_671_i0 pivot_mem_671_i0 child_required_sub_671_i0 child_envelope_sub_671_i0 ?_
  intro b hb
  exact common_sub_671_i0 (mem_commonEnvelope childrenD_671_i0 b hb)

theorem finite_children_work_671 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_671 j) (childrenD_671 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_126 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_126 3 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_671_i0.mono (by decide +kernel)

theorem finite_row_works_671 : FiniteTemplate HasSnaky 7 required_671 envelope_671 := by
  refine finite_compose HasSnaky 6 childrenC_671 childrenD_671 finite_children_work_671 (3, 3)
    required_671 envelope_671 pivot_mem_671 child_required_sub_671 child_envelope_sub_671 ?_
  intro b hb
  exact common_sub_671 (mem_commonEnvelope childrenD_671 b hb)

theorem finite_children_work_680_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_680_i0 j) (childrenD_680_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_56 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 6 (5, 5)).mono (by decide +kernel)

theorem finite_row_works_680_i0 : FiniteTemplate HasSnaky 6 required_680_i0 envelope_680_i0 := by
  refine finite_compose HasSnaky 5 childrenC_680_i0 childrenD_680_i0 finite_children_work_680_i0 (1, 3)
    required_680_i0 envelope_680_i0 pivot_mem_680_i0 child_required_sub_680_i0 child_envelope_sub_680_i0 ?_
  intro b hb
  exact common_sub_680_i0 (mem_commonEnvelope childrenD_680_i0 b hb)

theorem finite_children_work_680 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_680 j) (childrenD_680 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_680_i0.mono (by decide +kernel)

theorem finite_row_works_680 : FiniteTemplate HasSnaky 7 required_680 envelope_680 := by
  refine finite_compose HasSnaky 6 childrenC_680 childrenD_680 finite_children_work_680 (3, 3)
    required_680 envelope_680 pivot_mem_680 child_required_sub_680 child_envelope_sub_680 ?_
  intro b hb
  exact common_sub_680 (mem_commonEnvelope childrenD_680 b hb)

end FiniteCongruenceChecks.SnakyFinite
