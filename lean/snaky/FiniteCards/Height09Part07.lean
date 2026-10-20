/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part07
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part05
import FiniteCards.Height08Part03
import FiniteCards.Height08Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_622_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_622_i0 j) (childrenD_622_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_41 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 7 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_622_i0 : FiniteTemplate HasSnaky 5 required_622_i0 envelope_622_i0 := by
  refine finite_compose HasSnaky 4 childrenC_622_i0 childrenD_622_i0 finite_children_work_622_i0 (3, 6)
    required_622_i0 envelope_622_i0 pivot_mem_622_i0 child_required_sub_622_i0 child_envelope_sub_622_i0 ?_
  intro b hb
  exact common_sub_622_i0 (mem_commonEnvelope childrenD_622_i0 b hb)

theorem finite_children_work_622_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_622_i2 j) (childrenD_622_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 2 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_622_i2 : FiniteTemplate HasSnaky 5 required_622_i2 envelope_622_i2 := by
  refine finite_compose HasSnaky 4 childrenC_622_i2 childrenD_622_i2 finite_children_work_622_i2 (3, 6)
    required_622_i2 envelope_622_i2 pivot_mem_622_i2 child_required_sub_622_i2 child_envelope_sub_622_i2 ?_
  intro b hb
  exact common_sub_622_i2 (mem_commonEnvelope childrenD_622_i2 b hb)

theorem finite_children_work_622_i3 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_622_i3 j) (childrenD_622_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 4 (3, 6)).mono (by decide +kernel)

theorem finite_row_works_622_i3 : FiniteTemplate HasSnaky 3 required_622_i3 envelope_622_i3 := by
  refine finite_compose HasSnaky 2 childrenC_622_i3 childrenD_622_i3 finite_children_work_622_i3 (3, 2)
    required_622_i3 envelope_622_i3 pivot_mem_622_i3 child_required_sub_622_i3 child_envelope_sub_622_i3 ?_
  intro b hb
  exact common_sub_622_i3 (mem_commonEnvelope childrenD_622_i3 b hb)

theorem finite_children_work_622_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_622_i1 j) (childrenD_622_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_61 6 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_622_i2.mono (by decide +kernel)
  · exact finite_row_works_622_i3.mono (by decide +kernel)

theorem finite_row_works_622_i1 : FiniteTemplate HasSnaky 6 required_622_i1 envelope_622_i1 := by
  refine finite_compose HasSnaky 5 childrenC_622_i1 childrenD_622_i1 finite_children_work_622_i1 (2, 2)
    required_622_i1 envelope_622_i1 pivot_mem_622_i1 child_required_sub_622_i1 child_envelope_sub_622_i1 ?_
  intro b hb
  exact common_sub_622_i1 (mem_commonEnvelope childrenD_622_i1 b hb)

theorem finite_children_work_622_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_622_i4 j) (childrenD_622_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_621 2 (7, 1)).mono (by decide +kernel)

theorem finite_row_works_622_i4 : FiniteTemplate HasSnaky 8 required_622_i4 envelope_622_i4 := by
  refine finite_compose HasSnaky 7 childrenC_622_i4 childrenD_622_i4 finite_children_work_622_i4 (4, 5)
    required_622_i4 envelope_622_i4 pivot_mem_622_i4 child_required_sub_622_i4 child_envelope_sub_622_i4 ?_
  intro b hb
  exact common_sub_622_i4 (mem_commonEnvelope childrenD_622_i4 b hb)

theorem finite_children_work_622 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_622 j) (childrenD_622 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_57 7 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_622_i0.mono (by decide +kernel)
  · exact finite_row_works_622_i1.mono (by decide +kernel)
  · exact finite_row_works_622_i4.mono (by decide +kernel)

theorem finite_row_works_622 : FiniteTemplate HasSnaky 9 required_622 envelope_622 := by
  refine finite_compose HasSnaky 8 childrenC_622 childrenD_622 finite_children_work_622 (4, 4)
    required_622 envelope_622 pivot_mem_622 child_required_sub_622 child_envelope_sub_622 ?_
  intro b hb
  exact common_sub_622 (mem_commonEnvelope childrenD_622 b hb)

theorem finite_children_work_629 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_629 j) (childrenD_629 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_190 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_295 2 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_364 2 (6, 1)).mono (by decide +kernel)
  · exact finite_row_works_518.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_628 4 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_629 : FiniteTemplate HasSnaky 9 required_629 envelope_629 := by
  refine finite_compose HasSnaky 8 childrenC_629 childrenD_629 finite_children_work_629 (3, 5)
    required_629 envelope_629 pivot_mem_629 child_required_sub_629 child_envelope_sub_629 ?_
  intro b hb
  exact common_sub_629 (mem_commonEnvelope childrenD_629 b hb)

theorem finite_children_work_638_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_638_i0 j) (childrenD_638_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_85 4 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_638_i0 : FiniteTemplate HasSnaky 7 required_638_i0 envelope_638_i0 := by
  refine finite_compose HasSnaky 6 childrenC_638_i0 childrenD_638_i0 finite_children_work_638_i0 (3, 4)
    required_638_i0 envelope_638_i0 pivot_mem_638_i0 child_required_sub_638_i0 child_envelope_sub_638_i0 ?_
  intro b hb
  exact common_sub_638_i0 (mem_commonEnvelope childrenD_638_i0 b hb)

theorem finite_children_work_638 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_638 j) (childrenD_638 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_57 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_136 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_217 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_530 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_638_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_637 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_638 : FiniteTemplate HasSnaky 9 required_638 envelope_638 := by
  refine finite_compose HasSnaky 8 childrenC_638 childrenD_638 finite_children_work_638 (3, 3)
    required_638 envelope_638 pivot_mem_638 child_required_sub_638 child_envelope_sub_638 ?_
  intro b hb
  exact common_sub_638 (mem_commonEnvelope childrenD_638 b hb)

theorem finite_children_work_640_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_640_i3 j) (childrenD_640_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_90 0 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_640_i3 : FiniteTemplate HasSnaky 5 required_640_i3 envelope_640_i3 := by
  refine finite_compose HasSnaky 4 childrenC_640_i3 childrenD_640_i3 finite_children_work_640_i3 (5, 6)
    required_640_i3 envelope_640_i3 pivot_mem_640_i3 child_required_sub_640_i3 child_envelope_sub_640_i3 ?_
  intro b hb
  exact common_sub_640_i3 (mem_commonEnvelope childrenD_640_i3 b hb)

theorem finite_children_work_640_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_640_i2 j) (childrenD_640_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_260 5 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_640_i3.mono (by decide +kernel)

theorem finite_row_works_640_i2 : FiniteTemplate HasSnaky 6 required_640_i2 envelope_640_i2 := by
  refine finite_compose HasSnaky 5 childrenC_640_i2 childrenD_640_i2 finite_children_work_640_i2 (2, 6)
    required_640_i2 envelope_640_i2 pivot_mem_640_i2 child_required_sub_640_i2 child_envelope_sub_640_i2 ?_
  intro b hb
  exact common_sub_640_i2 (mem_commonEnvelope childrenD_640_i2 b hb)

theorem finite_children_work_640_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_640_i1 j) (childrenD_640_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_640_i2.mono (by decide +kernel)

theorem finite_row_works_640_i1 : FiniteTemplate HasSnaky 7 required_640_i1 envelope_640_i1 := by
  refine finite_compose HasSnaky 6 childrenC_640_i1 childrenD_640_i1 finite_children_work_640_i1 (4, 6)
    required_640_i1 envelope_640_i1 pivot_mem_640_i1 child_required_sub_640_i1 child_envelope_sub_640_i1 ?_
  intro b hb
  exact common_sub_640_i1 (mem_commonEnvelope childrenD_640_i1 b hb)

theorem finite_children_work_640_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_640_i0 j) (childrenD_640_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_61 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_89 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_183 5 (6, 2)).mono (by decide +kernel)
  · exact finite_row_works_640_i1.mono (by decide +kernel)

theorem finite_row_works_640_i0 : FiniteTemplate HasSnaky 8 required_640_i0 envelope_640_i0 := by
  refine finite_compose HasSnaky 7 childrenC_640_i0 childrenD_640_i0 finite_children_work_640_i0 (3, 6)
    required_640_i0 envelope_640_i0 pivot_mem_640_i0 child_required_sub_640_i0 child_envelope_sub_640_i0 ?_
  intro b hb
  exact common_sub_640_i0 (mem_commonEnvelope childrenD_640_i0 b hb)

theorem finite_children_work_640 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_640 j) (childrenD_640 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_640_i0.mono (by decide +kernel)

theorem finite_row_works_640 : FiniteTemplate HasSnaky 9 required_640 envelope_640 := by
  refine finite_compose HasSnaky 8 childrenC_640 childrenD_640 finite_children_work_640 (4, 5)
    required_640 envelope_640 pivot_mem_640 child_required_sub_640 child_envelope_sub_640 ?_
  intro b hb
  exact common_sub_640 (mem_commonEnvelope childrenD_640 b hb)

theorem finite_children_work_655_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_655_i0 j) (childrenD_655_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_179 5 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_344 7 (5, 7)).mono (by decide +kernel)

theorem finite_row_works_655_i0 : FiniteTemplate HasSnaky 8 required_655_i0 envelope_655_i0 := by
  refine finite_compose HasSnaky 7 childrenC_655_i0 childrenD_655_i0 finite_children_work_655_i0 (3, 6)
    required_655_i0 envelope_655_i0 pivot_mem_655_i0 child_required_sub_655_i0 child_envelope_sub_655_i0 ?_
  intro b hb
  exact common_sub_655_i0 (mem_commonEnvelope childrenD_655_i0 b hb)

theorem finite_children_work_655 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_655 j) (childrenD_655 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 7 (6, 6)).mono (by decide +kernel)
  · exact finite_row_works_655_i0.mono (by decide +kernel)

theorem finite_row_works_655 : FiniteTemplate HasSnaky 9 required_655 envelope_655 := by
  refine finite_compose HasSnaky 8 childrenC_655 childrenD_655 finite_children_work_655 (3, 3)
    required_655 envelope_655 pivot_mem_655 child_required_sub_655 child_envelope_sub_655 ?_
  intro b hb
  exact common_sub_655 (mem_commonEnvelope childrenD_655 b hb)

theorem finite_children_work_659 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_659 j) (childrenD_659 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_658 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_659 : FiniteTemplate HasSnaky 9 required_659 envelope_659 := by
  refine finite_compose HasSnaky 8 childrenC_659 childrenD_659 finite_children_work_659 (3, 4)
    required_659 envelope_659 pivot_mem_659 child_required_sub_659 child_envelope_sub_659 ?_
  intro b hb
  exact common_sub_659 (mem_commonEnvelope childrenD_659 b hb)

theorem finite_children_work_662_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_662_i0 j) (childrenD_662_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_141 2 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_662_i0 : FiniteTemplate HasSnaky 5 required_662_i0 envelope_662_i0 := by
  refine finite_compose HasSnaky 4 childrenC_662_i0 childrenD_662_i0 finite_children_work_662_i0 (1, 5)
    required_662_i0 envelope_662_i0 pivot_mem_662_i0 child_required_sub_662_i0 child_envelope_sub_662_i0 ?_
  intro b hb
  exact common_sub_662_i0 (mem_commonEnvelope childrenD_662_i0 b hb)

theorem finite_children_work_662 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_662 j) (childrenD_662 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_658 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_662_i0.mono (by decide +kernel)

theorem finite_row_works_662 : FiniteTemplate HasSnaky 9 required_662 envelope_662 := by
  refine finite_compose HasSnaky 8 childrenC_662 childrenD_662 finite_children_work_662 (4, 4)
    required_662 envelope_662 pivot_mem_662 child_required_sub_662 child_envelope_sub_662 ?_
  intro b hb
  exact common_sub_662 (mem_commonEnvelope childrenD_662 b hb)

theorem finite_children_work_667 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_667 j) (childrenD_667 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (4, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_666 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_667 : FiniteTemplate HasSnaky 9 required_667 envelope_667 := by
  refine finite_compose HasSnaky 8 childrenC_667 childrenD_667 finite_children_work_667 (3, 4)
    required_667 envelope_667 pivot_mem_667 child_required_sub_667 child_envelope_sub_667 ?_
  intro b hb
  exact common_sub_667 (mem_commonEnvelope childrenD_667 b hb)

theorem finite_children_work_668 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_668 j) (childrenD_668 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_666 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_668 : FiniteTemplate HasSnaky 9 required_668 envelope_668 := by
  refine finite_compose HasSnaky 8 childrenC_668 childrenD_668 finite_children_work_668 (3, 4)
    required_668 envelope_668 pivot_mem_668 child_required_sub_668 child_envelope_sub_668 ?_
  intro b hb
  exact common_sub_668 (mem_commonEnvelope childrenD_668 b hb)

end FiniteCongruenceChecks.SnakyFinite
