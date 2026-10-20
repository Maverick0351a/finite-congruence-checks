/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part06
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height04Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_495_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_495_i0 j) (childrenD_495_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_221 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_495_i0 : FiniteTemplate HasSnaky 4 required_495_i0 envelope_495_i0 := by
  refine finite_compose HasSnaky 3 childrenC_495_i0 childrenD_495_i0 finite_children_work_495_i0 (2, 2)
    required_495_i0 envelope_495_i0 pivot_mem_495_i0 child_required_sub_495_i0 child_envelope_sub_495_i0 ?_
  intro b hb
  exact common_sub_495_i0 (mem_commonEnvelope childrenD_495_i0 b hb)

theorem finite_children_work_495 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_495 j) (childrenD_495 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_495_i0.mono (by decide +kernel)

theorem finite_row_works_495 : FiniteTemplate HasSnaky 5 required_495 envelope_495 := by
  refine finite_compose HasSnaky 4 childrenC_495 childrenD_495 finite_children_work_495 (2, 4)
    required_495 envelope_495 pivot_mem_495 child_required_sub_495 child_envelope_sub_495 ?_
  intro b hb
  exact common_sub_495 (mem_commonEnvelope childrenD_495 b hb)

theorem finite_children_work_497 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_497 j) (childrenD_497 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_496.mono (by decide +kernel)

theorem finite_row_works_497 : FiniteTemplate HasSnaky 5 required_497 envelope_497 := by
  refine finite_compose HasSnaky 4 childrenC_497 childrenD_497 finite_children_work_497 (0, 3)
    required_497 envelope_497 pivot_mem_497 child_required_sub_497 child_envelope_sub_497 ?_
  intro b hb
  exact common_sub_497 (mem_commonEnvelope childrenD_497 b hb)

theorem finite_children_work_501 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_501 j) (childrenD_501 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 2 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_500.mono (by decide +kernel)

theorem finite_row_works_501 : FiniteTemplate HasSnaky 5 required_501 envelope_501 := by
  refine finite_compose HasSnaky 4 childrenC_501 childrenD_501 finite_children_work_501 (1, 3)
    required_501 envelope_501 pivot_mem_501 child_required_sub_501 child_envelope_sub_501 ?_
  intro b hb
  exact common_sub_501 (mem_commonEnvelope childrenD_501 b hb)

theorem finite_children_work_502_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_502_i0 j) (childrenD_502_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 4 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_502_i0 : FiniteTemplate HasSnaky 4 required_502_i0 envelope_502_i0 := by
  refine finite_compose HasSnaky 3 childrenC_502_i0 childrenD_502_i0 finite_children_work_502_i0 (2, 4)
    required_502_i0 envelope_502_i0 pivot_mem_502_i0 child_required_sub_502_i0 child_envelope_sub_502_i0 ?_
  intro b hb
  exact common_sub_502_i0 (mem_commonEnvelope childrenD_502_i0 b hb)

theorem finite_children_work_502 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_502 j) (childrenD_502 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_69 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_502_i0.mono (by decide +kernel)

theorem finite_row_works_502 : FiniteTemplate HasSnaky 5 required_502 envelope_502 := by
  refine finite_compose HasSnaky 4 childrenC_502 childrenD_502 finite_children_work_502 (4, 3)
    required_502 envelope_502 pivot_mem_502 child_required_sub_502 child_envelope_sub_502 ?_
  intro b hb
  exact common_sub_502 (mem_commonEnvelope childrenD_502 b hb)

theorem finite_children_work_505_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_505_i0 j) (childrenD_505_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_350 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_505_i0 : FiniteTemplate HasSnaky 4 required_505_i0 envelope_505_i0 := by
  refine finite_compose HasSnaky 3 childrenC_505_i0 childrenD_505_i0 finite_children_work_505_i0 (4, 2)
    required_505_i0 envelope_505_i0 pivot_mem_505_i0 child_required_sub_505_i0 child_envelope_sub_505_i0 ?_
  intro b hb
  exact common_sub_505_i0 (mem_commonEnvelope childrenD_505_i0 b hb)

theorem finite_children_work_505_i2 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_505_i2 j) (childrenD_505_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 0 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_505_i2 : FiniteTemplate HasSnaky 3 required_505_i2 envelope_505_i2 := by
  refine finite_compose HasSnaky 2 childrenC_505_i2 childrenD_505_i2 finite_children_work_505_i2 (4, 3)
    required_505_i2 envelope_505_i2 pivot_mem_505_i2 child_required_sub_505_i2 child_envelope_sub_505_i2 ?_
  intro b hb
  exact common_sub_505_i2 (mem_commonEnvelope childrenD_505_i2 b hb)

theorem finite_children_work_505_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_505_i1 j) (childrenD_505_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_505_i2.mono (by decide +kernel)

theorem finite_row_works_505_i1 : FiniteTemplate HasSnaky 4 required_505_i1 envelope_505_i1 := by
  refine finite_compose HasSnaky 3 childrenC_505_i1 childrenD_505_i1 finite_children_work_505_i1 (4, 2)
    required_505_i1 envelope_505_i1 pivot_mem_505_i1 child_required_sub_505_i1 child_envelope_sub_505_i1 ?_
  intro b hb
  exact common_sub_505_i1 (mem_commonEnvelope childrenD_505_i1 b hb)

theorem finite_children_work_505 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_505 j) (childrenD_505 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_505_i0.mono (by decide +kernel)
  · exact finite_row_works_505_i1.mono (by decide +kernel)

theorem finite_row_works_505 : FiniteTemplate HasSnaky 5 required_505 envelope_505 := by
  refine finite_compose HasSnaky 4 childrenC_505 childrenD_505 finite_children_work_505 (4, 1)
    required_505 envelope_505 pivot_mem_505 child_required_sub_505 child_envelope_sub_505 ?_
  intro b hb
  exact common_sub_505 (mem_commonEnvelope childrenD_505 b hb)

theorem finite_children_work_506_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_506_i0 j) (childrenD_506_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_506_i0 : FiniteTemplate HasSnaky 4 required_506_i0 envelope_506_i0 := by
  refine finite_compose HasSnaky 3 childrenC_506_i0 childrenD_506_i0 finite_children_work_506_i0 (1, 2)
    required_506_i0 envelope_506_i0 pivot_mem_506_i0 child_required_sub_506_i0 child_envelope_sub_506_i0 ?_
  intro b hb
  exact common_sub_506_i0 (mem_commonEnvelope childrenD_506_i0 b hb)

theorem finite_children_work_506 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_506 j) (childrenD_506 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_67 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_506_i0.mono (by decide +kernel)

theorem finite_row_works_506 : FiniteTemplate HasSnaky 5 required_506 envelope_506 := by
  refine finite_compose HasSnaky 4 childrenC_506 childrenD_506 finite_children_work_506 (1, 5)
    required_506 envelope_506 pivot_mem_506 child_required_sub_506 child_envelope_sub_506 ?_
  intro b hb
  exact common_sub_506 (mem_commonEnvelope childrenD_506 b hb)

theorem finite_children_work_515_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_515_i0 j) (childrenD_515_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_78.mono (by decide +kernel)

theorem finite_row_works_515_i0 : FiniteTemplate HasSnaky 4 required_515_i0 envelope_515_i0 := by
  refine finite_compose HasSnaky 3 childrenC_515_i0 childrenD_515_i0 finite_children_work_515_i0 (3, 1)
    required_515_i0 envelope_515_i0 pivot_mem_515_i0 child_required_sub_515_i0 child_envelope_sub_515_i0 ?_
  intro b hb
  exact common_sub_515_i0 (mem_commonEnvelope childrenD_515_i0 b hb)

theorem finite_children_work_515 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_515 j) (childrenD_515 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 7 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_515_i0.mono (by decide +kernel)

theorem finite_row_works_515 : FiniteTemplate HasSnaky 5 required_515 envelope_515 := by
  refine finite_compose HasSnaky 4 childrenC_515 childrenD_515 finite_children_work_515 (2, 1)
    required_515 envelope_515 pivot_mem_515 child_required_sub_515 child_envelope_sub_515 ?_
  intro b hb
  exact common_sub_515 (mem_commonEnvelope childrenD_515 b hb)

theorem finite_children_work_592_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_592_i0 j) (childrenD_592_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_158 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_592_i0 : FiniteTemplate HasSnaky 4 required_592_i0 envelope_592_i0 := by
  refine finite_compose HasSnaky 3 childrenC_592_i0 childrenD_592_i0 finite_children_work_592_i0 (1, 5)
    required_592_i0 envelope_592_i0 pivot_mem_592_i0 child_required_sub_592_i0 child_envelope_sub_592_i0 ?_
  intro b hb
  exact common_sub_592_i0 (mem_commonEnvelope childrenD_592_i0 b hb)

theorem finite_children_work_592 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_592 j) (childrenD_592 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_36 6 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_150.mono (by decide +kernel)
  · exact finite_row_works_592_i0.mono (by decide +kernel)

theorem finite_row_works_592 : FiniteTemplate HasSnaky 5 required_592 envelope_592 := by
  refine finite_compose HasSnaky 4 childrenC_592 childrenD_592 finite_children_work_592 (1, 4)
    required_592 envelope_592 pivot_mem_592 child_required_sub_592 child_envelope_sub_592 ?_
  intro b hb
  exact common_sub_592 (mem_commonEnvelope childrenD_592 b hb)

theorem finite_children_work_612_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_612_i1 j) (childrenD_612_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 2 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_612_i1 : FiniteTemplate HasSnaky 3 required_612_i1 envelope_612_i1 := by
  refine finite_compose HasSnaky 2 childrenC_612_i1 childrenD_612_i1 finite_children_work_612_i1 (1, 2)
    required_612_i1 envelope_612_i1 pivot_mem_612_i1 child_required_sub_612_i1 child_envelope_sub_612_i1 ?_
  intro b hb
  exact common_sub_612_i1 (mem_commonEnvelope childrenD_612_i1 b hb)

theorem finite_children_work_612_i2 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_612_i2 j) (childrenD_612_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_3 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_612_i2 : FiniteTemplate HasSnaky 2 required_612_i2 envelope_612_i2 := by
  refine finite_compose HasSnaky 1 childrenC_612_i2 childrenD_612_i2 finite_children_work_612_i2 (0, 2)
    required_612_i2 envelope_612_i2 pivot_mem_612_i2 child_required_sub_612_i2 child_envelope_sub_612_i2 ?_
  intro b hb
  exact common_sub_612_i2 (mem_commonEnvelope childrenD_612_i2 b hb)

theorem finite_children_work_612_i3 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_612_i3 j) (childrenD_612_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_612_i3 : FiniteTemplate HasSnaky 3 required_612_i3 envelope_612_i3 := by
  refine finite_compose HasSnaky 2 childrenC_612_i3 childrenD_612_i3 finite_children_work_612_i3 (1, 2)
    required_612_i3 envelope_612_i3 pivot_mem_612_i3 child_required_sub_612_i3 child_envelope_sub_612_i3 ?_
  intro b hb
  exact common_sub_612_i3 (mem_commonEnvelope childrenD_612_i3 b hb)

theorem finite_children_work_612_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_612_i0 j) (childrenD_612_i0 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_612_i1.mono (by decide +kernel)
  · exact finite_row_works_612_i2.mono (by decide +kernel)
  · exact finite_row_works_612_i3.mono (by decide +kernel)

theorem finite_row_works_612_i0 : FiniteTemplate HasSnaky 4 required_612_i0 envelope_612_i0 := by
  refine finite_compose HasSnaky 3 childrenC_612_i0 childrenD_612_i0 finite_children_work_612_i0 (1, 5)
    required_612_i0 envelope_612_i0 pivot_mem_612_i0 child_required_sub_612_i0 child_envelope_sub_612_i0 ?_
  intro b hb
  exact common_sub_612_i0 (mem_commonEnvelope childrenD_612_i0 b hb)

theorem finite_children_work_612 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_612 j) (childrenD_612 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_36 6 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_50.mono (by decide +kernel)
  · exact finite_row_works_54.mono (by decide +kernel)
  · exact finite_row_works_612_i0.mono (by decide +kernel)

theorem finite_row_works_612 : FiniteTemplate HasSnaky 5 required_612 envelope_612 := by
  refine finite_compose HasSnaky 4 childrenC_612 childrenD_612 finite_children_work_612 (1, 4)
    required_612 envelope_612 pivot_mem_612 child_required_sub_612 child_envelope_sub_612 ?_
  intro b hb
  exact common_sub_612 (mem_commonEnvelope childrenD_612 b hb)

theorem finite_children_work_672_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_672_i0 j) (childrenD_672_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_22 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_672_i0 : FiniteTemplate HasSnaky 3 required_672_i0 envelope_672_i0 := by
  refine finite_compose HasSnaky 2 childrenC_672_i0 childrenD_672_i0 finite_children_work_672_i0 (2, 1)
    required_672_i0 envelope_672_i0 pivot_mem_672_i0 child_required_sub_672_i0 child_envelope_sub_672_i0 ?_
  intro b hb
  exact common_sub_672_i0 (mem_commonEnvelope childrenD_672_i0 b hb)

theorem finite_children_work_672 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_672 j) (childrenD_672 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 3 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_305 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_672_i0.mono (by decide +kernel)

theorem finite_row_works_672 : FiniteTemplate HasSnaky 5 required_672 envelope_672 := by
  refine finite_compose HasSnaky 4 childrenC_672 childrenD_672 finite_children_work_672 (2, 2)
    required_672 envelope_672 pivot_mem_672 child_required_sub_672 child_envelope_sub_672 ?_
  intro b hb
  exact common_sub_672 (mem_commonEnvelope childrenD_672 b hb)

end FiniteCongruenceChecks.SnakyFinite
