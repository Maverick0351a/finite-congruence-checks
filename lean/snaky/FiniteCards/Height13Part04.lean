/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part04
import FiniteCards.Height07Part03
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height10Part05
import FiniteCards.Height11Part02
import FiniteCards.Height11Part05
import FiniteCards.Height12Part02
import FiniteCards.Height12Part04

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_650_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_650_i0 j) (childrenD_650_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 2 (6, 0)).mono (by decide +kernel)

theorem finite_row_works_650_i0 : FiniteTemplate HasSnaky 11 required_650_i0 envelope_650_i0 := by
  refine finite_compose HasSnaky 10 childrenC_650_i0 childrenD_650_i0 finite_children_work_650_i0 (5, 4)
    required_650_i0 envelope_650_i0 pivot_mem_650_i0 child_required_sub_650_i0 child_envelope_sub_650_i0 ?_
  intro b hb
  exact common_sub_650_i0 (mem_commonEnvelope childrenD_650_i0 b hb)

theorem finite_children_work_650 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_650 j) (childrenD_650 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_257 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_649 4 (1, 10)).mono (by decide +kernel)
  · exact finite_row_works_650_i0.mono (by decide +kernel)

theorem finite_row_works_650 : FiniteTemplate HasSnaky 13 required_650 envelope_650 := by
  refine finite_compose HasSnaky 12 childrenC_650 childrenD_650 finite_children_work_650 (5, 5)
    required_650 envelope_650 pivot_mem_650 child_required_sub_650 child_envelope_sub_650 ?_
  intro b hb
  exact common_sub_650 (mem_commonEnvelope childrenD_650 b hb)

theorem finite_children_work_657_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_657_i1 j) (childrenD_657_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 2 (5, 1)).mono (by decide +kernel)

theorem finite_row_works_657_i1 : FiniteTemplate HasSnaky 5 required_657_i1 envelope_657_i1 := by
  refine finite_compose HasSnaky 4 childrenC_657_i1 childrenD_657_i1 finite_children_work_657_i1 (2, 4)
    required_657_i1 envelope_657_i1 pivot_mem_657_i1 child_required_sub_657_i1 child_envelope_sub_657_i1 ?_
  intro b hb
  exact common_sub_657_i1 (mem_commonEnvelope childrenD_657_i1 b hb)

theorem finite_children_work_657_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_657_i2 j) (childrenD_657_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_71 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_345 1 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_657_i2 : FiniteTemplate HasSnaky 9 required_657_i2 envelope_657_i2 := by
  refine finite_compose HasSnaky 8 childrenC_657_i2 childrenD_657_i2 finite_children_work_657_i2 (4, 2)
    required_657_i2 envelope_657_i2 pivot_mem_657_i2 child_required_sub_657_i2 child_envelope_sub_657_i2 ?_
  intro b hb
  exact common_sub_657_i2 (mem_commonEnvelope childrenD_657_i2 b hb)

theorem finite_children_work_657_i6 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_657_i6 j) (childrenD_657_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_445 4 (3, 5)).mono (by decide +kernel)

theorem finite_row_works_657_i6 : FiniteTemplate HasSnaky 6 required_657_i6 envelope_657_i6 := by
  refine finite_compose HasSnaky 5 childrenC_657_i6 childrenD_657_i6 finite_children_work_657_i6 (6, 3)
    required_657_i6 envelope_657_i6 pivot_mem_657_i6 child_required_sub_657_i6 child_envelope_sub_657_i6 ?_
  intro b hb
  exact common_sub_657_i6 (mem_commonEnvelope childrenD_657_i6 b hb)

theorem finite_children_work_657_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_657_i5 j) (childrenD_657_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 3 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_657_i6.mono (by decide +kernel)

theorem finite_row_works_657_i5 : FiniteTemplate HasSnaky 7 required_657_i5 envelope_657_i5 := by
  refine finite_compose HasSnaky 6 childrenC_657_i5 childrenD_657_i5 finite_children_work_657_i5 (6, 4)
    required_657_i5 envelope_657_i5 pivot_mem_657_i5 child_required_sub_657_i5 child_envelope_sub_657_i5 ?_
  intro b hb
  exact common_sub_657_i5 (mem_commonEnvelope childrenD_657_i5 b hb)

theorem finite_children_work_657_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_657_i4 j) (childrenD_657_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_65 1 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_657_i5.mono (by decide +kernel)

theorem finite_row_works_657_i4 : FiniteTemplate HasSnaky 8 required_657_i4 envelope_657_i4 := by
  refine finite_compose HasSnaky 7 childrenC_657_i4 childrenD_657_i4 finite_children_work_657_i4 (3, 4)
    required_657_i4 envelope_657_i4 pivot_mem_657_i4 child_required_sub_657_i4 child_envelope_sub_657_i4 ?_
  intro b hb
  exact common_sub_657_i4 (mem_commonEnvelope childrenD_657_i4 b hb)

theorem finite_children_work_657_i3 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_657_i3 j) (childrenD_657_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_85 5 (8, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_85 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_411 4 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_537 5 (8, 2)).mono (by decide +kernel)
  · exact finite_row_works_657_i4.mono (by decide +kernel)

theorem finite_row_works_657_i3 : FiniteTemplate HasSnaky 11 required_657_i3 envelope_657_i3 := by
  refine finite_compose HasSnaky 10 childrenC_657_i3 childrenD_657_i3 finite_children_work_657_i3 (5, 4)
    required_657_i3 envelope_657_i3 pivot_mem_657_i3 child_required_sub_657_i3 child_envelope_sub_657_i3 ?_
  intro b hb
  exact common_sub_657_i3 (mem_commonEnvelope childrenD_657_i3 b hb)

theorem finite_children_work_657_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_657_i0 j) (childrenD_657_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_510 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_631 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_653 1 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_657_i1.mono (by decide +kernel)
  · exact finite_row_works_657_i2.mono (by decide +kernel)
  · exact finite_row_works_657_i3.mono (by decide +kernel)

theorem finite_row_works_657_i0 : FiniteTemplate HasSnaky 12 required_657_i0 envelope_657_i0 := by
  refine finite_compose HasSnaky 11 childrenC_657_i0 childrenD_657_i0 finite_children_work_657_i0 (4, 4)
    required_657_i0 envelope_657_i0 pivot_mem_657_i0 child_required_sub_657_i0 child_envelope_sub_657_i0 ?_
  intro b hb
  exact common_sub_657_i0 (mem_commonEnvelope childrenD_657_i0 b hb)

theorem finite_children_work_657 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_657 j) (childrenD_657 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_478 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_482 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_657_i0.mono (by decide +kernel)

theorem finite_row_works_657 : FiniteTemplate HasSnaky 13 required_657 envelope_657 := by
  refine finite_compose HasSnaky 12 childrenC_657 childrenD_657 finite_children_work_657 (4, 3)
    required_657 envelope_657 pivot_mem_657 child_required_sub_657 child_envelope_sub_657 ?_
  intro b hb
  exact common_sub_657 (mem_commonEnvelope childrenD_657 b hb)

theorem finite_children_work_665_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_665_i0 j) (childrenD_665_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_70 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_106 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_269 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 1 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_665_i0 : FiniteTemplate HasSnaky 10 required_665_i0 envelope_665_i0 := by
  refine finite_compose HasSnaky 9 childrenC_665_i0 childrenD_665_i0 finite_children_work_665_i0 (4, 7)
    required_665_i0 envelope_665_i0 pivot_mem_665_i0 child_required_sub_665_i0 child_envelope_sub_665_i0 ?_
  intro b hb
  exact common_sub_665_i0 (mem_commonEnvelope childrenD_665_i0 b hb)

theorem finite_children_work_665_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_665_i1 j) (childrenD_665_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_70 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_257 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (7, 4)).mono (by decide +kernel)

theorem finite_row_works_665_i1 : FiniteTemplate HasSnaky 9 required_665_i1 envelope_665_i1 := by
  refine finite_compose HasSnaky 8 childrenC_665_i1 childrenD_665_i1 finite_children_work_665_i1 (4, 7)
    required_665_i1 envelope_665_i1 pivot_mem_665_i1 child_required_sub_665_i1 child_envelope_sub_665_i1 ?_
  intro b hb
  exact common_sub_665_i1 (mem_commonEnvelope childrenD_665_i1 b hb)

theorem finite_children_work_665_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_665_i4 j) (childrenD_665_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_93 5 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_665_i4 : FiniteTemplate HasSnaky 5 required_665_i4 envelope_665_i4 := by
  refine finite_compose HasSnaky 4 childrenC_665_i4 childrenD_665_i4 finite_children_work_665_i4 (3, 7)
    required_665_i4 envelope_665_i4 pivot_mem_665_i4 child_required_sub_665_i4 child_envelope_sub_665_i4 ?_
  intro b hb
  exact common_sub_665_i4 (mem_commonEnvelope childrenD_665_i4 b hb)

theorem finite_children_work_665_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_665_i3 j) (childrenD_665_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_665_i4.mono (by decide +kernel)

theorem finite_row_works_665_i3 : FiniteTemplate HasSnaky 6 required_665_i3 envelope_665_i3 := by
  refine finite_compose HasSnaky 5 childrenC_665_i3 childrenD_665_i3 finite_children_work_665_i3 (3, 4)
    required_665_i3 envelope_665_i3 pivot_mem_665_i3 child_required_sub_665_i3 child_envelope_sub_665_i3 ?_
  intro b hb
  exact common_sub_665_i3 (mem_commonEnvelope childrenD_665_i3 b hb)

theorem finite_children_work_665_i2 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_665_i2 j) (childrenD_665_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_517 1 (0, 4)).mono (by decide +kernel)
  · exact finite_row_works_665_i3.mono (by decide +kernel)

theorem finite_row_works_665_i2 : FiniteTemplate HasSnaky 12 required_665_i2 envelope_665_i2 := by
  refine finite_compose HasSnaky 11 childrenC_665_i2 childrenD_665_i2 finite_children_work_665_i2 (3, 5)
    required_665_i2 envelope_665_i2 pivot_mem_665_i2 child_required_sub_665_i2 child_envelope_sub_665_i2 ?_
  intro b hb
  exact common_sub_665_i2 (mem_commonEnvelope childrenD_665_i2 b hb)

theorem finite_children_work_665 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_665 j) (childrenD_665 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_588 3 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_665_i0.mono (by decide +kernel)
  · exact finite_row_works_665_i1.mono (by decide +kernel)
  · exact finite_row_works_665_i2.mono (by decide +kernel)

theorem finite_row_works_665 : FiniteTemplate HasSnaky 13 required_665 envelope_665 := by
  refine finite_compose HasSnaky 12 childrenC_665 childrenD_665 finite_children_work_665 (4, 5)
    required_665 envelope_665 pivot_mem_665 child_required_sub_665 child_envelope_sub_665 ?_
  intro b hb
  exact common_sub_665 (mem_commonEnvelope childrenD_665 b hb)

end FiniteCongruenceChecks.SnakyFinite
