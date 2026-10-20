/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part04
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height10Part06
import FiniteCards.Height11Part01
import FiniteCards.Height12Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_675_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_675_i0 j) (childrenD_675_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_356 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_364 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_367 2 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_671 6 (8, 9)).mono (by decide +kernel)

theorem finite_row_works_675_i0 : FiniteTemplate HasSnaky 8 required_675_i0 envelope_675_i0 := by
  refine finite_compose HasSnaky 7 childrenC_675_i0 childrenD_675_i0 finite_children_work_675_i0 (7, 7)
    required_675_i0 envelope_675_i0 pivot_mem_675_i0 child_required_sub_675_i0 child_envelope_sub_675_i0 ?_
  intro b hb
  exact common_sub_675_i0 (mem_commonEnvelope childrenD_675_i0 b hb)

theorem finite_children_work_675_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_675_i1 j) (childrenD_675_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 0 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_190 6 (9, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_441 2 (8, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_442 2 (8, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_514 6 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_667 0 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_675_i1 : FiniteTemplate HasSnaky 10 required_675_i1 envelope_675_i1 := by
  refine finite_compose HasSnaky 9 childrenC_675_i1 childrenD_675_i1 finite_children_work_675_i1 (7, 4)
    required_675_i1 envelope_675_i1 pivot_mem_675_i1 child_required_sub_675_i1 child_envelope_sub_675_i1 ?_
  intro b hb
  exact common_sub_675_i1 (mem_commonEnvelope childrenD_675_i1 b hb)

theorem finite_children_work_675_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_675_i3 j) (childrenD_675_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 3 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 1 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_186 0 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_187 4 (7, 8)).mono (by decide +kernel)

theorem finite_row_works_675_i3 : FiniteTemplate HasSnaky 6 required_675_i3 envelope_675_i3 := by
  refine finite_compose HasSnaky 5 childrenC_675_i3 childrenD_675_i3 finite_children_work_675_i3 (7, 4)
    required_675_i3 envelope_675_i3 pivot_mem_675_i3 child_required_sub_675_i3 child_envelope_sub_675_i3 ?_
  intro b hb
  exact common_sub_675_i3 (mem_commonEnvelope childrenD_675_i3 b hb)

theorem finite_children_work_675_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_675_i5 j) (childrenD_675_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_179 5 (9, 2)).mono (by decide +kernel)

theorem finite_row_works_675_i5 : FiniteTemplate HasSnaky 6 required_675_i5 envelope_675_i5 := by
  refine finite_compose HasSnaky 5 childrenC_675_i5 childrenD_675_i5 finite_children_work_675_i5 (7, 4)
    required_675_i5 envelope_675_i5 pivot_mem_675_i5 child_required_sub_675_i5 child_envelope_sub_675_i5 ?_
  intro b hb
  exact common_sub_675_i5 (mem_commonEnvelope childrenD_675_i5 b hb)

theorem finite_children_work_675_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_675_i6 j) (childrenD_675_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 7 (8, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_34 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_305 7 (8, 6)).mono (by decide +kernel)

theorem finite_row_works_675_i6 : FiniteTemplate HasSnaky 5 required_675_i6 envelope_675_i6 := by
  refine finite_compose HasSnaky 4 childrenC_675_i6 childrenD_675_i6 finite_children_work_675_i6 (6, 5)
    required_675_i6 envelope_675_i6 pivot_mem_675_i6 child_required_sub_675_i6 child_envelope_sub_675_i6 ?_
  intro b hb
  exact common_sub_675_i6 (mem_commonEnvelope childrenD_675_i6 b hb)

theorem finite_children_work_675_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_675_i4 j) (childrenD_675_i4 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_675_i5.mono (by decide +kernel)
  · exact finite_row_works_675_i6.mono (by decide +kernel)

theorem finite_row_works_675_i4 : FiniteTemplate HasSnaky 7 required_675_i4 envelope_675_i4 := by
  refine finite_compose HasSnaky 6 childrenC_675_i4 childrenD_675_i4 finite_children_work_675_i4 (6, 6)
    required_675_i4 envelope_675_i4 pivot_mem_675_i4 child_required_sub_675_i4 child_envelope_sub_675_i4 ?_
  intro b hb
  exact common_sub_675_i4 (mem_commonEnvelope childrenD_675_i4 b hb)

theorem finite_children_work_675_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_675_i2 j) (childrenD_675_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_304 4 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_672 6 (8, 7)).mono (by decide +kernel)
  · exact finite_row_works_675_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_674 3 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_675_i4.mono (by decide +kernel)

theorem finite_row_works_675_i2 : FiniteTemplate HasSnaky 11 required_675_i2 envelope_675_i2 := by
  refine finite_compose HasSnaky 10 childrenC_675_i2 childrenD_675_i2 finite_children_work_675_i2 (7, 3)
    required_675_i2 envelope_675_i2 pivot_mem_675_i2 child_required_sub_675_i2 child_envelope_sub_675_i2 ?_
  intro b hb
  exact common_sub_675_i2 (mem_commonEnvelope childrenD_675_i2 b hb)

theorem finite_children_work_675_i7 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_675_i7 j) (childrenD_675_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_190 0 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_190 2 (9, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_363 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_671 6 (8, 9)).mono (by decide +kernel)

theorem finite_row_works_675_i7 : FiniteTemplate HasSnaky 8 required_675_i7 envelope_675_i7 := by
  refine finite_compose HasSnaky 7 childrenC_675_i7 childrenD_675_i7 finite_children_work_675_i7 (7, 7)
    required_675_i7 envelope_675_i7 pivot_mem_675_i7 child_required_sub_675_i7 child_envelope_sub_675_i7 ?_
  intro b hb
  exact common_sub_675_i7 (mem_commonEnvelope childrenD_675_i7 b hb)

theorem finite_children_work_675_i8 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_675_i8 j) (childrenD_675_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_97 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_535 4 (5, 10)).mono (by decide +kernel)

theorem finite_row_works_675_i8 : FiniteTemplate HasSnaky 11 required_675_i8 envelope_675_i8 := by
  refine finite_compose HasSnaky 10 childrenC_675_i8 childrenD_675_i8 finite_children_work_675_i8 (6, 5)
    required_675_i8 envelope_675_i8 pivot_mem_675_i8 child_required_sub_675_i8 child_envelope_sub_675_i8 ?_
  intro b hb
  exact common_sub_675_i8 (mem_commonEnvelope childrenD_675_i8 b hb)

theorem finite_children_work_675_i10 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_675_i10 j) (childrenD_675_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_321 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_354 5 (8, 3)).mono (by decide +kernel)

theorem finite_row_works_675_i10 : FiniteTemplate HasSnaky 9 required_675_i10 envelope_675_i10 := by
  refine finite_compose HasSnaky 8 childrenC_675_i10 childrenD_675_i10 finite_children_work_675_i10 (7, 4)
    required_675_i10 envelope_675_i10 pivot_mem_675_i10 child_required_sub_675_i10 child_envelope_sub_675_i10 ?_
  intro b hb
  exact common_sub_675_i10 (mem_commonEnvelope childrenD_675_i10 b hb)

theorem finite_children_work_675_i9 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_675_i9 j) (childrenD_675_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_328 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_330 3 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_384 4 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_672 6 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_674 3 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_675_i10.mono (by decide +kernel)

theorem finite_row_works_675_i9 : FiniteTemplate HasSnaky 11 required_675_i9 envelope_675_i9 := by
  refine finite_compose HasSnaky 10 childrenC_675_i9 childrenD_675_i9 finite_children_work_675_i9 (7, 3)
    required_675_i9 envelope_675_i9 pivot_mem_675_i9 child_required_sub_675_i9 child_envelope_sub_675_i9 ?_
  intro b hb
  exact common_sub_675_i9 (mem_commonEnvelope childrenD_675_i9 b hb)

theorem finite_children_work_675 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_675 j) (childrenD_675 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 0 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_618 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_629 2 (10, 2)).mono (by decide +kernel)
  · exact finite_row_works_675_i0.mono (by decide +kernel)
  · exact finite_row_works_675_i1.mono (by decide +kernel)
  · exact finite_row_works_675_i2.mono (by decide +kernel)
  · exact finite_row_works_675_i7.mono (by decide +kernel)
  · exact finite_row_works_675_i8.mono (by decide +kernel)
  · exact finite_row_works_675_i9.mono (by decide +kernel)

theorem finite_row_works_675 : FiniteTemplate HasSnaky 13 required_675 envelope_675 := by
  refine finite_compose HasSnaky 12 childrenC_675 childrenD_675 finite_children_work_675 (7, 6)
    required_675 envelope_675 pivot_mem_675 child_required_sub_675 child_envelope_sub_675 ?_
  intro b hb
  exact common_sub_675 (mem_commonEnvelope childrenD_675 b hb)

theorem finite_children_work_690_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_690_i0 j) (childrenD_690_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_80 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_463 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_690_i0 : FiniteTemplate HasSnaky 12 required_690_i0 envelope_690_i0 := by
  refine finite_compose HasSnaky 11 childrenC_690_i0 childrenD_690_i0 finite_children_work_690_i0 (3, 6)
    required_690_i0 envelope_690_i0 pivot_mem_690_i0 child_required_sub_690_i0 child_envelope_sub_690_i0 ?_
  intro b hb
  exact common_sub_690_i0 (mem_commonEnvelope childrenD_690_i0 b hb)

theorem finite_children_work_690 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_690 j) (childrenD_690 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_56 6 (5, 6)).mono (by decide +kernel)
  · exact finite_row_works_690_i0.mono (by decide +kernel)

theorem finite_row_works_690 : FiniteTemplate HasSnaky 13 required_690 envelope_690 := by
  refine finite_compose HasSnaky 12 childrenC_690 childrenD_690 finite_children_work_690 (3, 4)
    required_690 envelope_690 pivot_mem_690 child_required_sub_690 child_envelope_sub_690 ?_
  intro b hb
  exact common_sub_690 (mem_commonEnvelope childrenD_690 b hb)

theorem finite_children_work_692_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_692_i1 j) (childrenD_692_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_118 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_193 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_396 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 7 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_692_i1 : FiniteTemplate HasSnaky 10 required_692_i1 envelope_692_i1 := by
  refine finite_compose HasSnaky 9 childrenC_692_i1 childrenD_692_i1 finite_children_work_692_i1 (3, 3)
    required_692_i1 envelope_692_i1 pivot_mem_692_i1 child_required_sub_692_i1 child_envelope_sub_692_i1 ?_
  intro b hb
  exact common_sub_692_i1 (mem_commonEnvelope childrenD_692_i1 b hb)

theorem finite_children_work_692_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_692_i2 j) (childrenD_692_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_509 4 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_692_i2 : FiniteTemplate HasSnaky 11 required_692_i2 envelope_692_i2 := by
  refine finite_compose HasSnaky 10 childrenC_692_i2 childrenD_692_i2 finite_children_work_692_i2 (4, 4)
    required_692_i2 envelope_692_i2 pivot_mem_692_i2 child_required_sub_692_i2 child_envelope_sub_692_i2 ?_
  intro b hb
  exact common_sub_692_i2 (mem_commonEnvelope childrenD_692_i2 b hb)

theorem finite_children_work_692_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_692_i0 j) (childrenD_692_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_110 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_119 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_399 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_430 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_461 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 4 (1, 8)).mono (by decide +kernel)
  · exact finite_row_works_692_i1.mono (by decide +kernel)
  · exact finite_row_works_692_i2.mono (by decide +kernel)

theorem finite_row_works_692_i0 : FiniteTemplate HasSnaky 12 required_692_i0 envelope_692_i0 := by
  refine finite_compose HasSnaky 11 childrenC_692_i0 childrenD_692_i0 finite_children_work_692_i0 (3, 4)
    required_692_i0 envelope_692_i0 pivot_mem_692_i0 child_required_sub_692_i0 child_envelope_sub_692_i0 ?_
  intro b hb
  exact common_sub_692_i0 (mem_commonEnvelope childrenD_692_i0 b hb)

theorem finite_children_work_692 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_692 j) (childrenD_692 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_692_i0.mono (by decide +kernel)

theorem finite_row_works_692 : FiniteTemplate HasSnaky 13 required_692 envelope_692 := by
  refine finite_compose HasSnaky 12 childrenC_692 childrenD_692 finite_children_work_692 (1, 5)
    required_692 envelope_692 pivot_mem_692 child_required_sub_692 child_envelope_sub_692 ?_
  intro b hb
  exact common_sub_692 (mem_commonEnvelope childrenD_692 b hb)

end FiniteCongruenceChecks.SnakyFinite
