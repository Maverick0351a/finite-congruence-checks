/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height13Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part05
import FiniteCards.Height05Part03
import FiniteCards.Height05Part06
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height07Part03
import FiniteCards.Height07Part04
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height10Part03
import FiniteCards.Height11Part02
import FiniteCards.Height12Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_564_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_564_i2 j) (childrenD_564_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_453 2 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_564_i2 : FiniteTemplate HasSnaky 8 required_564_i2 envelope_564_i2 := by
  refine finite_compose HasSnaky 7 childrenC_564_i2 childrenD_564_i2 finite_children_work_564_i2 (2, 4)
    required_564_i2 envelope_564_i2 pivot_mem_564_i2 child_required_sub_564_i2 child_envelope_sub_564_i2 ?_
  intro b hb
  exact common_sub_564_i2 (mem_commonEnvelope childrenD_564_i2 b hb)

theorem finite_children_work_564_i7 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_564_i7 j) (childrenD_564_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_564_i7 : FiniteTemplate HasSnaky 5 required_564_i7 envelope_564_i7 := by
  refine finite_compose HasSnaky 4 childrenC_564_i7 childrenD_564_i7 finite_children_work_564_i7 (3, 5)
    required_564_i7 envelope_564_i7 pivot_mem_564_i7 child_required_sub_564_i7 child_envelope_sub_564_i7 ?_
  intro b hb
  exact common_sub_564_i7 (mem_commonEnvelope childrenD_564_i7 b hb)

theorem finite_children_work_564_i8 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_564_i8 j) (childrenD_564_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_342 2 (5, 2)).mono (by decide +kernel)

theorem finite_row_works_564_i8 : FiniteTemplate HasSnaky 6 required_564_i8 envelope_564_i8 := by
  refine finite_compose HasSnaky 5 childrenC_564_i8 childrenD_564_i8 finite_children_work_564_i8 (2, 4)
    required_564_i8 envelope_564_i8 pivot_mem_564_i8 child_required_sub_564_i8 child_envelope_sub_564_i8 ?_
  intro b hb
  exact common_sub_564_i8 (mem_commonEnvelope childrenD_564_i8 b hb)

theorem finite_children_work_564_i6 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_564_i6 j) (childrenD_564_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_102 5 (6, 4)).mono (by decide +kernel)
  · exact finite_row_works_564_i7.mono (by decide +kernel)
  · exact finite_row_works_564_i8.mono (by decide +kernel)

theorem finite_row_works_564_i6 : FiniteTemplate HasSnaky 7 required_564_i6 envelope_564_i6 := by
  refine finite_compose HasSnaky 6 childrenC_564_i6 childrenD_564_i6 finite_children_work_564_i6 (2, 5)
    required_564_i6 envelope_564_i6 pivot_mem_564_i6 child_required_sub_564_i6 child_envelope_sub_564_i6 ?_
  intro b hb
  exact common_sub_564_i6 (mem_commonEnvelope childrenD_564_i6 b hb)

theorem finite_children_work_564_i5 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_564_i5 j) (childrenD_564_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (5, 8)).mono (by decide +kernel)
  · exact finite_row_works_564_i6.mono (by decide +kernel)

theorem finite_row_works_564_i5 : FiniteTemplate HasSnaky 8 required_564_i5 envelope_564_i5 := by
  refine finite_compose HasSnaky 7 childrenC_564_i5 childrenD_564_i5 finite_children_work_564_i5 (4, 5)
    required_564_i5 envelope_564_i5 pivot_mem_564_i5 child_required_sub_564_i5 child_envelope_sub_564_i5 ?_
  intro b hb
  exact common_sub_564_i5 (mem_commonEnvelope childrenD_564_i5 b hb)

theorem finite_children_work_564_i4 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_564_i4 j) (childrenD_564_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_16 2 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_235 6 (6, 8)).mono (by decide +kernel)
  · exact finite_row_works_564_i5.mono (by decide +kernel)

theorem finite_row_works_564_i4 : FiniteTemplate HasSnaky 9 required_564_i4 envelope_564_i4 := by
  refine finite_compose HasSnaky 8 childrenC_564_i4 childrenD_564_i4 finite_children_work_564_i4 (5, 7)
    required_564_i4 envelope_564_i4 pivot_mem_564_i4 child_required_sub_564_i4 child_envelope_sub_564_i4 ?_
  intro b hb
  exact common_sub_564_i4 (mem_commonEnvelope childrenD_564_i4 b hb)

theorem finite_children_work_564_i3 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_564_i3 j) (childrenD_564_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_67 2 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 5 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_327 7 (9, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_504 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 5 (7, 4)).mono (by decide +kernel)
  · exact finite_row_works_564_i4.mono (by decide +kernel)

theorem finite_row_works_564_i3 : FiniteTemplate HasSnaky 10 required_564_i3 envelope_564_i3 := by
  refine finite_compose HasSnaky 9 childrenC_564_i3 childrenD_564_i3 finite_children_work_564_i3 (5, 6)
    required_564_i3 envelope_564_i3 pivot_mem_564_i3 child_required_sub_564_i3 child_envelope_sub_564_i3 ?_
  intro b hb
  exact common_sub_564_i3 (mem_commonEnvelope childrenD_564_i3 b hb)

theorem finite_children_work_564_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_564_i1 j) (childrenD_564_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (2, 4)).mono (by decide +kernel)
  · exact finite_row_works_564_i2.mono (by decide +kernel)
  · exact finite_row_works_564_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_560 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_563 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_564_i1 : FiniteTemplate HasSnaky 11 required_564_i1 envelope_564_i1 := by
  refine finite_compose HasSnaky 10 childrenC_564_i1 childrenD_564_i1 finite_children_work_564_i1 (5, 5)
    required_564_i1 envelope_564_i1 pivot_mem_564_i1 child_required_sub_564_i1 child_envelope_sub_564_i1 ?_
  intro b hb
  exact common_sub_564_i1 (mem_commonEnvelope childrenD_564_i1 b hb)

theorem finite_children_work_564_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_564_i0 j) (childrenD_564_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_12 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_79 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_135 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_182 3 (1, 6)).mono (by decide +kernel)
  · exact finite_row_works_564_i1.mono (by decide +kernel)

theorem finite_row_works_564_i0 : FiniteTemplate HasSnaky 12 required_564_i0 envelope_564_i0 := by
  refine finite_compose HasSnaky 11 childrenC_564_i0 childrenD_564_i0 finite_children_work_564_i0 (5, 4)
    required_564_i0 envelope_564_i0 pivot_mem_564_i0 child_required_sub_564_i0 child_envelope_sub_564_i0 ?_
  intro b hb
  exact common_sub_564_i0 (mem_commonEnvelope childrenD_564_i0 b hb)

theorem finite_children_work_564 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_564 j) (childrenD_564 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_119 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_497 2 (4, 0)).mono (by decide +kernel)
  · exact finite_row_works_498.mono (by decide +kernel)
  · exact finite_row_works_564_i0.mono (by decide +kernel)

theorem finite_row_works_564 : FiniteTemplate HasSnaky 13 required_564 envelope_564 := by
  refine finite_compose HasSnaky 12 childrenC_564 childrenD_564 finite_children_work_564 (4, 4)
    required_564 envelope_564 pivot_mem_564 child_required_sub_564 child_envelope_sub_564 ?_
  intro b hb
  exact common_sub_564 (mem_commonEnvelope childrenD_564 b hb)

theorem finite_children_work_568_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_568_i0 j) (childrenD_568_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_255 5 (7, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_496 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_568_i0 : FiniteTemplate HasSnaky 7 required_568_i0 envelope_568_i0 := by
  refine finite_compose HasSnaky 6 childrenC_568_i0 childrenD_568_i0 finite_children_work_568_i0 (4, 3)
    required_568_i0 envelope_568_i0 pivot_mem_568_i0 child_required_sub_568_i0 child_envelope_sub_568_i0 ?_
  intro b hb
  exact common_sub_568_i0 (mem_commonEnvelope childrenD_568_i0 b hb)

theorem finite_children_work_568_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_568_i3 j) (childrenD_568_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_24 4 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_77 3 (2, 5)).mono (by decide +kernel)

theorem finite_row_works_568_i3 : FiniteTemplate HasSnaky 4 required_568_i3 envelope_568_i3 := by
  refine finite_compose HasSnaky 3 childrenC_568_i3 childrenD_568_i3 finite_children_work_568_i3 (6, 4)
    required_568_i3 envelope_568_i3 pivot_mem_568_i3 child_required_sub_568_i3 child_envelope_sub_568_i3 ?_
  intro b hb
  exact common_sub_568_i3 (mem_commonEnvelope childrenD_568_i3 b hb)

theorem finite_children_work_568_i6 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_568_i6 j) (childrenD_568_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_132 5 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_568_i6 : FiniteTemplate HasSnaky 5 required_568_i6 envelope_568_i6 := by
  refine finite_compose HasSnaky 4 childrenC_568_i6 childrenD_568_i6 finite_children_work_568_i6 (3, 7)
    required_568_i6 envelope_568_i6 pivot_mem_568_i6 child_required_sub_568_i6 child_envelope_sub_568_i6 ?_
  intro b hb
  exact common_sub_568_i6 (mem_commonEnvelope childrenD_568_i6 b hb)

theorem finite_children_work_568_i7 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_568_i7 j) (childrenD_568_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 2 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_124 2 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_568_i7 : FiniteTemplate HasSnaky 4 required_568_i7 envelope_568_i7 := by
  refine finite_compose HasSnaky 3 childrenC_568_i7 childrenD_568_i7 finite_children_work_568_i7 (3, 7)
    required_568_i7 envelope_568_i7 pivot_mem_568_i7 child_required_sub_568_i7 child_envelope_sub_568_i7 ?_
  intro b hb
  exact common_sub_568_i7 (mem_commonEnvelope childrenD_568_i7 b hb)

theorem finite_children_work_568_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_568_i5 j) (childrenD_568_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 5 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_387 2 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_568_i6.mono (by decide +kernel)
  · exact finite_row_works_568_i7.mono (by decide +kernel)

theorem finite_row_works_568_i5 : FiniteTemplate HasSnaky 7 required_568_i5 envelope_568_i5 := by
  refine finite_compose HasSnaky 6 childrenC_568_i5 childrenD_568_i5 finite_children_work_568_i5 (3, 6)
    required_568_i5 envelope_568_i5 pivot_mem_568_i5 child_required_sub_568_i5 child_envelope_sub_568_i5 ?_
  intro b hb
  exact common_sub_568_i5 (mem_commonEnvelope childrenD_568_i5 b hb)

theorem finite_children_work_568_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_568_i4 j) (childrenD_568_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 3 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_568_i5.mono (by decide +kernel)

theorem finite_row_works_568_i4 : FiniteTemplate HasSnaky 8 required_568_i4 envelope_568_i4 := by
  refine finite_compose HasSnaky 7 childrenC_568_i4 childrenD_568_i4 finite_children_work_568_i4 (3, 3)
    required_568_i4 envelope_568_i4 pivot_mem_568_i4 child_required_sub_568_i4 child_envelope_sub_568_i4 ?_
  intro b hb
  exact common_sub_568_i4 (mem_commonEnvelope childrenD_568_i4 b hb)

theorem finite_children_work_568_i2 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_568_i2 j) (childrenD_568_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 5 (6, 4)).mono (by decide +kernel)
  · exact finite_row_works_568_i3.mono (by decide +kernel)
  · exact finite_row_works_568_i4.mono (by decide +kernel)

theorem finite_row_works_568_i2 : FiniteTemplate HasSnaky 9 required_568_i2 envelope_568_i2 := by
  refine finite_compose HasSnaky 8 childrenC_568_i2 childrenD_568_i2 finite_children_work_568_i2 (3, 5)
    required_568_i2 envelope_568_i2 pivot_mem_568_i2 child_required_sub_568_i2 child_envelope_sub_568_i2 ?_
  intro b hb
  exact common_sub_568_i2 (mem_commonEnvelope childrenD_568_i2 b hb)

theorem finite_children_work_568_i1 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_568_i1 j) (childrenD_568_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_79 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_189 3 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_518 3 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_568_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_565 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_567 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_568_i1 : FiniteTemplate HasSnaky 12 required_568_i1 envelope_568_i1 := by
  refine finite_compose HasSnaky 11 childrenC_568_i1 childrenD_568_i1 finite_children_work_568_i1 (5, 4)
    required_568_i1 envelope_568_i1 pivot_mem_568_i1 child_required_sub_568_i1 child_envelope_sub_568_i1 ?_
  intro b hb
  exact common_sub_568_i1 (mem_commonEnvelope childrenD_568_i1 b hb)

theorem finite_children_work_568 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_568 j) (childrenD_568 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_110 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_497 2 (4, 0)).mono (by decide +kernel)
  · exact finite_row_works_568_i0.mono (by decide +kernel)
  · exact finite_row_works_568_i1.mono (by decide +kernel)

theorem finite_row_works_568 : FiniteTemplate HasSnaky 13 required_568 envelope_568 := by
  refine finite_compose HasSnaky 12 childrenC_568 childrenD_568 finite_children_work_568 (4, 4)
    required_568 envelope_568 pivot_mem_568 child_required_sub_568 child_envelope_sub_568 ?_
  intro b hb
  exact common_sub_568 (mem_commonEnvelope childrenD_568 b hb)

theorem finite_children_work_572_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_572_i0 j) (childrenD_572_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 4 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_572_i0 : FiniteTemplate HasSnaky 4 required_572_i0 envelope_572_i0 := by
  refine finite_compose HasSnaky 3 childrenC_572_i0 childrenD_572_i0 finite_children_work_572_i0 (2, 6)
    required_572_i0 envelope_572_i0 pivot_mem_572_i0 child_required_sub_572_i0 child_envelope_sub_572_i0 ?_
  intro b hb
  exact common_sub_572_i0 (mem_commonEnvelope childrenD_572_i0 b hb)

theorem finite_children_work_572 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_572 j) (childrenD_572 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_97 3 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_98 1 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_572_i0.mono (by decide +kernel)
  · exact finite_row_works_571.mono (by decide +kernel)

theorem finite_row_works_572 : FiniteTemplate HasSnaky 13 required_572 envelope_572 := by
  refine finite_compose HasSnaky 12 childrenC_572 childrenD_572 finite_children_work_572 (4, 6)
    required_572 envelope_572 pivot_mem_572 child_required_sub_572 child_envelope_sub_572 ?_
  intro b hb
  exact common_sub_572 (mem_commonEnvelope childrenD_572 b hb)

theorem finite_children_work_590 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_590 j) (childrenD_590 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_588.mono (by decide +kernel)

theorem finite_row_works_590 : FiniteTemplate HasSnaky 13 required_590 envelope_590 := by
  refine finite_compose HasSnaky 12 childrenC_590 childrenD_590 finite_children_work_590 (2, 3)
    required_590 envelope_590 pivot_mem_590 child_required_sub_590 child_envelope_sub_590 ?_
  intro b hb
  exact common_sub_590 (mem_commonEnvelope childrenD_590 b hb)

end FiniteCongruenceChecks.SnakyFinite
