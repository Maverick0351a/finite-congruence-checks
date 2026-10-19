/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part08
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height04Part05
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height08Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_673_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_673_i0 j) (childrenD_673_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_74 3 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_673_i0 : FiniteTemplate HasSnaky 4 required_673_i0 envelope_673_i0 := by
  refine finite_compose HasSnaky 3 childrenC_673_i0 childrenD_673_i0 finite_children_work_673_i0 (1, 4)
    required_673_i0 envelope_673_i0 pivot_mem_673_i0 child_required_sub_673_i0 child_envelope_sub_673_i0 ?_
  intro b hb
  exact common_sub_673_i0 (mem_commonEnvelope childrenD_673_i0 b hb)

theorem finite_children_work_673_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_673_i3 j) (childrenD_673_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_260 0 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_673_i3 : FiniteTemplate HasSnaky 6 required_673_i3 envelope_673_i3 := by
  refine finite_compose HasSnaky 5 childrenC_673_i3 childrenD_673_i3 finite_children_work_673_i3 (4, 5)
    required_673_i3 envelope_673_i3 pivot_mem_673_i3 child_required_sub_673_i3 child_envelope_sub_673_i3 ?_
  intro b hb
  exact common_sub_673_i3 (mem_commonEnvelope childrenD_673_i3 b hb)

theorem finite_children_work_673_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_673_i2 j) (childrenD_673_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 2 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_673_i3.mono (by decide +kernel)

theorem finite_row_works_673_i2 : FiniteTemplate HasSnaky 7 required_673_i2 envelope_673_i2 := by
  refine finite_compose HasSnaky 6 childrenC_673_i2 childrenD_673_i2 finite_children_work_673_i2 (1, 4)
    required_673_i2 envelope_673_i2 pivot_mem_673_i2 child_required_sub_673_i2 child_envelope_sub_673_i2 ?_
  intro b hb
  exact common_sub_673_i2 (mem_commonEnvelope childrenD_673_i2 b hb)

theorem finite_children_work_673_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_673_i1 j) (childrenD_673_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_673_i2.mono (by decide +kernel)

theorem finite_row_works_673_i1 : FiniteTemplate HasSnaky 8 required_673_i1 envelope_673_i1 := by
  refine finite_compose HasSnaky 7 childrenC_673_i1 childrenD_673_i1 finite_children_work_673_i1 (3, 4)
    required_673_i1 envelope_673_i1 pivot_mem_673_i1 child_required_sub_673_i1 child_envelope_sub_673_i1 ?_
  intro b hb
  exact common_sub_673_i1 (mem_commonEnvelope childrenD_673_i1 b hb)

theorem finite_children_work_673_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_673_i4 j) (childrenD_673_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_190 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_230 7 (6, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_263 0 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_306 4 (1, 8)).mono (by decide +kernel)

theorem finite_row_works_673_i4 : FiniteTemplate HasSnaky 7 required_673_i4 envelope_673_i4 := by
  refine finite_compose HasSnaky 6 childrenC_673_i4 childrenD_673_i4 finite_children_work_673_i4 (4, 5)
    required_673_i4 envelope_673_i4 pivot_mem_673_i4 child_required_sub_673_i4 child_envelope_sub_673_i4 ?_
  intro b hb
  exact common_sub_673_i4 (mem_commonEnvelope childrenD_673_i4 b hb)

theorem finite_children_work_673_i6 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_673_i6 j) (childrenD_673_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_38 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_145 0 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_673_i6 : FiniteTemplate HasSnaky 6 required_673_i6 envelope_673_i6 := by
  refine finite_compose HasSnaky 5 childrenC_673_i6 childrenD_673_i6 finite_children_work_673_i6 (1, 4)
    required_673_i6 envelope_673_i6 pivot_mem_673_i6 child_required_sub_673_i6 child_envelope_sub_673_i6 ?_
  intro b hb
  exact common_sub_673_i6 (mem_commonEnvelope childrenD_673_i6 b hb)

theorem finite_children_work_673_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_673_i5 j) (childrenD_673_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_673_i6.mono (by decide +kernel)

theorem finite_row_works_673_i5 : FiniteTemplate HasSnaky 7 required_673_i5 envelope_673_i5 := by
  refine finite_compose HasSnaky 6 childrenC_673_i5 childrenD_673_i5 finite_children_work_673_i5 (3, 4)
    required_673_i5 envelope_673_i5 pivot_mem_673_i5 child_required_sub_673_i5 child_envelope_sub_673_i5 ?_
  intro b hb
  exact common_sub_673_i5 (mem_commonEnvelope childrenD_673_i5 b hb)

theorem finite_children_work_673_i9 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_673_i9 j) (childrenD_673_i9 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_19 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_25 7 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_673_i9 : FiniteTemplate HasSnaky 6 required_673_i9 envelope_673_i9 := by
  refine finite_compose HasSnaky 5 childrenC_673_i9 childrenD_673_i9 finite_children_work_673_i9 (4, 3)
    required_673_i9 envelope_673_i9 pivot_mem_673_i9 child_required_sub_673_i9 child_envelope_sub_673_i9 ?_
  intro b hb
  exact common_sub_673_i9 (mem_commonEnvelope childrenD_673_i9 b hb)

theorem finite_children_work_673_i10 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_673_i10 j) (childrenD_673_i10 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 0 (3, 3)).mono (by decide +kernel)

theorem finite_row_works_673_i10 : FiniteTemplate HasSnaky 5 required_673_i10 envelope_673_i10 := by
  refine finite_compose HasSnaky 4 childrenC_673_i10 childrenD_673_i10 finite_children_work_673_i10 (3, 4)
    required_673_i10 envelope_673_i10 pivot_mem_673_i10 child_required_sub_673_i10 child_envelope_sub_673_i10 ?_
  intro b hb
  exact common_sub_673_i10 (mem_commonEnvelope childrenD_673_i10 b hb)

theorem finite_children_work_673_i8 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_673_i8 j) (childrenD_673_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_263 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_271 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_424 4 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_673_i9.mono (by decide +kernel)
  · exact finite_row_works_673_i10.mono (by decide +kernel)

theorem finite_row_works_673_i8 : FiniteTemplate HasSnaky 7 required_673_i8 envelope_673_i8 := by
  refine finite_compose HasSnaky 6 childrenC_673_i8 childrenD_673_i8 finite_children_work_673_i8 (4, 5)
    required_673_i8 envelope_673_i8 pivot_mem_673_i8 child_required_sub_673_i8 child_envelope_sub_673_i8 ?_
  intro b hb
  exact common_sub_673_i8 (mem_commonEnvelope childrenD_673_i8 b hb)

theorem finite_children_work_673_i7 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_673_i7 j) (childrenD_673_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 0 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_673_i8.mono (by decide +kernel)

theorem finite_row_works_673_i7 : FiniteTemplate HasSnaky 8 required_673_i7 envelope_673_i7 := by
  refine finite_compose HasSnaky 7 childrenC_673_i7 childrenD_673_i7 finite_children_work_673_i7 (1, 4)
    required_673_i7 envelope_673_i7 pivot_mem_673_i7 child_required_sub_673_i7 child_envelope_sub_673_i7 ?_
  intro b hb
  exact common_sub_673_i7 (mem_commonEnvelope childrenD_673_i7 b hb)

theorem finite_children_work_673 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_673 j) (childrenD_673 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_673_i0.mono (by decide +kernel)
  · exact finite_row_works_673_i1.mono (by decide +kernel)
  · exact finite_row_works_673_i4.mono (by decide +kernel)
  · exact finite_row_works_673_i5.mono (by decide +kernel)
  · exact finite_row_works_673_i7.mono (by decide +kernel)

theorem finite_row_works_673 : FiniteTemplate HasSnaky 9 required_673 envelope_673 := by
  refine finite_compose HasSnaky 8 childrenC_673 childrenD_673 finite_children_work_673 (4, 4)
    required_673 envelope_673 pivot_mem_673 child_required_sub_673 child_envelope_sub_673 ?_
  intro b hb
  exact common_sub_673 (mem_commonEnvelope childrenD_673 b hb)

theorem finite_children_work_686_i0 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_686_i0 j) (childrenD_686_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_43 1 (2, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_57 5 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_340 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_686_i0 : FiniteTemplate HasSnaky 7 required_686_i0 envelope_686_i0 := by
  refine finite_compose HasSnaky 6 childrenC_686_i0 childrenD_686_i0 finite_children_work_686_i0 (5, 4)
    required_686_i0 envelope_686_i0 pivot_mem_686_i0 child_required_sub_686_i0 child_envelope_sub_686_i0 ?_
  intro b hb
  exact common_sub_686_i0 (mem_commonEnvelope childrenD_686_i0 b hb)

theorem finite_children_work_686_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_686_i1 j) (childrenD_686_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_256 5 (7, 2)).mono (by decide +kernel)

theorem finite_row_works_686_i1 : FiniteTemplate HasSnaky 8 required_686_i1 envelope_686_i1 := by
  refine finite_compose HasSnaky 7 childrenC_686_i1 childrenD_686_i1 finite_children_work_686_i1 (4, 2)
    required_686_i1 envelope_686_i1 pivot_mem_686_i1 child_required_sub_686_i1 child_envelope_sub_686_i1 ?_
  intro b hb
  exact common_sub_686_i1 (mem_commonEnvelope childrenD_686_i1 b hb)

theorem finite_children_work_686 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_686 j) (childrenD_686 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_134 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_337 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 5 (6, 3)).mono (by decide +kernel)
  · exact finite_row_works_686_i0.mono (by decide +kernel)
  · exact finite_row_works_686_i1.mono (by decide +kernel)

theorem finite_row_works_686 : FiniteTemplate HasSnaky 9 required_686 envelope_686 := by
  refine finite_compose HasSnaky 8 childrenC_686 childrenD_686 finite_children_work_686 (4, 5)
    required_686 envelope_686 pivot_mem_686 child_required_sub_686 child_envelope_sub_686 ?_
  intro b hb
  exact common_sub_686 (mem_commonEnvelope childrenD_686 b hb)

theorem finite_children_work_688_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_688_i0 j) (childrenD_688_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 4 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_41 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_253 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_256 4 (0, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_336 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_688_i0 : FiniteTemplate HasSnaky 8 required_688_i0 envelope_688_i0 := by
  refine finite_compose HasSnaky 7 childrenC_688_i0 childrenD_688_i0 finite_children_work_688_i0 (3, 4)
    required_688_i0 envelope_688_i0 pivot_mem_688_i0 child_required_sub_688_i0 child_envelope_sub_688_i0 ?_
  intro b hb
  exact common_sub_688_i0 (mem_commonEnvelope childrenD_688_i0 b hb)

theorem finite_children_work_688 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_688 j) (childrenD_688 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_688_i0.mono (by decide +kernel)

theorem finite_row_works_688 : FiniteTemplate HasSnaky 9 required_688 envelope_688 := by
  refine finite_compose HasSnaky 8 childrenC_688 childrenD_688 finite_children_work_688 (1, 5)
    required_688 envelope_688 pivot_mem_688 child_required_sub_688 child_envelope_sub_688 ?_
  intro b hb
  exact common_sub_688 (mem_commonEnvelope childrenD_688 b hb)

end FiniteCongruenceChecks.SnakyFinite
