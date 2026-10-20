/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height17Part02
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height10Part06
import FiniteCards.Height11Part04
import FiniteCards.Height11Part05
import FiniteCards.Height11Part06
import FiniteCards.Height12Part01
import FiniteCards.Height14Part04
import FiniteCards.Height16Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_707_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_707_i0 j) (childrenD_707_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_116 3 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_337 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 5 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_662 1 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_707_i0 : FiniteTemplate HasSnaky 10 required_707_i0 envelope_707_i0 := by
  refine finite_compose HasSnaky 9 childrenC_707_i0 childrenD_707_i0 finite_children_work_707_i0 (5, 7)
    required_707_i0 envelope_707_i0 pivot_mem_707_i0 child_required_sub_707_i0 child_envelope_sub_707_i0 ?_
  intro b hb
  exact common_sub_707_i0 (mem_commonEnvelope childrenD_707_i0 b hb)

theorem finite_children_work_707_i2 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_707_i2 j) (childrenD_707_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_380 5 (6, 4)).mono (by decide +kernel)

theorem finite_row_works_707_i2 : FiniteTemplate HasSnaky 10 required_707_i2 envelope_707_i2 := by
  refine finite_compose HasSnaky 9 childrenC_707_i2 childrenD_707_i2 finite_children_work_707_i2 (5, 7)
    required_707_i2 envelope_707_i2 pivot_mem_707_i2 child_required_sub_707_i2 child_envelope_sub_707_i2 ?_
  intro b hb
  exact common_sub_707_i2 (mem_commonEnvelope childrenD_707_i2 b hb)

theorem finite_children_work_707_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_707_i1 j) (childrenD_707_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_33 4 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 3 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_707_i2.mono (by decide +kernel)

theorem finite_row_works_707_i1 : FiniteTemplate HasSnaky 11 required_707_i1 envelope_707_i1 := by
  refine finite_compose HasSnaky 10 childrenC_707_i1 childrenD_707_i1 finite_children_work_707_i1 (5, 4)
    required_707_i1 envelope_707_i1 pivot_mem_707_i1 child_required_sub_707_i1 child_envelope_sub_707_i1 ?_
  intro b hb
  exact common_sub_707_i1 (mem_commonEnvelope childrenD_707_i1 b hb)

theorem finite_children_work_707_i4 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_707_i4 j) (childrenD_707_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 0 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_485 4 (4, 9)).mono (by decide +kernel)

theorem finite_row_works_707_i4 : FiniteTemplate HasSnaky 13 required_707_i4 envelope_707_i4 := by
  refine finite_compose HasSnaky 12 childrenC_707_i4 childrenD_707_i4 finite_children_work_707_i4 (5, 7)
    required_707_i4 envelope_707_i4 pivot_mem_707_i4 child_required_sub_707_i4 child_envelope_sub_707_i4 ?_
  intro b hb
  exact common_sub_707_i4 (mem_commonEnvelope childrenD_707_i4 b hb)

theorem finite_children_work_707_i3 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_707_i3 j) (childrenD_707_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_136 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_267 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_322 5 (9, 3)).mono (by decide +kernel)
  · exact finite_row_works_707_i4.mono (by decide +kernel)

theorem finite_row_works_707_i3 : FiniteTemplate HasSnaky 14 required_707_i3 envelope_707_i3 := by
  refine finite_compose HasSnaky 13 childrenC_707_i3 childrenD_707_i3 finite_children_work_707_i3 (5, 4)
    required_707_i3 envelope_707_i3 pivot_mem_707_i3 child_required_sub_707_i3 child_envelope_sub_707_i3 ?_
  intro b hb
  exact common_sub_707_i3 (mem_commonEnvelope childrenD_707_i3 b hb)

theorem finite_children_work_707_i6 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_707_i6 j) (childrenD_707_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_302 5 (8, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_303 5 (8, 3)).mono (by decide +kernel)

theorem finite_row_works_707_i6 : FiniteTemplate HasSnaky 7 required_707_i6 envelope_707_i6 := by
  refine finite_compose HasSnaky 6 childrenC_707_i6 childrenD_707_i6 finite_children_work_707_i6 (5, 7)
    required_707_i6 envelope_707_i6 pivot_mem_707_i6 child_required_sub_707_i6 child_envelope_sub_707_i6 ?_
  intro b hb
  exact common_sub_707_i6 (mem_commonEnvelope childrenD_707_i6 b hb)

theorem finite_children_work_707_i5 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_707_i5 j) (childrenD_707_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 4 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 6 (6, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_332 7 (8, 7)).mono (by decide +kernel)
  · exact finite_row_works_707_i6.mono (by decide +kernel)

theorem finite_row_works_707_i5 : FiniteTemplate HasSnaky 8 required_707_i5 envelope_707_i5 := by
  refine finite_compose HasSnaky 7 childrenC_707_i5 childrenD_707_i5 finite_children_work_707_i5 (5, 4)
    required_707_i5 envelope_707_i5 pivot_mem_707_i5 child_required_sub_707_i5 child_envelope_sub_707_i5 ?_
  intro b hb
  exact common_sub_707_i5 (mem_commonEnvelope childrenD_707_i5 b hb)

theorem finite_children_work_707_i7 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_707_i7 j) (childrenD_707_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_12 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_13 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_118 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 6 (6, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_528 0 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_689 1 (1, 3)).mono (by decide +kernel)

theorem finite_row_works_707_i7 : FiniteTemplate HasSnaky 12 required_707_i7 envelope_707_i7 := by
  refine finite_compose HasSnaky 11 childrenC_707_i7 childrenD_707_i7 finite_children_work_707_i7 (5, 7)
    required_707_i7 envelope_707_i7 pivot_mem_707_i7 child_required_sub_707_i7 child_envelope_sub_707_i7 ?_
  intro b hb
  exact common_sub_707_i7 (mem_commonEnvelope childrenD_707_i7 b hb)

theorem finite_children_work_707_i8 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_707_i8 j) (childrenD_707_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_537 5 (8, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_537 4 (3, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_702 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_702 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_704 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_704 0 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_707_i8 : FiniteTemplate HasSnaky 11 required_707_i8 envelope_707_i8 := by
  refine finite_compose HasSnaky 10 childrenC_707_i8 childrenD_707_i8 finite_children_work_707_i8 (4, 6)
    required_707_i8 envelope_707_i8 pivot_mem_707_i8 child_required_sub_707_i8 child_envelope_sub_707_i8 ?_
  intro b hb
  exact common_sub_707_i8 (mem_commonEnvelope childrenD_707_i8 b hb)

theorem finite_children_work_707 : ∀ j, FiniteTemplate HasSnaky 16 (childrenC_707 j) (childrenD_707 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_459 0 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_535 4 (3, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_617 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_660 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_663 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_707_i0.mono (by decide +kernel)
  · exact finite_row_works_707_i1.mono (by decide +kernel)
  · exact finite_row_works_707_i3.mono (by decide +kernel)
  · exact finite_row_works_707_i5.mono (by decide +kernel)
  · exact finite_row_works_707_i7.mono (by decide +kernel)
  · exact finite_row_works_707_i8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_705 4 (2, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_706 4 (0, 10)).mono (by decide +kernel)

theorem finite_row_works_707 : FiniteTemplate HasSnaky 17 required_707 envelope_707 := by
  refine finite_compose HasSnaky 16 childrenC_707 childrenD_707 finite_children_work_707 (5, 6)
    required_707 envelope_707 pivot_mem_707 child_required_sub_707 child_envelope_sub_707 ?_
  intro b hb
  exact common_sub_707 (mem_commonEnvelope childrenD_707 b hb)

end FiniteCongruenceChecks.SnakyFinite
