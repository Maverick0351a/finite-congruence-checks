/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height12Part05
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part03
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part02
import FiniteCards.Height07Part04
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part02
import FiniteCards.Height10Part04
import FiniteCards.Height10Part06
import FiniteCards.Height10Part07
import FiniteCards.Height11Part02
import FiniteCards.Height11Part05
import FiniteCards.Height11Part06

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_715_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_715_i1 j) (childrenD_715_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 6 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_111 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_394 1 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_715_i1 : FiniteTemplate HasSnaky 8 required_715_i1 envelope_715_i1 := by
  refine finite_compose HasSnaky 7 childrenC_715_i1 childrenD_715_i1 finite_children_work_715_i1 (4, 4)
    required_715_i1 envelope_715_i1 pivot_mem_715_i1 child_required_sub_715_i1 child_envelope_sub_715_i1 ?_
  intro b hb
  exact common_sub_715_i1 (mem_commonEnvelope childrenD_715_i1 b hb)

theorem finite_children_work_715_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_715_i0 j) (childrenD_715_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_134 2 (6, 3)).mono (by decide +kernel)
  · exact finite_row_works_715_i1.mono (by decide +kernel)

theorem finite_row_works_715_i0 : FiniteTemplate HasSnaky 9 required_715_i0 envelope_715_i0 := by
  refine finite_compose HasSnaky 8 childrenC_715_i0 childrenD_715_i0 finite_children_work_715_i0 (3, 5)
    required_715_i0 envelope_715_i0 pivot_mem_715_i0 child_required_sub_715_i0 child_envelope_sub_715_i0 ?_
  intro b hb
  exact common_sub_715_i0 (mem_commonEnvelope childrenD_715_i0 b hb)

theorem finite_children_work_715_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_715_i4 j) (childrenD_715_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 3 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_110 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_296 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_511 0 (4, 3)).mono (by decide +kernel)

theorem finite_row_works_715_i4 : FiniteTemplate HasSnaky 8 required_715_i4 envelope_715_i4 := by
  refine finite_compose HasSnaky 7 childrenC_715_i4 childrenD_715_i4 finite_children_work_715_i4 (7, 6)
    required_715_i4 envelope_715_i4 pivot_mem_715_i4 child_required_sub_715_i4 child_envelope_sub_715_i4 ?_
  intro b hb
  exact common_sub_715_i4 (mem_commonEnvelope childrenD_715_i4 b hb)

theorem finite_children_work_715_i3 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_715_i3 j) (childrenD_715_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 1 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_74 1 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_325 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_715_i4.mono (by decide +kernel)

theorem finite_row_works_715_i3 : FiniteTemplate HasSnaky 10 required_715_i3 envelope_715_i3 := by
  refine finite_compose HasSnaky 9 childrenC_715_i3 childrenD_715_i3 finite_children_work_715_i3 (7, 5)
    required_715_i3 envelope_715_i3 pivot_mem_715_i3 child_required_sub_715_i3 child_envelope_sub_715_i3 ?_
  intro b hb
  exact common_sub_715_i3 (mem_commonEnvelope childrenD_715_i3 b hb)

theorem finite_children_work_715_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_715_i2 j) (childrenD_715_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_361 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_408 5 (8, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_621 7 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_714 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_715_i3.mono (by decide +kernel)

theorem finite_row_works_715_i2 : FiniteTemplate HasSnaky 11 required_715_i2 envelope_715_i2 := by
  refine finite_compose HasSnaky 10 childrenC_715_i2 childrenD_715_i2 finite_children_work_715_i2 (4, 6)
    required_715_i2 envelope_715_i2 pivot_mem_715_i2 child_required_sub_715_i2 child_envelope_sub_715_i2 ?_
  intro b hb
  exact common_sub_715_i2 (mem_commonEnvelope childrenD_715_i2 b hb)

theorem finite_children_work_715 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_715 j) (childrenD_715 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_523 4 (2, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_532 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_536 6 (8, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_545 6 (6, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_655 4 (2, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_664 1 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_715_i0.mono (by decide +kernel)
  · exact finite_row_works_715_i2.mono (by decide +kernel)

theorem finite_row_works_715 : FiniteTemplate HasSnaky 12 required_715 envelope_715 := by
  refine finite_compose HasSnaky 11 childrenC_715 childrenD_715 finite_children_work_715 (5, 6)
    required_715 envelope_715 pivot_mem_715 child_required_sub_715 child_envelope_sub_715 ?_
  intro b hb
  exact common_sub_715 (mem_commonEnvelope childrenD_715 b hb)

theorem finite_children_work_717 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_717 j) (childrenD_717 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_192 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 7 (8, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_550 2 (10, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_550 4 (0, 11)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_578 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_578 6 (7, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_622 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_622 7 (9, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_716 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_716 6 (10, 11)).mono (by decide +kernel)

theorem finite_row_works_717 : FiniteTemplate HasSnaky 12 required_717 envelope_717 := by
  refine finite_compose HasSnaky 11 childrenC_717 childrenD_717 finite_children_work_717 (6, 6)
    required_717 envelope_717 pivot_mem_717 child_required_sub_717 child_envelope_sub_717 ?_
  intro b hb
  exact common_sub_717 (mem_commonEnvelope childrenD_717 b hb)

theorem finite_children_work_723_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_723_i0 j) (childrenD_723_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_46 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_321 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_723_i0 : FiniteTemplate HasSnaky 9 required_723_i0 envelope_723_i0 := by
  refine finite_compose HasSnaky 8 childrenC_723_i0 childrenD_723_i0 finite_children_work_723_i0 (4, 5)
    required_723_i0 envelope_723_i0 pivot_mem_723_i0 child_required_sub_723_i0 child_envelope_sub_723_i0 ?_
  intro b hb
  exact common_sub_723_i0 (mem_commonEnvelope childrenD_723_i0 b hb)

theorem finite_children_work_723_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_723_i1 j) (childrenD_723_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 6 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_310 1 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_723_i1 : FiniteTemplate HasSnaky 4 required_723_i1 envelope_723_i1 := by
  refine finite_compose HasSnaky 3 childrenC_723_i1 childrenD_723_i1 finite_children_work_723_i1 (2, 4)
    required_723_i1 envelope_723_i1 pivot_mem_723_i1 child_required_sub_723_i1 child_envelope_sub_723_i1 ?_
  intro b hb
  exact common_sub_723_i1 (mem_commonEnvelope childrenD_723_i1 b hb)

theorem finite_children_work_723_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_723_i4 j) (childrenD_723_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 6 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_90 3 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_99 5 (6, 4)).mono (by decide +kernel)

theorem finite_row_works_723_i4 : FiniteTemplate HasSnaky 5 required_723_i4 envelope_723_i4 := by
  refine finite_compose HasSnaky 4 childrenC_723_i4 childrenD_723_i4 finite_children_work_723_i4 (3, 4)
    required_723_i4 envelope_723_i4 pivot_mem_723_i4 child_required_sub_723_i4 child_envelope_sub_723_i4 ?_
  intro b hb
  exact common_sub_723_i4 (mem_commonEnvelope childrenD_723_i4 b hb)

theorem finite_children_work_723_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_723_i3 j) (childrenD_723_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_723_i4.mono (by decide +kernel)

theorem finite_row_works_723_i3 : FiniteTemplate HasSnaky 7 required_723_i3 envelope_723_i3 := by
  refine finite_compose HasSnaky 6 childrenC_723_i3 childrenD_723_i3 finite_children_work_723_i3 (3, 7)
    required_723_i3 envelope_723_i3 pivot_mem_723_i3 child_required_sub_723_i3 child_envelope_sub_723_i3 ?_
  intro b hb
  exact common_sub_723_i3 (mem_commonEnvelope childrenD_723_i3 b hb)

theorem finite_children_work_723_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_723_i5 j) (childrenD_723_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_82 0 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_176 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_218 1 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 6 (6, 10)).mono (by decide +kernel)

theorem finite_row_works_723_i5 : FiniteTemplate HasSnaky 7 required_723_i5 envelope_723_i5 := by
  refine finite_compose HasSnaky 6 childrenC_723_i5 childrenD_723_i5 finite_children_work_723_i5 (5, 6)
    required_723_i5 envelope_723_i5 pivot_mem_723_i5 child_required_sub_723_i5 child_envelope_sub_723_i5 ?_
  intro b hb
  exact common_sub_723_i5 (mem_commonEnvelope childrenD_723_i5 b hb)

theorem finite_children_work_723_i7 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_723_i7 j) (childrenD_723_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_145 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 3 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_723_i7 : FiniteTemplate HasSnaky 6 required_723_i7 envelope_723_i7 := by
  refine finite_compose HasSnaky 5 childrenC_723_i7 childrenD_723_i7 finite_children_work_723_i7 (3, 4)
    required_723_i7 envelope_723_i7 pivot_mem_723_i7 child_required_sub_723_i7 child_envelope_sub_723_i7 ?_
  intro b hb
  exact common_sub_723_i7 (mem_commonEnvelope childrenD_723_i7 b hb)

theorem finite_children_work_723_i6 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_723_i6 j) (childrenD_723_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 5 (5, 4)).mono (by decide +kernel)
  · exact finite_row_works_723_i7.mono (by decide +kernel)

theorem finite_row_works_723_i6 : FiniteTemplate HasSnaky 7 required_723_i6 envelope_723_i6 := by
  refine finite_compose HasSnaky 6 childrenC_723_i6 childrenD_723_i6 finite_children_work_723_i6 (3, 7)
    required_723_i6 envelope_723_i6 pivot_mem_723_i6 child_required_sub_723_i6 child_envelope_sub_723_i6 ?_
  intro b hb
  exact common_sub_723_i6 (mem_commonEnvelope childrenD_723_i6 b hb)

theorem finite_children_work_723_i8 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_723_i8 j) (childrenD_723_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 4 (4, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_369 6 (6, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_477 3 (3, 8)).mono (by decide +kernel)

theorem finite_row_works_723_i8 : FiniteTemplate HasSnaky 10 required_723_i8 envelope_723_i8 := by
  refine finite_compose HasSnaky 9 childrenC_723_i8 childrenD_723_i8 finite_children_work_723_i8 (5, 6)
    required_723_i8 envelope_723_i8 pivot_mem_723_i8 child_required_sub_723_i8 child_envelope_sub_723_i8 ?_
  intro b hb
  exact common_sub_723_i8 (mem_commonEnvelope childrenD_723_i8 b hb)

theorem finite_children_work_723_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_723_i2 j) (childrenD_723_i2 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_723_i3.mono (by decide +kernel)
  · exact finite_row_works_723_i5.mono (by decide +kernel)
  · exact finite_row_works_723_i6.mono (by decide +kernel)
  · exact finite_row_works_723_i8.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_721 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_722 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_723_i2 : FiniteTemplate HasSnaky 11 required_723_i2 envelope_723_i2 := by
  refine finite_compose HasSnaky 10 childrenC_723_i2 childrenD_723_i2 finite_children_work_723_i2 (5, 7)
    required_723_i2 envelope_723_i2 pivot_mem_723_i2 child_required_sub_723_i2 child_envelope_sub_723_i2 ?_
  intro b hb
  exact common_sub_723_i2 (mem_commonEnvelope childrenD_723_i2 b hb)

theorem finite_children_work_723 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_723 j) (childrenD_723 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_328 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_330 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_723_i0.mono (by decide +kernel)
  · exact finite_row_works_723_i1.mono (by decide +kernel)
  · exact finite_row_works_723_i2.mono (by decide +kernel)

theorem finite_row_works_723 : FiniteTemplate HasSnaky 12 required_723 envelope_723 := by
  refine finite_compose HasSnaky 11 childrenC_723 childrenD_723 finite_children_work_723 (5, 5)
    required_723 envelope_723 pivot_mem_723 child_required_sub_723 child_envelope_sub_723 ?_
  intro b hb
  exact common_sub_723 (mem_commonEnvelope childrenD_723 b hb)

end FiniteCongruenceChecks.SnakyFinite
