/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part04
import FiniteCards.Height06Part01
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height13Part02
import FiniteCards.Height13Part03
import FiniteCards.Height13Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_645_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_645_i0 j) (childrenD_645_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_128 3 (2, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_144 6 (6, 6)).mono (by decide +kernel)

theorem finite_row_works_645_i0 : FiniteTemplate HasSnaky 6 required_645_i0 envelope_645_i0 := by
  refine finite_compose HasSnaky 5 childrenC_645_i0 childrenD_645_i0 finite_children_work_645_i0 (5, 4)
    required_645_i0 envelope_645_i0 pivot_mem_645_i0 child_required_sub_645_i0 child_envelope_sub_645_i0 ?_
  intro b hb
  exact common_sub_645_i0 (mem_commonEnvelope childrenD_645_i0 b hb)

theorem finite_children_work_645_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_645_i1 j) (childrenD_645_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_104 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_359 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_438 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_452 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_476 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_479 0 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_645_i1 : FiniteTemplate HasSnaky 11 required_645_i1 envelope_645_i1 := by
  refine finite_compose HasSnaky 10 childrenC_645_i1 childrenD_645_i1 finite_children_work_645_i1 (6, 5)
    required_645_i1 envelope_645_i1 pivot_mem_645_i1 child_required_sub_645_i1 child_envelope_sub_645_i1 ?_
  intro b hb
  exact common_sub_645_i1 (mem_commonEnvelope childrenD_645_i1 b hb)

theorem finite_children_work_645 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_645 j) (childrenD_645 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_120 6 (7, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_276 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_338 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_437 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_611 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_634 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_642 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_643 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_645_i0.mono (by decide +kernel)
  · exact finite_row_works_645_i1.mono (by decide +kernel)

theorem finite_row_works_645 : FiniteTemplate HasSnaky 14 required_645 envelope_645 := by
  refine finite_compose HasSnaky 13 childrenC_645 childrenD_645 finite_children_work_645 (6, 4)
    required_645 envelope_645 pivot_mem_645 child_required_sub_645 child_envelope_sub_645 ?_
  intro b hb
  exact common_sub_645 (mem_commonEnvelope childrenD_645 b hb)

theorem finite_children_work_669_i5 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_669_i5 j) (childrenD_669_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_66 7 (7, 7)).mono (by decide +kernel)

theorem finite_row_works_669_i5 : FiniteTemplate HasSnaky 3 required_669_i5 envelope_669_i5 := by
  refine finite_compose HasSnaky 2 childrenC_669_i5 childrenD_669_i5 finite_children_work_669_i5 (5, 6)
    required_669_i5 envelope_669_i5 pivot_mem_669_i5 child_required_sub_669_i5 child_envelope_sub_669_i5 ?_
  intro b hb
  exact common_sub_669_i5 (mem_commonEnvelope childrenD_669_i5 b hb)

theorem finite_children_work_669_i4 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_669_i4 j) (childrenD_669_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (4, 8)).mono (by decide +kernel)
  · exact finite_row_works_669_i5.mono (by decide +kernel)

theorem finite_row_works_669_i4 : FiniteTemplate HasSnaky 4 required_669_i4 envelope_669_i4 := by
  refine finite_compose HasSnaky 3 childrenC_669_i4 childrenD_669_i4 finite_children_work_669_i4 (4, 6)
    required_669_i4 envelope_669_i4 pivot_mem_669_i4 child_required_sub_669_i4 child_envelope_sub_669_i4 ?_
  intro b hb
  exact common_sub_669_i4 (mem_commonEnvelope childrenD_669_i4 b hb)

theorem finite_children_work_669_i6 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_669_i6 j) (childrenD_669_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_36 0 (3, 4)).mono (by decide +kernel)

theorem finite_row_works_669_i6 : FiniteTemplate HasSnaky 3 required_669_i6 envelope_669_i6 := by
  refine finite_compose HasSnaky 2 childrenC_669_i6 childrenD_669_i6 finite_children_work_669_i6 (3, 7)
    required_669_i6 envelope_669_i6 pivot_mem_669_i6 child_required_sub_669_i6 child_envelope_sub_669_i6 ?_
  intro b hb
  exact common_sub_669_i6 (mem_commonEnvelope childrenD_669_i6 b hb)

theorem finite_children_work_669_i7 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_669_i7 j) (childrenD_669_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_24 2 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_36 0 (3, 4)).mono (by decide +kernel)

theorem finite_row_works_669_i7 : FiniteTemplate HasSnaky 4 required_669_i7 envelope_669_i7 := by
  refine finite_compose HasSnaky 3 childrenC_669_i7 childrenD_669_i7 finite_children_work_669_i7 (3, 7)
    required_669_i7 envelope_669_i7 pivot_mem_669_i7 child_required_sub_669_i7 child_envelope_sub_669_i7 ?_
  intro b hb
  exact common_sub_669_i7 (mem_commonEnvelope childrenD_669_i7 b hb)

theorem finite_children_work_669_i3 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_669_i3 j) (childrenD_669_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_48 5 (7, 6)).mono (by decide +kernel)
  · exact finite_row_works_669_i4.mono (by decide +kernel)
  · exact finite_row_works_669_i6.mono (by decide +kernel)
  · exact finite_row_works_669_i7.mono (by decide +kernel)

theorem finite_row_works_669_i3 : FiniteTemplate HasSnaky 5 required_669_i3 envelope_669_i3 := by
  refine finite_compose HasSnaky 4 childrenC_669_i3 childrenD_669_i3 finite_children_work_669_i3 (4, 7)
    required_669_i3 envelope_669_i3 pivot_mem_669_i3 child_required_sub_669_i3 child_envelope_sub_669_i3 ?_
  intro b hb
  exact common_sub_669_i3 (mem_commonEnvelope childrenD_669_i3 b hb)

theorem finite_children_work_669_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_669_i2 j) (childrenD_669_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (6, 4)).mono (by decide +kernel)
  · exact finite_row_works_669_i3.mono (by decide +kernel)

theorem finite_row_works_669_i2 : FiniteTemplate HasSnaky 6 required_669_i2 envelope_669_i2 := by
  refine finite_compose HasSnaky 5 childrenC_669_i2 childrenD_669_i2 finite_children_work_669_i2 (5, 7)
    required_669_i2 envelope_669_i2 pivot_mem_669_i2 child_required_sub_669_i2 child_envelope_sub_669_i2 ?_
  intro b hb
  exact common_sub_669_i2 (mem_commonEnvelope childrenD_669_i2 b hb)

theorem finite_children_work_669_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_669_i1 j) (childrenD_669_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_25 7 (7, 7)).mono (by decide +kernel)
  · exact finite_row_works_669_i2.mono (by decide +kernel)

theorem finite_row_works_669_i1 : FiniteTemplate HasSnaky 7 required_669_i1 envelope_669_i1 := by
  refine finite_compose HasSnaky 6 childrenC_669_i1 childrenD_669_i1 finite_children_work_669_i1 (4, 5)
    required_669_i1 envelope_669_i1 pivot_mem_669_i1 child_required_sub_669_i1 child_envelope_sub_669_i1 ?_
  intro b hb
  exact common_sub_669_i1 (mem_commonEnvelope childrenD_669_i1 b hb)

theorem finite_children_work_669_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_669_i0 j) (childrenD_669_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_19 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 1 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_225 2 (7, 3)).mono (by decide +kernel)
  · exact finite_row_works_669_i1.mono (by decide +kernel)

theorem finite_row_works_669_i0 : FiniteTemplate HasSnaky 8 required_669_i0 envelope_669_i0 := by
  refine finite_compose HasSnaky 7 childrenC_669_i0 childrenD_669_i0 finite_children_work_669_i0 (6, 7)
    required_669_i0 envelope_669_i0 pivot_mem_669_i0 child_required_sub_669_i0 child_envelope_sub_669_i0 ?_
  intro b hb
  exact common_sub_669_i0 (mem_commonEnvelope childrenD_669_i0 b hb)

theorem finite_children_work_669 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_669 j) (childrenD_669 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_188 4 (4, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_590 2 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_668 4 (3, 7)).mono (by decide +kernel)
  · exact finite_row_works_669_i0.mono (by decide +kernel)

theorem finite_row_works_669 : FiniteTemplate HasSnaky 14 required_669 envelope_669 := by
  refine finite_compose HasSnaky 13 childrenC_669 childrenD_669 finite_children_work_669 (6, 4)
    required_669 envelope_669 pivot_mem_669 child_required_sub_669 child_envelope_sub_669 ?_
  intro b hb
  exact common_sub_669 (mem_commonEnvelope childrenD_669 b hb)

theorem finite_children_work_693_i1 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_693_i1 j) (childrenD_693_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_409 1 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_693_i1 : FiniteTemplate HasSnaky 11 required_693_i1 envelope_693_i1 := by
  refine finite_compose HasSnaky 10 childrenC_693_i1 childrenD_693_i1 finite_children_work_693_i1 (5, 8)
    required_693_i1 envelope_693_i1 pivot_mem_693_i1 child_required_sub_693_i1 child_envelope_sub_693_i1 ?_
  intro b hb
  exact common_sub_693_i1 (mem_commonEnvelope childrenD_693_i1 b hb)

theorem finite_children_work_693_i2 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_693_i2 j) (childrenD_693_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_168 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_409 1 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_611 1 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_693_i2 : FiniteTemplate HasSnaky 11 required_693_i2 envelope_693_i2 := by
  refine finite_compose HasSnaky 10 childrenC_693_i2 childrenD_693_i2 finite_children_work_693_i2 (5, 8)
    required_693_i2 envelope_693_i2 pivot_mem_693_i2 child_required_sub_693_i2 child_envelope_sub_693_i2 ?_
  intro b hb
  exact common_sub_693_i2 (mem_commonEnvelope childrenD_693_i2 b hb)

theorem finite_children_work_693_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_693_i4 j) (childrenD_693_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 5 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_308 4 (4, 8)).mono (by decide +kernel)

theorem finite_row_works_693_i4 : FiniteTemplate HasSnaky 6 required_693_i4 envelope_693_i4 := by
  refine finite_compose HasSnaky 5 childrenC_693_i4 childrenD_693_i4 finite_children_work_693_i4 (5, 4)
    required_693_i4 envelope_693_i4 pivot_mem_693_i4 child_required_sub_693_i4 child_envelope_sub_693_i4 ?_
  intro b hb
  exact common_sub_693_i4 (mem_commonEnvelope childrenD_693_i4 b hb)

theorem finite_children_work_693_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_693_i3 j) (childrenD_693_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 5 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_26 2 (6, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_214 2 (7, 2)).mono (by decide +kernel)
  · exact finite_row_works_693_i4.mono (by decide +kernel)

theorem finite_row_works_693_i3 : FiniteTemplate HasSnaky 7 required_693_i3 envelope_693_i3 := by
  refine finite_compose HasSnaky 6 childrenC_693_i3 childrenD_693_i3 finite_children_work_693_i3 (3, 5)
    required_693_i3 envelope_693_i3 pivot_mem_693_i3 child_required_sub_693_i3 child_envelope_sub_693_i3 ?_
  intro b hb
  exact common_sub_693_i3 (mem_commonEnvelope childrenD_693_i3 b hb)

theorem finite_children_work_693_i6 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_693_i6 j) (childrenD_693_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_233 2 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 7 (6, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_314 3 (4, 7)).mono (by decide +kernel)

theorem finite_row_works_693_i6 : FiniteTemplate HasSnaky 6 required_693_i6 envelope_693_i6 := by
  refine finite_compose HasSnaky 5 childrenC_693_i6 childrenD_693_i6 finite_children_work_693_i6 (5, 4)
    required_693_i6 envelope_693_i6 pivot_mem_693_i6 child_required_sub_693_i6 child_envelope_sub_693_i6 ?_
  intro b hb
  exact common_sub_693_i6 (mem_commonEnvelope childrenD_693_i6 b hb)

theorem finite_children_work_693_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_693_i5 j) (childrenD_693_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 6 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 4 (5, 8)).mono (by decide +kernel)
  · exact finite_row_works_693_i6.mono (by decide +kernel)

theorem finite_row_works_693_i5 : FiniteTemplate HasSnaky 7 required_693_i5 envelope_693_i5 := by
  refine finite_compose HasSnaky 6 childrenC_693_i5 childrenD_693_i5 finite_children_work_693_i5 (5, 6)
    required_693_i5 envelope_693_i5 pivot_mem_693_i5 child_required_sub_693_i5 child_envelope_sub_693_i5 ?_
  intro b hb
  exact common_sub_693_i5 (mem_commonEnvelope childrenD_693_i5 b hb)

theorem finite_children_work_693_i0 : ∀ j, FiniteTemplate HasSnaky 11 (childrenC_693_i0 j) (childrenD_693_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_319 6 (7, 10)).mono (by decide +kernel)
  · exact finite_row_works_693_i1.mono (by decide +kernel)
  · exact finite_row_works_693_i2.mono (by decide +kernel)
  · exact finite_row_works_693_i3.mono (by decide +kernel)
  · exact finite_row_works_693_i5.mono (by decide +kernel)

theorem finite_row_works_693_i0 : FiniteTemplate HasSnaky 12 required_693_i0 envelope_693_i0 := by
  refine finite_compose HasSnaky 11 childrenC_693_i0 childrenD_693_i0 finite_children_work_693_i0 (5, 7)
    required_693_i0 envelope_693_i0 pivot_mem_693_i0 child_required_sub_693_i0 child_envelope_sub_693_i0 ?_
  intro b hb
  exact common_sub_693_i0 (mem_commonEnvelope childrenD_693_i0 b hb)

theorem finite_children_work_693 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_693 j) (childrenD_693 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_147 0 (4, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_339 7 (8, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_692 1 (2, 5)).mono (by decide +kernel)
  · exact finite_row_works_693_i0.mono (by decide +kernel)

theorem finite_row_works_693 : FiniteTemplate HasSnaky 14 required_693 envelope_693 := by
  refine finite_compose HasSnaky 13 childrenC_693 childrenD_693 finite_children_work_693 (7, 8)
    required_693 envelope_693 pivot_mem_693 child_required_sub_693 child_envelope_sub_693 ?_
  intro b hb
  exact common_sub_693 (mem_commonEnvelope childrenD_693 b hb)

end FiniteCongruenceChecks.SnakyFinite
