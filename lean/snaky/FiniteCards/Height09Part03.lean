/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part03
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part04
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_512_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_512_i0 j) (childrenD_512_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_69 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_416 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_512_i0 : FiniteTemplate HasSnaky 6 required_512_i0 envelope_512_i0 := by
  refine finite_compose HasSnaky 5 childrenC_512_i0 childrenD_512_i0 finite_children_work_512_i0 (3, 3)
    required_512_i0 envelope_512_i0 pivot_mem_512_i0 child_required_sub_512_i0 child_envelope_sub_512_i0 ?_
  intro b hb
  exact common_sub_512_i0 (mem_commonEnvelope childrenD_512_i0 b hb)

theorem finite_children_work_512_i3 : ∀ j, FiniteTemplate HasSnaky 1 (childrenC_512_i3 j) (childrenD_512_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_5 0 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_512_i3 : FiniteTemplate HasSnaky 2 required_512_i3 envelope_512_i3 := by
  refine finite_compose HasSnaky 1 childrenC_512_i3 childrenD_512_i3 finite_children_work_512_i3 (3, 4)
    required_512_i3 envelope_512_i3 pivot_mem_512_i3 child_required_sub_512_i3 child_envelope_sub_512_i3 ?_
  intro b hb
  exact common_sub_512_i3 (mem_commonEnvelope childrenD_512_i3 b hb)

theorem finite_children_work_512_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_512_i4 j) (childrenD_512_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 4 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_382 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_512_i4 : FiniteTemplate HasSnaky 6 required_512_i4 envelope_512_i4 := by
  refine finite_compose HasSnaky 5 childrenC_512_i4 childrenD_512_i4 finite_children_work_512_i4 (3, 6)
    required_512_i4 envelope_512_i4 pivot_mem_512_i4 child_required_sub_512_i4 child_envelope_sub_512_i4 ?_
  intro b hb
  exact common_sub_512_i4 (mem_commonEnvelope childrenD_512_i4 b hb)

theorem finite_children_work_512_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_512_i2 j) (childrenD_512_i2 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_512_i3.mono (by decide +kernel)
  · exact finite_row_works_512_i4.mono (by decide +kernel)

theorem finite_row_works_512_i2 : FiniteTemplate HasSnaky 7 required_512_i2 envelope_512_i2 := by
  refine finite_compose HasSnaky 6 childrenC_512_i2 childrenD_512_i2 finite_children_work_512_i2 (4, 5)
    required_512_i2 envelope_512_i2 pivot_mem_512_i2 child_required_sub_512_i2 child_envelope_sub_512_i2 ?_
  intro b hb
  exact common_sub_512_i2 (mem_commonEnvelope childrenD_512_i2 b hb)

theorem finite_children_work_512_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_512_i1 j) (childrenD_512_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_30 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_59 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_511 0 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_512_i2.mono (by decide +kernel)

theorem finite_row_works_512_i1 : FiniteTemplate HasSnaky 8 required_512_i1 envelope_512_i1 := by
  refine finite_compose HasSnaky 7 childrenC_512_i1 childrenD_512_i1 finite_children_work_512_i1 (4, 4)
    required_512_i1 envelope_512_i1 pivot_mem_512_i1 child_required_sub_512_i1 child_envelope_sub_512_i1 ?_
  intro b hb
  exact common_sub_512_i1 (mem_commonEnvelope childrenD_512_i1 b hb)

theorem finite_children_work_512 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_512 j) (childrenD_512 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_74 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_108 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_512_i0.mono (by decide +kernel)
  · exact finite_row_works_512_i1.mono (by decide +kernel)

theorem finite_row_works_512 : FiniteTemplate HasSnaky 9 required_512 envelope_512 := by
  refine finite_compose HasSnaky 8 childrenC_512 childrenD_512 finite_children_work_512 (4, 3)
    required_512 envelope_512 pivot_mem_512 child_required_sub_512 child_envelope_sub_512 ?_
  intro b hb
  exact common_sub_512 (mem_commonEnvelope childrenD_512 b hb)

theorem finite_children_work_514 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_514 j) (childrenD_514 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 7 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_149 5 (5, 1)).mono (by decide +kernel)
  · exact finite_row_works_513.mono (by decide +kernel)

theorem finite_row_works_514 : FiniteTemplate HasSnaky 9 required_514 envelope_514 := by
  refine finite_compose HasSnaky 8 childrenC_514 childrenD_514 finite_children_work_514 (3, 2)
    required_514 envelope_514 pivot_mem_514 child_required_sub_514 child_envelope_sub_514 ?_
  intro b hb
  exact common_sub_514 (mem_commonEnvelope childrenD_514 b hb)

theorem finite_children_work_519 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_519 j) (childrenD_519 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_47 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_518 2 (6, 0)).mono (by decide +kernel)

theorem finite_row_works_519 : FiniteTemplate HasSnaky 9 required_519 envelope_519 := by
  refine finite_compose HasSnaky 8 childrenC_519 childrenD_519 finite_children_work_519 (3, 5)
    required_519 envelope_519 pivot_mem_519 child_required_sub_519 child_envelope_sub_519 ?_
  intro b hb
  exact common_sub_519 (mem_commonEnvelope childrenD_519 b hb)

theorem finite_children_work_528_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_528_i0 j) (childrenD_528_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 5 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 7 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_528_i0 : FiniteTemplate HasSnaky 5 required_528_i0 envelope_528_i0 := by
  refine finite_compose HasSnaky 4 childrenC_528_i0 childrenD_528_i0 finite_children_work_528_i0 (1, 3)
    required_528_i0 envelope_528_i0 pivot_mem_528_i0 child_required_sub_528_i0 child_envelope_sub_528_i0 ?_
  intro b hb
  exact common_sub_528_i0 (mem_commonEnvelope childrenD_528_i0 b hb)

theorem finite_children_work_528_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_528_i1 j) (childrenD_528_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 5 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_446 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_528_i1 : FiniteTemplate HasSnaky 8 required_528_i1 envelope_528_i1 := by
  refine finite_compose HasSnaky 7 childrenC_528_i1 childrenD_528_i1 finite_children_work_528_i1 (1, 7)
    required_528_i1 envelope_528_i1 pivot_mem_528_i1 child_required_sub_528_i1 child_envelope_sub_528_i1 ?_
  intro b hb
  exact common_sub_528_i1 (mem_commonEnvelope childrenD_528_i1 b hb)

theorem finite_children_work_528 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_528 j) (childrenD_528 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_61 2 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_528_i0.mono (by decide +kernel)
  · exact finite_row_works_528_i1.mono (by decide +kernel)

theorem finite_row_works_528 : FiniteTemplate HasSnaky 9 required_528 envelope_528 := by
  refine finite_compose HasSnaky 8 childrenC_528 childrenD_528 finite_children_work_528 (0, 7)
    required_528 envelope_528 pivot_mem_528 child_required_sub_528 child_envelope_sub_528 ?_
  intro b hb
  exact common_sub_528 (mem_commonEnvelope childrenD_528 b hb)

theorem finite_children_work_531 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_531 j) (childrenD_531 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact finite_row_works_530.mono (by decide +kernel)

theorem finite_row_works_531 : FiniteTemplate HasSnaky 9 required_531 envelope_531 := by
  refine finite_compose HasSnaky 8 childrenC_531 childrenD_531 finite_children_work_531 (1, 4)
    required_531 envelope_531 pivot_mem_531 child_required_sub_531 child_envelope_sub_531 ?_
  intro b hb
  exact common_sub_531 (mem_commonEnvelope childrenD_531 b hb)

theorem finite_children_work_536 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_536 j) (childrenD_536 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_14 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_88 7 (6, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_213 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_534 3 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_536 : FiniteTemplate HasSnaky 9 required_536 envelope_536 := by
  refine finite_compose HasSnaky 8 childrenC_536 childrenD_536 finite_children_work_536 (3, 5)
    required_536 envelope_536 pivot_mem_536 child_required_sub_536 child_envelope_sub_536 ?_
  intro b hb
  exact common_sub_536 (mem_commonEnvelope childrenD_536 b hb)

theorem finite_children_work_537_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_537_i0 j) (childrenD_537_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_45 6 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_418 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_537_i0 : FiniteTemplate HasSnaky 8 required_537_i0 envelope_537_i0 := by
  refine finite_compose HasSnaky 7 childrenC_537_i0 childrenD_537_i0 finite_children_work_537_i0 (3, 3)
    required_537_i0 envelope_537_i0 pivot_mem_537_i0 child_required_sub_537_i0 child_envelope_sub_537_i0 ?_
  intro b hb
  exact common_sub_537_i0 (mem_commonEnvelope childrenD_537_i0 b hb)

theorem finite_children_work_537_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_537_i2 j) (childrenD_537_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 6 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_425 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_537_i2 : FiniteTemplate HasSnaky 6 required_537_i2 envelope_537_i2 := by
  refine finite_compose HasSnaky 5 childrenC_537_i2 childrenD_537_i2 finite_children_work_537_i2 (2, 5)
    required_537_i2 envelope_537_i2 pivot_mem_537_i2 child_required_sub_537_i2 child_envelope_sub_537_i2 ?_
  intro b hb
  exact common_sub_537_i2 (mem_commonEnvelope childrenD_537_i2 b hb)

theorem finite_children_work_537_i6 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_537_i6 j) (childrenD_537_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 2 (2, 2)).mono (by decide +kernel)

theorem finite_row_works_537_i6 : FiniteTemplate HasSnaky 3 required_537_i6 envelope_537_i6 := by
  refine finite_compose HasSnaky 2 childrenC_537_i6 childrenD_537_i6 finite_children_work_537_i6 (2, 5)
    required_537_i6 envelope_537_i6 pivot_mem_537_i6 child_required_sub_537_i6 child_envelope_sub_537_i6 ?_
  intro b hb
  exact common_sub_537_i6 (mem_commonEnvelope childrenD_537_i6 b hb)

theorem finite_children_work_537_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_537_i5 j) (childrenD_537_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_537_i6.mono (by decide +kernel)

theorem finite_row_works_537_i5 : FiniteTemplate HasSnaky 4 required_537_i5 envelope_537_i5 := by
  refine finite_compose HasSnaky 3 childrenC_537_i5 childrenD_537_i5 finite_children_work_537_i5 (3, 5)
    required_537_i5 envelope_537_i5 pivot_mem_537_i5 child_required_sub_537_i5 child_envelope_sub_537_i5 ?_
  intro b hb
  exact common_sub_537_i5 (mem_commonEnvelope childrenD_537_i5 b hb)

theorem finite_children_work_537_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_537_i4 j) (childrenD_537_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_139 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_382 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_537_i5.mono (by decide +kernel)

theorem finite_row_works_537_i4 : FiniteTemplate HasSnaky 6 required_537_i4 envelope_537_i4 := by
  refine finite_compose HasSnaky 5 childrenC_537_i4 childrenD_537_i4 finite_children_work_537_i4 (3, 6)
    required_537_i4 envelope_537_i4 pivot_mem_537_i4 child_required_sub_537_i4 child_envelope_sub_537_i4 ?_
  intro b hb
  exact common_sub_537_i4 (mem_commonEnvelope childrenD_537_i4 b hb)

theorem finite_children_work_537_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_537_i3 j) (childrenD_537_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 2 (5, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_30 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_537_i4.mono (by decide +kernel)

theorem finite_row_works_537_i3 : FiniteTemplate HasSnaky 7 required_537_i3 envelope_537_i3 := by
  refine finite_compose HasSnaky 6 childrenC_537_i3 childrenD_537_i3 finite_children_work_537_i3 (4, 4)
    required_537_i3 envelope_537_i3 pivot_mem_537_i3 child_required_sub_537_i3 child_envelope_sub_537_i3 ?_
  intro b hb
  exact common_sub_537_i3 (mem_commonEnvelope childrenD_537_i3 b hb)

theorem finite_children_work_537_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_537_i1 j) (childrenD_537_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_166 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_464 4 (1, 7)).mono (by decide +kernel)
  · exact finite_row_works_537_i2.mono (by decide +kernel)
  · exact finite_row_works_537_i3.mono (by decide +kernel)

theorem finite_row_works_537_i1 : FiniteTemplate HasSnaky 8 required_537_i1 envelope_537_i1 := by
  refine finite_compose HasSnaky 7 childrenC_537_i1 childrenD_537_i1 finite_children_work_537_i1 (4, 5)
    required_537_i1 envelope_537_i1 pivot_mem_537_i1 child_required_sub_537_i1 child_envelope_sub_537_i1 ?_
  intro b hb
  exact common_sub_537_i1 (mem_commonEnvelope childrenD_537_i1 b hb)

theorem finite_children_work_537 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_537 j) (childrenD_537 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_74 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_108 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_537_i0.mono (by decide +kernel)
  · exact finite_row_works_537_i1.mono (by decide +kernel)

theorem finite_row_works_537 : FiniteTemplate HasSnaky 9 required_537 envelope_537 := by
  refine finite_compose HasSnaky 8 childrenC_537 childrenD_537 finite_children_work_537 (4, 3)
    required_537 envelope_537 pivot_mem_537 child_required_sub_537 child_envelope_sub_537 ?_
  intro b hb
  exact common_sub_537 (mem_commonEnvelope childrenD_537 b hb)

end FiniteCongruenceChecks.SnakyFinite
