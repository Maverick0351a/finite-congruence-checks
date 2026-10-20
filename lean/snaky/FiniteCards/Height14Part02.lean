/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height14Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height05Part01
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part04
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height09Part01
import FiniteCards.Height09Part02
import FiniteCards.Height09Part03
import FiniteCards.Height09Part05
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part05
import FiniteCards.Height11Part03
import FiniteCards.Height12Part02
import FiniteCards.Height12Part04
import FiniteCards.Height13Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_598_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_598_i2 j) (childrenD_598_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 2 (7, 3)).mono (by decide +kernel)

theorem finite_row_works_598_i2 : FiniteTemplate HasSnaky 6 required_598_i2 envelope_598_i2 := by
  refine finite_compose HasSnaky 5 childrenC_598_i2 childrenD_598_i2 finite_children_work_598_i2 (5, 5)
    required_598_i2 envelope_598_i2 pivot_mem_598_i2 child_required_sub_598_i2 child_envelope_sub_598_i2 ?_
  intro b hb
  exact common_sub_598_i2 (mem_commonEnvelope childrenD_598_i2 b hb)

theorem finite_children_work_598_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_598_i1 j) (childrenD_598_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (3, 8)).mono (by decide +kernel)
  · exact finite_row_works_598_i2.mono (by decide +kernel)

theorem finite_row_works_598_i1 : FiniteTemplate HasSnaky 7 required_598_i1 envelope_598_i1 := by
  refine finite_compose HasSnaky 6 childrenC_598_i1 childrenD_598_i1 finite_children_work_598_i1 (4, 5)
    required_598_i1 envelope_598_i1 pivot_mem_598_i1 child_required_sub_598_i1 child_envelope_sub_598_i1 ?_
  intro b hb
  exact common_sub_598_i1 (mem_commonEnvelope childrenD_598_i1 b hb)

theorem finite_children_work_598_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_598_i0 j) (childrenD_598_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_598_i1.mono (by decide +kernel)

theorem finite_row_works_598_i0 : FiniteTemplate HasSnaky 8 required_598_i0 envelope_598_i0 := by
  refine finite_compose HasSnaky 7 childrenC_598_i0 childrenD_598_i0 finite_children_work_598_i0 (3, 6)
    required_598_i0 envelope_598_i0 pivot_mem_598_i0 child_required_sub_598_i0 child_envelope_sub_598_i0 ?_
  intro b hb
  exact common_sub_598_i0 (mem_commonEnvelope childrenD_598_i0 b hb)

theorem finite_children_work_598_i5 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_598_i5 j) (childrenD_598_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_133 6 (7, 7)).mono (by decide +kernel)

theorem finite_row_works_598_i5 : FiniteTemplate HasSnaky 6 required_598_i5 envelope_598_i5 := by
  refine finite_compose HasSnaky 5 childrenC_598_i5 childrenD_598_i5 finite_children_work_598_i5 (5, 5)
    required_598_i5 envelope_598_i5 pivot_mem_598_i5 child_required_sub_598_i5 child_envelope_sub_598_i5 ?_
  intro b hb
  exact common_sub_598_i5 (mem_commonEnvelope childrenD_598_i5 b hb)

theorem finite_children_work_598_i4 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_598_i4 j) (childrenD_598_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (3, 8)).mono (by decide +kernel)
  · exact finite_row_works_598_i5.mono (by decide +kernel)

theorem finite_row_works_598_i4 : FiniteTemplate HasSnaky 7 required_598_i4 envelope_598_i4 := by
  refine finite_compose HasSnaky 6 childrenC_598_i4 childrenD_598_i4 finite_children_work_598_i4 (4, 5)
    required_598_i4 envelope_598_i4 pivot_mem_598_i4 child_required_sub_598_i4 child_envelope_sub_598_i4 ?_
  intro b hb
  exact common_sub_598_i4 (mem_commonEnvelope childrenD_598_i4 b hb)

theorem finite_children_work_598_i3 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_598_i3 j) (childrenD_598_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_598_i4.mono (by decide +kernel)

theorem finite_row_works_598_i3 : FiniteTemplate HasSnaky 8 required_598_i3 envelope_598_i3 := by
  refine finite_compose HasSnaky 7 childrenC_598_i3 childrenD_598_i3 finite_children_work_598_i3 (3, 6)
    required_598_i3 envelope_598_i3 pivot_mem_598_i3 child_required_sub_598_i3 child_envelope_sub_598_i3 ?_
  intro b hb
  exact common_sub_598_i3 (mem_commonEnvelope childrenD_598_i3 b hb)

theorem finite_children_work_598_i8 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_598_i8 j) (childrenD_598_i8 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (6, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_413 3 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_598_i8 : FiniteTemplate HasSnaky 6 required_598_i8 envelope_598_i8 := by
  refine finite_compose HasSnaky 5 childrenC_598_i8 childrenD_598_i8 finite_children_work_598_i8 (5, 5)
    required_598_i8 envelope_598_i8 pivot_mem_598_i8 child_required_sub_598_i8 child_envelope_sub_598_i8 ?_
  intro b hb
  exact common_sub_598_i8 (mem_commonEnvelope childrenD_598_i8 b hb)

theorem finite_children_work_598_i7 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_598_i7 j) (childrenD_598_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (3, 8)).mono (by decide +kernel)
  · exact finite_row_works_598_i8.mono (by decide +kernel)

theorem finite_row_works_598_i7 : FiniteTemplate HasSnaky 7 required_598_i7 envelope_598_i7 := by
  refine finite_compose HasSnaky 6 childrenC_598_i7 childrenD_598_i7 finite_children_work_598_i7 (4, 5)
    required_598_i7 envelope_598_i7 pivot_mem_598_i7 child_required_sub_598_i7 child_envelope_sub_598_i7 ?_
  intro b hb
  exact common_sub_598_i7 (mem_commonEnvelope childrenD_598_i7 b hb)

theorem finite_children_work_598_i6 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_598_i6 j) (childrenD_598_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 4)).mono (by decide +kernel)
  · exact finite_row_works_598_i7.mono (by decide +kernel)

theorem finite_row_works_598_i6 : FiniteTemplate HasSnaky 8 required_598_i6 envelope_598_i6 := by
  refine finite_compose HasSnaky 7 childrenC_598_i6 childrenD_598_i6 finite_children_work_598_i6 (3, 6)
    required_598_i6 envelope_598_i6 pivot_mem_598_i6 child_required_sub_598_i6 child_envelope_sub_598_i6 ?_
  intro b hb
  exact common_sub_598_i6 (mem_commonEnvelope childrenD_598_i6 b hb)

theorem finite_children_work_598 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_598 j) (childrenD_598 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_598_i0.mono (by decide +kernel)
  · exact finite_row_works_598_i3.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_584 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_591 4 (2, 10)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_594 2 (8, 1)).mono (by decide +kernel)
  · exact finite_row_works_598_i6.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_597 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_598 : FiniteTemplate HasSnaky 14 required_598 envelope_598 := by
  refine finite_compose HasSnaky 13 childrenC_598 childrenD_598 finite_children_work_598 (3, 5)
    required_598 envelope_598 pivot_mem_598 child_required_sub_598 child_envelope_sub_598 ?_
  intro b hb
  exact common_sub_598 (mem_commonEnvelope childrenD_598 b hb)

theorem finite_children_work_636_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_636_i1 j) (childrenD_636_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_22 7 (5, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_108 6 (5, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_512 0 (2, 1)).mono (by decide +kernel)

theorem finite_row_works_636_i1 : FiniteTemplate HasSnaky 10 required_636_i1 envelope_636_i1 := by
  refine finite_compose HasSnaky 9 childrenC_636_i1 childrenD_636_i1 finite_children_work_636_i1 (3, 5)
    required_636_i1 envelope_636_i1 pivot_mem_636_i1 child_required_sub_636_i1 child_envelope_sub_636_i1 ?_
  intro b hb
  exact common_sub_636_i1 (mem_commonEnvelope childrenD_636_i1 b hb)

theorem finite_children_work_636_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_636_i2 j) (childrenD_636_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 6 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_63 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_117 3 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_636_i2 : FiniteTemplate HasSnaky 8 required_636_i2 envelope_636_i2 := by
  refine finite_compose HasSnaky 7 childrenC_636_i2 childrenD_636_i2 finite_children_work_636_i2 (4, 6)
    required_636_i2 envelope_636_i2 pivot_mem_636_i2 child_required_sub_636_i2 child_envelope_sub_636_i2 ?_
  intro b hb
  exact common_sub_636_i2 (mem_commonEnvelope childrenD_636_i2 b hb)

theorem finite_children_work_636_i5 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_636_i5 j) (childrenD_636_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_85 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_164 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_262 4 (2, 7)).mono (by decide +kernel)

theorem finite_row_works_636_i5 : FiniteTemplate HasSnaky 7 required_636_i5 envelope_636_i5 := by
  refine finite_compose HasSnaky 6 childrenC_636_i5 childrenD_636_i5 finite_children_work_636_i5 (5, 5)
    required_636_i5 envelope_636_i5 pivot_mem_636_i5 child_required_sub_636_i5 child_envelope_sub_636_i5 ?_
  intro b hb
  exact common_sub_636_i5 (mem_commonEnvelope childrenD_636_i5 b hb)

theorem finite_children_work_636_i4 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_636_i4 j) (childrenD_636_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_1 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_636_i5.mono (by decide +kernel)

theorem finite_row_works_636_i4 : FiniteTemplate HasSnaky 8 required_636_i4 envelope_636_i4 := by
  refine finite_compose HasSnaky 7 childrenC_636_i4 childrenD_636_i4 finite_children_work_636_i4 (3, 5)
    required_636_i4 envelope_636_i4 pivot_mem_636_i4 child_required_sub_636_i4 child_envelope_sub_636_i4 ?_
  intro b hb
  exact common_sub_636_i4 (mem_commonEnvelope childrenD_636_i4 b hb)

theorem finite_children_work_636_i6 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_636_i6 j) (childrenD_636_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 1 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_331 2 (6, 1)).mono (by decide +kernel)

theorem finite_row_works_636_i6 : FiniteTemplate HasSnaky 7 required_636_i6 envelope_636_i6 := by
  refine finite_compose HasSnaky 6 childrenC_636_i6 childrenD_636_i6 finite_children_work_636_i6 (6, 4)
    required_636_i6 envelope_636_i6 pivot_mem_636_i6 child_required_sub_636_i6 child_envelope_sub_636_i6 ?_
  intro b hb
  exact common_sub_636_i6 (mem_commonEnvelope childrenD_636_i6 b hb)

theorem finite_children_work_636_i3 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_636_i3 j) (childrenD_636_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_332 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_474 4 (2, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_522 0 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_636_i4.mono (by decide +kernel)
  · exact finite_row_works_636_i6.mono (by decide +kernel)

theorem finite_row_works_636_i3 : FiniteTemplate HasSnaky 10 required_636_i3 envelope_636_i3 := by
  refine finite_compose HasSnaky 9 childrenC_636_i3 childrenD_636_i3 finite_children_work_636_i3 (5, 4)
    required_636_i3 envelope_636_i3 pivot_mem_636_i3 child_required_sub_636_i3 child_envelope_sub_636_i3 ?_
  intro b hb
  exact common_sub_636_i3 (mem_commonEnvelope childrenD_636_i3 b hb)

theorem finite_children_work_636_i0 : ∀ j, FiniteTemplate HasSnaky 12 (childrenC_636_i0 j) (childrenD_636_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_399 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_408 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_475 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_509 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_587 0 (2, 1)).mono (by decide +kernel)
  · exact finite_row_works_636_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_635 4 (2, 9)).mono (by decide +kernel)
  · exact finite_row_works_636_i2.mono (by decide +kernel)
  · exact finite_row_works_636_i3.mono (by decide +kernel)

theorem finite_row_works_636_i0 : FiniteTemplate HasSnaky 13 required_636_i0 envelope_636_i0 := by
  refine finite_compose HasSnaky 12 childrenC_636_i0 childrenD_636_i0 finite_children_work_636_i0 (4, 5)
    required_636_i0 envelope_636_i0 pivot_mem_636_i0 child_required_sub_636_i0 child_envelope_sub_636_i0 ?_
  intro b hb
  exact common_sub_636_i0 (mem_commonEnvelope childrenD_636_i0 b hb)

theorem finite_children_work_636_i7 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_636_i7 j) (childrenD_636_i7 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_118 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_188 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_192 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_193 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_396 5 (8, 2)).mono (by decide +kernel)

theorem finite_row_works_636_i7 : FiniteTemplate HasSnaky 10 required_636_i7 envelope_636_i7 := by
  refine finite_compose HasSnaky 9 childrenC_636_i7 childrenD_636_i7 finite_children_work_636_i7 (5, 4)
    required_636_i7 envelope_636_i7 pivot_mem_636_i7 child_required_sub_636_i7 child_envelope_sub_636_i7 ?_
  intro b hb
  exact common_sub_636_i7 (mem_commonEnvelope childrenD_636_i7 b hb)

theorem finite_children_work_636 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_636 j) (childrenD_636 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_125 3 (0, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_454 5 (5, 3)).mono (by decide +kernel)
  · exact finite_row_works_636_i0.mono (by decide +kernel)
  · exact finite_row_works_636_i7.mono (by decide +kernel)

theorem finite_row_works_636 : FiniteTemplate HasSnaky 14 required_636 envelope_636 := by
  refine finite_compose HasSnaky 13 childrenC_636 childrenD_636 finite_children_work_636 (3, 4)
    required_636 envelope_636 pivot_mem_636 child_required_sub_636 child_envelope_sub_636 ?_
  intro b hb
  exact common_sub_636 (mem_commonEnvelope childrenD_636 b hb)

theorem finite_children_work_644_i1 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_644_i1 j) (childrenD_644_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_317 0 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_640 4 (2, 8)).mono (by decide +kernel)

theorem finite_row_works_644_i1 : FiniteTemplate HasSnaky 10 required_644_i1 envelope_644_i1 := by
  refine finite_compose HasSnaky 9 childrenC_644_i1 childrenD_644_i1 finite_children_work_644_i1 (5, 5)
    required_644_i1 envelope_644_i1 pivot_mem_644_i1 child_required_sub_644_i1 child_envelope_sub_644_i1 ?_
  intro b hb
  exact common_sub_644_i1 (mem_commonEnvelope childrenD_644_i1 b hb)

theorem finite_children_work_644_i0 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_644_i0 j) (childrenD_644_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_104 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_359 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_452 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_476 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_479 0 (3, 1)).mono (by decide +kernel)
  · exact finite_row_works_644_i1.mono (by decide +kernel)

theorem finite_row_works_644_i0 : FiniteTemplate HasSnaky 11 required_644_i0 envelope_644_i0 := by
  refine finite_compose HasSnaky 10 childrenC_644_i0 childrenD_644_i0 finite_children_work_644_i0 (6, 5)
    required_644_i0 envelope_644_i0 pivot_mem_644_i0 child_required_sub_644_i0 child_envelope_sub_644_i0 ?_
  intro b hb
  exact common_sub_644_i0 (mem_commonEnvelope childrenD_644_i0 b hb)

theorem finite_children_work_644 : ∀ j, FiniteTemplate HasSnaky 13 (childrenC_644 j) (childrenD_644 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_120 6 (7, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_338 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_437 3 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_611 3 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_613 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_634 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_644_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_642 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_643 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_644 : FiniteTemplate HasSnaky 14 required_644 envelope_644 := by
  refine finite_compose HasSnaky 13 childrenC_644 childrenD_644 finite_children_work_644 (6, 4)
    required_644 envelope_644 pivot_mem_644 child_required_sub_644 child_envelope_sub_644 ?_
  intro b hb
  exact common_sub_644 (mem_commonEnvelope childrenD_644 b hb)

end FiniteCongruenceChecks.SnakyFinite
