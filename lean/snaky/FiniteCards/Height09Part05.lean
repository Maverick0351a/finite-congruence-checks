/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height09Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height06Part01
import FiniteCards.Height06Part02
import FiniteCards.Height06Part04
import FiniteCards.Height06Part05
import FiniteCards.Height07Part02
import FiniteCards.Height08Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_574_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_574_i1 j) (childrenD_574_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_43 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_64 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_574_i1 : FiniteTemplate HasSnaky 4 required_574_i1 envelope_574_i1 := by
  refine finite_compose HasSnaky 3 childrenC_574_i1 childrenD_574_i1 finite_children_work_574_i1 (3, 3)
    required_574_i1 envelope_574_i1 pivot_mem_574_i1 child_required_sub_574_i1 child_envelope_sub_574_i1 ?_
  intro b hb
  exact common_sub_574_i1 (mem_commonEnvelope childrenD_574_i1 b hb)

theorem finite_children_work_574_i3 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_574_i3 j) (childrenD_574_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_223 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_574_i3 : FiniteTemplate HasSnaky 4 required_574_i3 envelope_574_i3 := by
  refine finite_compose HasSnaky 3 childrenC_574_i3 childrenD_574_i3 finite_children_work_574_i3 (4, 4)
    required_574_i3 envelope_574_i3 pivot_mem_574_i3 child_required_sub_574_i3 child_envelope_sub_574_i3 ?_
  intro b hb
  exact common_sub_574_i3 (mem_commonEnvelope childrenD_574_i3 b hb)

theorem finite_children_work_574_i2 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_574_i2 j) (childrenD_574_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_574_i3.mono (by decide +kernel)

theorem finite_row_works_574_i2 : FiniteTemplate HasSnaky 5 required_574_i2 envelope_574_i2 := by
  refine finite_compose HasSnaky 4 childrenC_574_i2 childrenD_574_i2 finite_children_work_574_i2 (4, 2)
    required_574_i2 envelope_574_i2 pivot_mem_574_i2 child_required_sub_574_i2 child_envelope_sub_574_i2 ?_
  intro b hb
  exact common_sub_574_i2 (mem_commonEnvelope childrenD_574_i2 b hb)

theorem finite_children_work_574_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_574_i5 j) (childrenD_574_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_236 6 (5, 6)).mono (by decide +kernel)

theorem finite_row_works_574_i5 : FiniteTemplate HasSnaky 4 required_574_i5 envelope_574_i5 := by
  refine finite_compose HasSnaky 3 childrenC_574_i5 childrenD_574_i5 finite_children_work_574_i5 (4, 2)
    required_574_i5 envelope_574_i5 pivot_mem_574_i5 child_required_sub_574_i5 child_envelope_sub_574_i5 ?_
  intro b hb
  exact common_sub_574_i5 (mem_commonEnvelope childrenD_574_i5 b hb)

theorem finite_children_work_574_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_574_i4 j) (childrenD_574_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_18 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_61 6 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_574_i5.mono (by decide +kernel)

theorem finite_row_works_574_i4 : FiniteTemplate HasSnaky 5 required_574_i4 envelope_574_i4 := by
  refine finite_compose HasSnaky 4 childrenC_574_i4 childrenD_574_i4 finite_children_work_574_i4 (4, 4)
    required_574_i4 envelope_574_i4 pivot_mem_574_i4 child_required_sub_574_i4 child_envelope_sub_574_i4 ?_
  intro b hb
  exact common_sub_574_i4 (mem_commonEnvelope childrenD_574_i4 b hb)

theorem finite_children_work_574_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_574_i0 j) (childrenD_574_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_130 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_574_i1.mono (by decide +kernel)
  · exact finite_row_works_574_i2.mono (by decide +kernel)
  · exact finite_row_works_574_i4.mono (by decide +kernel)

theorem finite_row_works_574_i0 : FiniteTemplate HasSnaky 6 required_574_i0 envelope_574_i0 := by
  refine finite_compose HasSnaky 5 childrenC_574_i0 childrenD_574_i0 finite_children_work_574_i0 (3, 2)
    required_574_i0 envelope_574_i0 pivot_mem_574_i0 child_required_sub_574_i0 child_envelope_sub_574_i0 ?_
  intro b hb
  exact common_sub_574_i0 (mem_commonEnvelope childrenD_574_i0 b hb)

theorem finite_children_work_574 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_574 j) (childrenD_574 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_184 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_384 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_385 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_493 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_494 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_574_i0.mono (by decide +kernel)

theorem finite_row_works_574 : FiniteTemplate HasSnaky 9 required_574 envelope_574 := by
  refine finite_compose HasSnaky 8 childrenC_574 childrenD_574 finite_children_work_574 (4, 5)
    required_574 envelope_574 pivot_mem_574 child_required_sub_574 child_envelope_sub_574 ?_
  intro b hb
  exact common_sub_574 (mem_commonEnvelope childrenD_574 b hb)

theorem finite_children_work_577_i1 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_577_i1 j) (childrenD_577_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_393 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_577_i1 : FiniteTemplate HasSnaky 7 required_577_i1 envelope_577_i1 := by
  refine finite_compose HasSnaky 6 childrenC_577_i1 childrenD_577_i1 finite_children_work_577_i1 (3, 1)
    required_577_i1 envelope_577_i1 pivot_mem_577_i1 child_required_sub_577_i1 child_envelope_sub_577_i1 ?_
  intro b hb
  exact common_sub_577_i1 (mem_commonEnvelope childrenD_577_i1 b hb)

theorem finite_children_work_577_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_577_i0 j) (childrenD_577_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_577_i1.mono (by decide +kernel)

theorem finite_row_works_577_i0 : FiniteTemplate HasSnaky 8 required_577_i0 envelope_577_i0 := by
  refine finite_compose HasSnaky 7 childrenC_577_i0 childrenD_577_i0 finite_children_work_577_i0 (3, 3)
    required_577_i0 envelope_577_i0 pivot_mem_577_i0 child_required_sub_577_i0 child_envelope_sub_577_i0 ?_
  intro b hb
  exact common_sub_577_i0 (mem_commonEnvelope childrenD_577_i0 b hb)

theorem finite_children_work_577 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_577 j) (childrenD_577 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_577_i0.mono (by decide +kernel)

theorem finite_row_works_577 : FiniteTemplate HasSnaky 9 required_577 envelope_577 := by
  refine finite_compose HasSnaky 8 childrenC_577 childrenD_577 finite_children_work_577 (4, 3)
    required_577 envelope_577 pivot_mem_577 child_required_sub_577 child_envelope_sub_577 ?_
  intro b hb
  exact common_sub_577 (mem_commonEnvelope childrenD_577 b hb)

theorem finite_children_work_584_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_584_i1 j) (childrenD_584_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_121 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_584_i1 : FiniteTemplate HasSnaky 3 required_584_i1 envelope_584_i1 := by
  refine finite_compose HasSnaky 2 childrenC_584_i1 childrenD_584_i1 finite_children_work_584_i1 (4, 1)
    required_584_i1 envelope_584_i1 pivot_mem_584_i1 child_required_sub_584_i1 child_envelope_sub_584_i1 ?_
  intro b hb
  exact common_sub_584_i1 (mem_commonEnvelope childrenD_584_i1 b hb)

theorem finite_children_work_584_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_584_i2 j) (childrenD_584_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact finite_row_works_203.mono (by decide +kernel)

theorem finite_row_works_584_i2 : FiniteTemplate HasSnaky 7 required_584_i2 envelope_584_i2 := by
  refine finite_compose HasSnaky 6 childrenC_584_i2 childrenD_584_i2 finite_children_work_584_i2 (1, 2)
    required_584_i2 envelope_584_i2 pivot_mem_584_i2 child_required_sub_584_i2 child_envelope_sub_584_i2 ?_
  intro b hb
  exact common_sub_584_i2 (mem_commonEnvelope childrenD_584_i2 b hb)

theorem finite_children_work_584_i0 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_584_i0 j) (childrenD_584_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_584_i1.mono (by decide +kernel)
  · exact finite_row_works_584_i2.mono (by decide +kernel)

theorem finite_row_works_584_i0 : FiniteTemplate HasSnaky 8 required_584_i0 envelope_584_i0 := by
  refine finite_compose HasSnaky 7 childrenC_584_i0 childrenD_584_i0 finite_children_work_584_i0 (3, 4)
    required_584_i0 envelope_584_i0 pivot_mem_584_i0 child_required_sub_584_i0 child_envelope_sub_584_i0 ?_
  intro b hb
  exact common_sub_584_i0 (mem_commonEnvelope childrenD_584_i0 b hb)

theorem finite_children_work_584 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_584 j) (childrenD_584 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_584_i0.mono (by decide +kernel)

theorem finite_row_works_584 : FiniteTemplate HasSnaky 9 required_584 envelope_584 := by
  refine finite_compose HasSnaky 8 childrenC_584 childrenD_584 finite_children_work_584 (2, 1)
    required_584 envelope_584 pivot_mem_584 child_required_sub_584 child_envelope_sub_584 ?_
  intro b hb
  exact common_sub_584 (mem_commonEnvelope childrenD_584 b hb)

end FiniteCongruenceChecks.SnakyFinite
