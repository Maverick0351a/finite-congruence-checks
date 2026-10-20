/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part06
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height06Part01
import FiniteCards.Height06Part03
import FiniteCards.Height06Part04
import FiniteCards.Height07Part01
import FiniteCards.Height08Part01
import FiniteCards.Height09Part05
import FiniteCards.Height09Part07
import FiniteCards.Height09Part08
import FiniteCards.Height10Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_689_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_689_i0 j) (childrenD_689_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_67 2 (5, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_175 6 (5, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_228 1 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_373 5 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (7, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_688 1 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_689_i0 : FiniteTemplate HasSnaky 10 required_689_i0 envelope_689_i0 := by
  refine finite_compose HasSnaky 9 childrenC_689_i0 childrenD_689_i0 finite_children_work_689_i0 (4, 6)
    required_689_i0 envelope_689_i0 pivot_mem_689_i0 child_required_sub_689_i0 child_envelope_sub_689_i0 ?_
  intro b hb
  exact common_sub_689_i0 (mem_commonEnvelope childrenD_689_i0 b hb)

theorem finite_children_work_689 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_689 j) (childrenD_689 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_44 1 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_324 2 (5, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_686 0 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_689_i0.mono (by decide +kernel)

theorem finite_row_works_689 : FiniteTemplate HasSnaky 11 required_689 envelope_689 := by
  refine finite_compose HasSnaky 10 childrenC_689 childrenD_689 finite_children_work_689 (4, 5)
    required_689 envelope_689 pivot_mem_689 child_required_sub_689 child_envelope_sub_689 ?_
  intro b hb
  exact common_sub_689 (mem_commonEnvelope childrenD_689 b hb)

theorem finite_children_work_700_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_700_i0 j) (childrenD_700_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_39 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_700_i0 : FiniteTemplate HasSnaky 5 required_700_i0 envelope_700_i0 := by
  refine finite_compose HasSnaky 4 childrenC_700_i0 childrenD_700_i0 finite_children_work_700_i0 (2, 5)
    required_700_i0 envelope_700_i0 pivot_mem_700_i0 child_required_sub_700_i0 child_envelope_sub_700_i0 ?_
  intro b hb
  exact common_sub_700_i0 (mem_commonEnvelope childrenD_700_i0 b hb)

theorem finite_children_work_700_i3 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_700_i3 j) (childrenD_700_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_197 4 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_700_i3 : FiniteTemplate HasSnaky 6 required_700_i3 envelope_700_i3 := by
  refine finite_compose HasSnaky 5 childrenC_700_i3 childrenD_700_i3 finite_children_work_700_i3 (3, 5)
    required_700_i3 envelope_700_i3 pivot_mem_700_i3 child_required_sub_700_i3 child_envelope_sub_700_i3 ?_
  intro b hb
  exact common_sub_700_i3 (mem_commonEnvelope childrenD_700_i3 b hb)

theorem finite_children_work_700_i2 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_700_i2 j) (childrenD_700_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (1, 2)).mono (by decide +kernel)
  · exact finite_row_works_700_i3.mono (by decide +kernel)

theorem finite_row_works_700_i2 : FiniteTemplate HasSnaky 7 required_700_i2 envelope_700_i2 := by
  refine finite_compose HasSnaky 6 childrenC_700_i2 childrenD_700_i2 finite_children_work_700_i2 (2, 5)
    required_700_i2 envelope_700_i2 pivot_mem_700_i2 child_required_sub_700_i2 child_envelope_sub_700_i2 ?_
  intro b hb
  exact common_sub_700_i2 (mem_commonEnvelope childrenD_700_i2 b hb)

theorem finite_children_work_700_i1 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_700_i1 j) (childrenD_700_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_61 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_348 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_700_i2.mono (by decide +kernel)

theorem finite_row_works_700_i1 : FiniteTemplate HasSnaky 8 required_700_i1 envelope_700_i1 := by
  refine finite_compose HasSnaky 7 childrenC_700_i1 childrenD_700_i1 finite_children_work_700_i1 (2, 6)
    required_700_i1 envelope_700_i1 pivot_mem_700_i1 child_required_sub_700_i1 child_envelope_sub_700_i1 ?_
  intro b hb
  exact common_sub_700_i1 (mem_commonEnvelope childrenD_700_i1 b hb)

theorem finite_children_work_700_i5 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_700_i5 j) (childrenD_700_i5 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 3 (3, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 4 (3, 7)).mono (by decide +kernel)

theorem finite_row_works_700_i5 : FiniteTemplate HasSnaky 4 required_700_i5 envelope_700_i5 := by
  refine finite_compose HasSnaky 3 childrenC_700_i5 childrenD_700_i5 finite_children_work_700_i5 (4, 4)
    required_700_i5 envelope_700_i5 pivot_mem_700_i5 child_required_sub_700_i5 child_envelope_sub_700_i5 ?_
  intro b hb
  exact common_sub_700_i5 (mem_commonEnvelope childrenD_700_i5 b hb)

theorem finite_children_work_700_i6 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_700_i6 j) (childrenD_700_i6 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_40 1 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_700_i6 : FiniteTemplate HasSnaky 4 required_700_i6 envelope_700_i6 := by
  refine finite_compose HasSnaky 3 childrenC_700_i6 childrenD_700_i6 finite_children_work_700_i6 (2, 5)
    required_700_i6 envelope_700_i6 pivot_mem_700_i6 child_required_sub_700_i6 child_envelope_sub_700_i6 ?_
  intro b hb
  exact common_sub_700_i6 (mem_commonEnvelope childrenD_700_i6 b hb)

theorem finite_children_work_700_i4 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_700_i4 j) (childrenD_700_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_304 6 (5, 8)).mono (by decide +kernel)
  · exact finite_row_works_700_i5.mono (by decide +kernel)
  · exact finite_row_works_700_i6.mono (by decide +kernel)

theorem finite_row_works_700_i4 : FiniteTemplate HasSnaky 5 required_700_i4 envelope_700_i4 := by
  refine finite_compose HasSnaky 4 childrenC_700_i4 childrenD_700_i4 finite_children_work_700_i4 (4, 6)
    required_700_i4 envelope_700_i4 pivot_mem_700_i4 child_required_sub_700_i4 child_envelope_sub_700_i4 ?_
  intro b hb
  exact common_sub_700_i4 (mem_commonEnvelope childrenD_700_i4 b hb)

theorem finite_children_work_700 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_700 j) (childrenD_700 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_204 4 (0, 8)).mono (by decide +kernel)
  · exact finite_row_works_700_i0.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_460 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_700_i1.mono (by decide +kernel)
  · exact finite_row_works_700_i4.mono (by decide +kernel)

theorem finite_row_works_700 : FiniteTemplate HasSnaky 11 required_700 envelope_700 := by
  refine finite_compose HasSnaky 10 childrenC_700 childrenD_700 finite_children_work_700 (4, 5)
    required_700 envelope_700 pivot_mem_700 child_required_sub_700 child_envelope_sub_700 ?_
  intro b hb
  exact common_sub_700 (mem_commonEnvelope childrenD_700 b hb)

theorem finite_children_work_710_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_710_i1 j) (childrenD_710_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (3, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_196 3 (2, 6)).mono (by decide +kernel)

theorem finite_row_works_710_i1 : FiniteTemplate HasSnaky 5 required_710_i1 envelope_710_i1 := by
  refine finite_compose HasSnaky 4 childrenC_710_i1 childrenD_710_i1 finite_children_work_710_i1 (3, 2)
    required_710_i1 envelope_710_i1 pivot_mem_710_i1 child_required_sub_710_i1 child_envelope_sub_710_i1 ?_
  intro b hb
  exact common_sub_710_i1 (mem_commonEnvelope childrenD_710_i1 b hb)

theorem finite_children_work_710_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_710_i0 j) (childrenD_710_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_115 3 (0, 6)).mono (by decide +kernel)
  · exact finite_row_works_710_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_577 1 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_710_i0 : FiniteTemplate HasSnaky 10 required_710_i0 envelope_710_i0 := by
  refine finite_compose HasSnaky 9 childrenC_710_i0 childrenD_710_i0 finite_children_work_710_i0 (3, 3)
    required_710_i0 envelope_710_i0 pivot_mem_710_i0 child_required_sub_710_i0 child_envelope_sub_710_i0 ?_
  intro b hb
  exact common_sub_710_i0 (mem_commonEnvelope childrenD_710_i0 b hb)

theorem finite_children_work_710 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_710 j) (childrenD_710 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_117 1 (0, 3)).mono (by decide +kernel)
  · exact finite_row_works_710_i0.mono (by decide +kernel)

theorem finite_row_works_710 : FiniteTemplate HasSnaky 11 required_710 envelope_710 := by
  refine finite_compose HasSnaky 10 childrenC_710 childrenD_710 finite_children_work_710 (3, 6)
    required_710 envelope_710 pivot_mem_710 child_required_sub_710 child_envelope_sub_710 ?_
  intro b hb
  exact common_sub_710 (mem_commonEnvelope childrenD_710 b hb)

theorem finite_children_work_716_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_716_i0 j) (childrenD_716_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_55 0 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_659 2 (7, 0)).mono (by decide +kernel)

theorem finite_row_works_716_i0 : FiniteTemplate HasSnaky 10 required_716_i0 envelope_716_i0 := by
  refine finite_compose HasSnaky 9 childrenC_716_i0 childrenD_716_i0 finite_children_work_716_i0 (6, 4)
    required_716_i0 envelope_716_i0 pivot_mem_716_i0 child_required_sub_716_i0 child_envelope_sub_716_i0 ?_
  intro b hb
  exact common_sub_716_i0 (mem_commonEnvelope childrenD_716_i0 b hb)

theorem finite_children_work_716 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_716 j) (childrenD_716 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_49 4 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_142 0 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_716_i0.mono (by decide +kernel)

theorem finite_row_works_716 : FiniteTemplate HasSnaky 11 required_716 envelope_716 := by
  refine finite_compose HasSnaky 10 childrenC_716 childrenD_716 finite_children_work_716 (7, 5)
    required_716 envelope_716 pivot_mem_716 child_required_sub_716 child_envelope_sub_716 ?_
  intro b hb
  exact common_sub_716 (mem_commonEnvelope childrenD_716 b hb)

end FiniteCongruenceChecks.SnakyFinite
