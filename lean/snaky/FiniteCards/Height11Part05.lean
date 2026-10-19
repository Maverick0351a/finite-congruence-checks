/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height11Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03
import FiniteCards.Height04Part04
import FiniteCards.Height05Part01
import FiniteCards.Height05Part02
import FiniteCards.Height05Part03
import FiniteCards.Height05Part05
import FiniteCards.Height06Part01
import FiniteCards.Height06Part04
import FiniteCards.Height06Part06
import FiniteCards.Height07Part01
import FiniteCards.Height07Part02
import FiniteCards.Height07Part03
import FiniteCards.Height07Part05
import FiniteCards.Height08Part01
import FiniteCards.Height08Part02
import FiniteCards.Height08Part03
import FiniteCards.Height09Part01
import FiniteCards.Height09Part03
import FiniteCards.Height09Part04
import FiniteCards.Height09Part07
import FiniteCards.Height10Part01
import FiniteCards.Height10Part04
import FiniteCards.Height10Part06

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_639_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_639_i2 j) (childrenD_639_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_21 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 2 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_62 6 (4, 7)).mono (by decide +kernel)

theorem finite_row_works_639_i2 : FiniteTemplate HasSnaky 4 required_639_i2 envelope_639_i2 := by
  refine finite_compose HasSnaky 3 childrenC_639_i2 childrenD_639_i2 finite_children_work_639_i2 (3, 6)
    required_639_i2 envelope_639_i2 pivot_mem_639_i2 child_required_sub_639_i2 child_envelope_sub_639_i2 ?_
  intro b hb
  exact common_sub_639_i2 (mem_commonEnvelope childrenD_639_i2 b hb)

theorem finite_children_work_639_i1 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_639_i1 j) (childrenD_639_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact finite_row_works_639_i2.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_451 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_639_i1 : FiniteTemplate HasSnaky 6 required_639_i1 envelope_639_i1 := by
  refine finite_compose HasSnaky 5 childrenC_639_i1 childrenD_639_i1 finite_children_work_639_i1 (3, 5)
    required_639_i1 envelope_639_i1 pivot_mem_639_i1 child_required_sub_639_i1 child_envelope_sub_639_i1 ?_
  intro b hb
  exact common_sub_639_i1 (mem_commonEnvelope childrenD_639_i1 b hb)

theorem finite_children_work_639_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_639_i3 j) (childrenD_639_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_71 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_73 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 5 (6, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_451 6 (4, 6)).mono (by decide +kernel)

theorem finite_row_works_639_i3 : FiniteTemplate HasSnaky 7 required_639_i3 envelope_639_i3 := by
  refine finite_compose HasSnaky 6 childrenC_639_i3 childrenD_639_i3 finite_children_work_639_i3 (3, 5)
    required_639_i3 envelope_639_i3 pivot_mem_639_i3 child_required_sub_639_i3 child_envelope_sub_639_i3 ?_
  intro b hb
  exact common_sub_639_i3 (mem_commonEnvelope childrenD_639_i3 b hb)

theorem finite_children_work_639_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_639_i0 j) (childrenD_639_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_54 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_638 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_639_i1.mono (by decide +kernel)
  · exact finite_row_works_639_i3.mono (by decide +kernel)

theorem finite_row_works_639_i0 : FiniteTemplate HasSnaky 10 required_639_i0 envelope_639_i0 := by
  refine finite_compose HasSnaky 9 childrenC_639_i0 childrenD_639_i0 finite_children_work_639_i0 (3, 3)
    required_639_i0 envelope_639_i0 pivot_mem_639_i0 child_required_sub_639_i0 child_envelope_sub_639_i0 ?_
  intro b hb
  exact common_sub_639_i0 (mem_commonEnvelope childrenD_639_i0 b hb)

theorem finite_children_work_639 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_639 j) (childrenD_639 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_50 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_125 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_478 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_482 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_639_i0.mono (by decide +kernel)

theorem finite_row_works_639 : FiniteTemplate HasSnaky 11 required_639 envelope_639 := by
  refine finite_compose HasSnaky 10 childrenC_639 childrenD_639 finite_children_work_639 (3, 4)
    required_639 envelope_639 pivot_mem_639 child_required_sub_639 child_envelope_sub_639 ?_
  intro b hb
  exact common_sub_639 (mem_commonEnvelope childrenD_639 b hb)

theorem finite_children_work_646_i0 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_646_i0 j) (childrenD_646_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_72 1 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_262 7 (6, 5)).mono (by decide +kernel)

theorem finite_row_works_646_i0 : FiniteTemplate HasSnaky 6 required_646_i0 envelope_646_i0 := by
  refine finite_compose HasSnaky 5 childrenC_646_i0 childrenD_646_i0 finite_children_work_646_i0 (4, 2)
    required_646_i0 envelope_646_i0 pivot_mem_646_i0 child_required_sub_646_i0 child_envelope_sub_646_i0 ?_
  intro b hb
  exact common_sub_646_i0 (mem_commonEnvelope childrenD_646_i0 b hb)

theorem finite_children_work_646 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_646 j) (childrenD_646 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_361 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_361 5 (6, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_411 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_600 5 (7, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_621 3 (0, 7)).mono (by decide +kernel)
  · exact finite_row_works_646_i0.mono (by decide +kernel)

theorem finite_row_works_646 : FiniteTemplate HasSnaky 11 required_646 envelope_646 := by
  refine finite_compose HasSnaky 10 childrenC_646 childrenD_646 finite_children_work_646 (4, 4)
    required_646 envelope_646 pivot_mem_646 child_required_sub_646 child_envelope_sub_646 ?_
  intro b hb
  exact common_sub_646 (mem_commonEnvelope childrenD_646 b hb)

theorem finite_children_work_653_i0 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_653_i0 j) (childrenD_653_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_206 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_301 0 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_405 5 (5, 3)).mono (by decide +kernel)

theorem finite_row_works_653_i0 : FiniteTemplate HasSnaky 9 required_653_i0 envelope_653_i0 := by
  refine finite_compose HasSnaky 8 childrenC_653_i0 childrenD_653_i0 finite_children_work_653_i0 (4, 4)
    required_653_i0 envelope_653_i0 pivot_mem_653_i0 child_required_sub_653_i0 child_envelope_sub_653_i0 ?_
  intro b hb
  exact common_sub_653_i0 (mem_commonEnvelope childrenD_653_i0 b hb)

theorem finite_children_work_653 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_653 j) (childrenD_653 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_53 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 5 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_652 0 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_653_i0.mono (by decide +kernel)

theorem finite_row_works_653 : FiniteTemplate HasSnaky 11 required_653 envelope_653 := by
  refine finite_compose HasSnaky 10 childrenC_653 childrenD_653 finite_children_work_653 (2, 4)
    required_653 envelope_653 pivot_mem_653 child_required_sub_653 child_envelope_sub_653 ?_
  intro b hb
  exact common_sub_653 (mem_commonEnvelope childrenD_653 b hb)

theorem finite_children_work_660_i1 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_660_i1 j) (childrenD_660_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 5 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 1 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_660_i1 : FiniteTemplate HasSnaky 5 required_660_i1 envelope_660_i1 := by
  refine finite_compose HasSnaky 4 childrenC_660_i1 childrenD_660_i1 finite_children_work_660_i1 (7, 5)
    required_660_i1 envelope_660_i1 pivot_mem_660_i1 child_required_sub_660_i1 child_envelope_sub_660_i1 ?_
  intro b hb
  exact common_sub_660_i1 (mem_commonEnvelope childrenD_660_i1 b hb)

theorem finite_children_work_660_i2 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_660_i2 j) (childrenD_660_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 5 (7, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_252 0 (3, 2)).mono (by decide +kernel)

theorem finite_row_works_660_i2 : FiniteTemplate HasSnaky 6 required_660_i2 envelope_660_i2 := by
  refine finite_compose HasSnaky 5 childrenC_660_i2 childrenD_660_i2 finite_children_work_660_i2 (7, 5)
    required_660_i2 envelope_660_i2 pivot_mem_660_i2 child_required_sub_660_i2 child_envelope_sub_660_i2 ?_
  intro b hb
  exact common_sub_660_i2 (mem_commonEnvelope childrenD_660_i2 b hb)

theorem finite_children_work_660_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_660_i0 j) (childrenD_660_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 3 (2, 6)).mono (by decide +kernel)
  · exact finite_row_works_660_i1.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_659 0 (3, 0)).mono (by decide +kernel)
  · exact finite_row_works_660_i2.mono (by decide +kernel)

theorem finite_row_works_660_i0 : FiniteTemplate HasSnaky 10 required_660_i0 envelope_660_i0 := by
  refine finite_compose HasSnaky 9 childrenC_660_i0 childrenD_660_i0 finite_children_work_660_i0 (6, 5)
    required_660_i0 envelope_660_i0 pivot_mem_660_i0 child_required_sub_660_i0 child_envelope_sub_660_i0 ?_
  intro b hb
  exact common_sub_660_i0 (mem_commonEnvelope childrenD_660_i0 b hb)

theorem finite_children_work_660 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_660 j) (childrenD_660 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_13 5 (7, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_137 2 (6, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_332 6 (6, 8)).mono (by decide +kernel)
  · exact finite_row_works_660_i0.mono (by decide +kernel)

theorem finite_row_works_660 : FiniteTemplate HasSnaky 11 required_660 envelope_660 := by
  refine finite_compose HasSnaky 10 childrenC_660 childrenD_660 finite_children_work_660 (3, 5)
    required_660 envelope_660 pivot_mem_660 child_required_sub_660 child_envelope_sub_660 ?_
  intro b hb
  exact common_sub_660 (mem_commonEnvelope childrenD_660 b hb)

theorem finite_children_work_663 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_663 j) (childrenD_663 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_134 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 4 (1, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (1, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_507 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 4 (2, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_562 4 (1, 9)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_580 0 (1, 3)).mono (by decide +kernel)
  · exact finite_row_works_662.mono (by decide +kernel)

theorem finite_row_works_663 : FiniteTemplate HasSnaky 11 required_663 envelope_663 := by
  refine finite_compose HasSnaky 10 childrenC_663 childrenD_663 finite_children_work_663 (4, 5)
    required_663 envelope_663 pivot_mem_663 child_required_sub_663 child_envelope_sub_663 ?_
  intro b hb
  exact common_sub_663 (mem_commonEnvelope childrenD_663 b hb)

theorem finite_children_work_664 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_664 j) (childrenD_664 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_134 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_180 4 (3, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_309 2 (7, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (3, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_558 4 (4, 7)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_580 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_662 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_664 : FiniteTemplate HasSnaky 11 required_664 envelope_664 := by
  refine finite_compose HasSnaky 10 childrenC_664 childrenD_664 finite_children_work_664 (6, 5)
    required_664 envelope_664 pivot_mem_664 child_required_sub_664 child_envelope_sub_664 ?_
  intro b hb
  exact common_sub_664 (mem_commonEnvelope childrenD_664 b hb)

theorem finite_children_work_676_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_676_i0 j) (childrenD_676_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_55 6 (4, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_380 0 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_676_i0 : FiniteTemplate HasSnaky 10 required_676_i0 envelope_676_i0 := by
  refine finite_compose HasSnaky 9 childrenC_676_i0 childrenD_676_i0 finite_children_work_676_i0 (2, 4)
    required_676_i0 envelope_676_i0 pivot_mem_676_i0 child_required_sub_676_i0 child_envelope_sub_676_i0 ?_
  intro b hb
  exact common_sub_676_i0 (mem_commonEnvelope childrenD_676_i0 b hb)

theorem finite_children_work_676 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_676 j) (childrenD_676 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 0 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_676_i0.mono (by decide +kernel)

theorem finite_row_works_676 : FiniteTemplate HasSnaky 11 required_676 envelope_676 := by
  refine finite_compose HasSnaky 10 childrenC_676 childrenD_676 finite_children_work_676 (4, 3)
    required_676 envelope_676 pivot_mem_676 child_required_sub_676 child_envelope_sub_676 ?_
  intro b hb
  exact common_sub_676 (mem_commonEnvelope childrenD_676 b hb)

theorem finite_children_work_685_i4 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_685_i4 j) (childrenD_685_i4 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_312 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_685_i4 : FiniteTemplate HasSnaky 6 required_685_i4 envelope_685_i4 := by
  refine finite_compose HasSnaky 5 childrenC_685_i4 childrenD_685_i4 finite_children_work_685_i4 (3, 1)
    required_685_i4 envelope_685_i4 pivot_mem_685_i4 child_required_sub_685_i4 child_envelope_sub_685_i4 ?_
  intro b hb
  exact common_sub_685_i4 (mem_commonEnvelope childrenD_685_i4 b hb)

theorem finite_children_work_685_i3 : ∀ j, FiniteTemplate HasSnaky 6 (childrenC_685_i3 j) (childrenD_685_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_685_i4.mono (by decide +kernel)

theorem finite_row_works_685_i3 : FiniteTemplate HasSnaky 7 required_685_i3 envelope_685_i3 := by
  refine finite_compose HasSnaky 6 childrenC_685_i3 childrenD_685_i3 finite_children_work_685_i3 (2, 1)
    required_685_i3 envelope_685_i3 pivot_mem_685_i3 child_required_sub_685_i3 child_envelope_sub_685_i3 ?_
  intro b hb
  exact common_sub_685_i3 (mem_commonEnvelope childrenD_685_i3 b hb)

theorem finite_children_work_685_i2 : ∀ j, FiniteTemplate HasSnaky 7 (childrenC_685_i2 j) (childrenD_685_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_351 4 (3, 6)).mono (by decide +kernel)
  · exact finite_row_works_685_i3.mono (by decide +kernel)

theorem finite_row_works_685_i2 : FiniteTemplate HasSnaky 8 required_685_i2 envelope_685_i2 := by
  refine finite_compose HasSnaky 7 childrenC_685_i2 childrenD_685_i2 finite_children_work_685_i2 (6, 2)
    required_685_i2 envelope_685_i2 pivot_mem_685_i2 child_required_sub_685_i2 child_envelope_sub_685_i2 ?_
  intro b hb
  exact common_sub_685_i2 (mem_commonEnvelope childrenD_685_i2 b hb)

theorem finite_children_work_685_i1 : ∀ j, FiniteTemplate HasSnaky 8 (childrenC_685_i1 j) (childrenD_685_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_96 1 (2, 2)).mono (by decide +kernel)
  · exact finite_row_works_685_i2.mono (by decide +kernel)

theorem finite_row_works_685_i1 : FiniteTemplate HasSnaky 9 required_685_i1 envelope_685_i1 := by
  refine finite_compose HasSnaky 8 childrenC_685_i1 childrenD_685_i1 finite_children_work_685_i1 (6, 4)
    required_685_i1 envelope_685_i1 pivot_mem_685_i1 child_required_sub_685_i1 child_envelope_sub_685_i1 ?_
  intro b hb
  exact common_sub_685_i1 (mem_commonEnvelope childrenD_685_i1 b hb)

theorem finite_children_work_685_i0 : ∀ j, FiniteTemplate HasSnaky 9 (childrenC_685_i0 j) (childrenD_685_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_685_i1.mono (by decide +kernel)

theorem finite_row_works_685_i0 : FiniteTemplate HasSnaky 10 required_685_i0 envelope_685_i0 := by
  refine finite_compose HasSnaky 9 childrenC_685_i0 childrenD_685_i0 finite_children_work_685_i0 (3, 2)
    required_685_i0 envelope_685_i0 pivot_mem_685_i0 child_required_sub_685_i0 child_envelope_sub_685_i0 ?_
  intro b hb
  exact common_sub_685_i0 (mem_commonEnvelope childrenD_685_i0 b hb)

theorem finite_children_work_685 : ∀ j, FiniteTemplate HasSnaky 10 (childrenC_685 j) (childrenD_685 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_67 3 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_175 7 (7, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_228 0 (2, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_435 4 (2, 8)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_531 0 (3, 2)).mono (by decide +kernel)
  · exact finite_row_works_685_i0.mono (by decide +kernel)

theorem finite_row_works_685 : FiniteTemplate HasSnaky 11 required_685 envelope_685 := by
  refine finite_compose HasSnaky 10 childrenC_685 childrenD_685 finite_children_work_685 (5, 5)
    required_685 envelope_685 pivot_mem_685 child_required_sub_685 child_envelope_sub_685 ?_
  intro b hb
  exact common_sub_685 (mem_commonEnvelope childrenD_685 b hb)

end FiniteCongruenceChecks.SnakyFinite
