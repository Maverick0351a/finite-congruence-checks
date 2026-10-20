/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height21Part01
import FiniteCards.Height15Part01
import FiniteCards.Height15Part03
import FiniteCards.Height20Part01

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_727 : ∀ j, FiniteTemplate HasSnaky 20 (childrenC_727 j) (childrenD_727 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_648 0 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_648 1 (3, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_648 3 (3, 12)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_648 4 (4, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_708 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_708 2 (16, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_708 4 (0, 16)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_708 7 (16, 16)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 0 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 1 (3, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 2 (13, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 3 (3, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 4 (3, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 5 (13, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 6 (13, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_712 7 (13, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_713 2 (13, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_713 3 (3, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_713 4 (3, 13)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_713 5 (13, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 0 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 2 (15, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 3 (1, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 4 (1, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 5 (15, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 6 (15, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_725 7 (15, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_726 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_726 2 (15, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_726 4 (1, 15)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_726 6 (15, 15)).mono (by decide +kernel)

theorem finite_row_works_727 : FiniteTemplate HasSnaky 21 required_727 envelope_727 := by
  refine finite_compose HasSnaky 20 childrenC_727 childrenD_727 finite_children_work_727 (8, 8)
    required_727 envelope_727 pivot_mem_727 child_required_sub_727 child_envelope_sub_727 ?_
  intro b hb
  exact common_sub_727 (mem_commonEnvelope childrenD_727 b hb)

end FiniteCongruenceChecks.SnakyFinite
