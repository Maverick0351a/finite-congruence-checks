/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height04Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_67 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_67 j) (childrenD_67 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_67 : FiniteTemplate HasSnaky 4 required_67 envelope_67 := by
  refine finite_compose HasSnaky 3 childrenC_67 childrenD_67 finite_children_work_67 (1, 1)
    required_67 envelope_67 pivot_mem_67 child_required_sub_67 child_envelope_sub_67 ?_
  intro b hb
  exact common_sub_67 (mem_commonEnvelope childrenD_67 b hb)

theorem finite_children_work_73 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_73 j) (childrenD_73 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_73 : FiniteTemplate HasSnaky 4 required_73 envelope_73 := by
  refine finite_compose HasSnaky 3 childrenC_73 childrenD_73 finite_children_work_73 (2, 3)
    required_73 envelope_73 pivot_mem_73 child_required_sub_73 child_envelope_sub_73 ?_
  intro b hb
  exact common_sub_73 (mem_commonEnvelope childrenD_73 b hb)

theorem finite_children_work_75 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_75 j) (childrenD_75 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 6 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_75 : FiniteTemplate HasSnaky 4 required_75 envelope_75 := by
  refine finite_compose HasSnaky 3 childrenC_75 childrenD_75 finite_children_work_75 (0, 4)
    required_75 envelope_75 pivot_mem_75 child_required_sub_75 child_envelope_sub_75 ?_
  intro b hb
  exact common_sub_75 (mem_commonEnvelope childrenD_75 b hb)

theorem finite_children_work_79 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_79 j) (childrenD_79 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_79 : FiniteTemplate HasSnaky 4 required_79 envelope_79 := by
  refine finite_compose HasSnaky 3 childrenC_79 childrenD_79 finite_children_work_79 (3, 4)
    required_79 envelope_79 pivot_mem_79 child_required_sub_79 child_envelope_sub_79 ?_
  intro b hb
  exact common_sub_79 (mem_commonEnvelope childrenD_79 b hb)

theorem finite_children_work_82 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_82 j) (childrenD_82 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 0 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_64 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_82 : FiniteTemplate HasSnaky 4 required_82 envelope_82 := by
  refine finite_compose HasSnaky 3 childrenC_82 childrenD_82 finite_children_work_82 (4, 3)
    required_82 envelope_82 pivot_mem_82 child_required_sub_82 child_envelope_sub_82 ?_
  intro b hb
  exact common_sub_82 (mem_commonEnvelope childrenD_82 b hb)

theorem finite_children_work_86 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_86 j) (childrenD_86 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_78 7 (4, 4)).mono (by decide +kernel)

theorem finite_row_works_86 : FiniteTemplate HasSnaky 4 required_86 envelope_86 := by
  refine finite_compose HasSnaky 3 childrenC_86 childrenD_86 finite_children_work_86 (1, 2)
    required_86 envelope_86 pivot_mem_86 child_required_sub_86 child_envelope_sub_86 ?_
  intro b hb
  exact common_sub_86 (mem_commonEnvelope childrenD_86 b hb)

theorem finite_children_work_88 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_88 j) (childrenD_88 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_88 : FiniteTemplate HasSnaky 4 required_88 envelope_88 := by
  refine finite_compose HasSnaky 3 childrenC_88 childrenD_88 finite_children_work_88 (3, 4)
    required_88 envelope_88 pivot_mem_88 child_required_sub_88 child_envelope_sub_88 ?_
  intro b hb
  exact common_sub_88 (mem_commonEnvelope childrenD_88 b hb)

theorem finite_children_work_89 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_89 j) (childrenD_89 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_89 : FiniteTemplate HasSnaky 4 required_89 envelope_89 := by
  refine finite_compose HasSnaky 3 childrenC_89 childrenD_89 finite_children_work_89 (1, 4)
    required_89 envelope_89 pivot_mem_89 child_required_sub_89 child_envelope_sub_89 ?_
  intro b hb
  exact common_sub_89 (mem_commonEnvelope childrenD_89 b hb)

theorem finite_children_work_90 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_90 j) (childrenD_90 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 3 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_37 1 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_90 : FiniteTemplate HasSnaky 4 required_90 envelope_90 := by
  refine finite_compose HasSnaky 3 childrenC_90 childrenD_90 finite_children_work_90 (4, 1)
    required_90 envelope_90 pivot_mem_90 child_required_sub_90 child_envelope_sub_90 ?_
  intro b hb
  exact common_sub_90 (mem_commonEnvelope childrenD_90 b hb)

theorem finite_children_work_91 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_91 j) (childrenD_91 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_91 : FiniteTemplate HasSnaky 4 required_91 envelope_91 := by
  refine finite_compose HasSnaky 3 childrenC_91 childrenD_91 finite_children_work_91 (1, 4)
    required_91 envelope_91 pivot_mem_91 child_required_sub_91 child_envelope_sub_91 ?_
  intro b hb
  exact common_sub_91 (mem_commonEnvelope childrenD_91 b hb)

theorem finite_children_work_92 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_92 j) (childrenD_92 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_69.mono (by decide +kernel)

theorem finite_row_works_92 : FiniteTemplate HasSnaky 4 required_92 envelope_92 := by
  refine finite_compose HasSnaky 3 childrenC_92 childrenD_92 finite_children_work_92 (3, 3)
    required_92 envelope_92 pivot_mem_92 child_required_sub_92 child_envelope_sub_92 ?_
  intro b hb
  exact common_sub_92 (mem_commonEnvelope childrenD_92 b hb)

theorem finite_children_work_93 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_93 j) (childrenD_93 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_21 3 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_93 : FiniteTemplate HasSnaky 4 required_93 envelope_93 := by
  refine finite_compose HasSnaky 3 childrenC_93 childrenD_93 finite_children_work_93 (4, 1)
    required_93 envelope_93 pivot_mem_93 child_required_sub_93 child_envelope_sub_93 ?_
  intro b hb
  exact common_sub_93 (mem_commonEnvelope childrenD_93 b hb)

theorem finite_children_work_97 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_97 j) (childrenD_97 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_97 : FiniteTemplate HasSnaky 4 required_97 envelope_97 := by
  refine finite_compose HasSnaky 3 childrenC_97 childrenD_97 finite_children_work_97 (1, 2)
    required_97 envelope_97 pivot_mem_97 child_required_sub_97 child_envelope_sub_97 ?_
  intro b hb
  exact common_sub_97 (mem_commonEnvelope childrenD_97 b hb)

theorem finite_children_work_98 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_98 j) (childrenD_98 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_98 : FiniteTemplate HasSnaky 4 required_98 envelope_98 := by
  refine finite_compose HasSnaky 3 childrenC_98 childrenD_98 finite_children_work_98 (0, 2)
    required_98 envelope_98 pivot_mem_98 child_required_sub_98 child_envelope_sub_98 ?_
  intro b hb
  exact common_sub_98 (mem_commonEnvelope childrenD_98 b hb)

theorem finite_children_work_99 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_99 j) (childrenD_99 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_99 : FiniteTemplate HasSnaky 4 required_99 envelope_99 := by
  refine finite_compose HasSnaky 3 childrenC_99 childrenD_99 finite_children_work_99 (3, 2)
    required_99 envelope_99 pivot_mem_99 child_required_sub_99 child_envelope_sub_99 ?_
  intro b hb
  exact common_sub_99 (mem_commonEnvelope childrenD_99 b hb)

theorem finite_children_work_106 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_106 j) (childrenD_106 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_7 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_106 : FiniteTemplate HasSnaky 4 required_106 envelope_106 := by
  refine finite_compose HasSnaky 3 childrenC_106 childrenD_106 finite_children_work_106 (1, 1)
    required_106 envelope_106 pivot_mem_106 child_required_sub_106 child_envelope_sub_106 ?_
  intro b hb
  exact common_sub_106 (mem_commonEnvelope childrenD_106 b hb)

theorem finite_children_work_109 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_109 j) (childrenD_109 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_109 : FiniteTemplate HasSnaky 4 required_109 envelope_109 := by
  refine finite_compose HasSnaky 3 childrenC_109 childrenD_109 finite_children_work_109 (2, 3)
    required_109 envelope_109 pivot_mem_109 child_required_sub_109 child_envelope_sub_109 ?_
  intro b hb
  exact common_sub_109 (mem_commonEnvelope childrenD_109 b hb)

theorem finite_children_work_112 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_112 j) (childrenD_112 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_34 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_112 : FiniteTemplate HasSnaky 4 required_112 envelope_112 := by
  refine finite_compose HasSnaky 3 childrenC_112 childrenD_112 finite_children_work_112 (2, 3)
    required_112 envelope_112 pivot_mem_112 child_required_sub_112 child_envelope_sub_112 ?_
  intro b hb
  exact common_sub_112 (mem_commonEnvelope childrenD_112 b hb)

theorem finite_children_work_125 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_125 j) (childrenD_125 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_124.mono (by decide +kernel)

theorem finite_row_works_125 : FiniteTemplate HasSnaky 4 required_125 envelope_125 := by
  refine finite_compose HasSnaky 3 childrenC_125 childrenD_125 finite_children_work_125 (1, 2)
    required_125 envelope_125 pivot_mem_125 child_required_sub_125 child_envelope_sub_125 ?_
  intro b hb
  exact common_sub_125 (mem_commonEnvelope childrenD_125 b hb)

theorem finite_children_work_127 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_127 j) (childrenD_127 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 4 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_24 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_124 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_127 : FiniteTemplate HasSnaky 4 required_127 envelope_127 := by
  refine finite_compose HasSnaky 3 childrenC_127 childrenD_127 finite_children_work_127 (1, 5)
    required_127 envelope_127 pivot_mem_127 child_required_sub_127 child_envelope_sub_127 ?_
  intro b hb
  exact common_sub_127 (mem_commonEnvelope childrenD_127 b hb)

theorem finite_children_work_128 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_128 j) (childrenD_128 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_9 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_16 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_124 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_128 : FiniteTemplate HasSnaky 4 required_128 envelope_128 := by
  refine finite_compose HasSnaky 3 childrenC_128 childrenD_128 finite_children_work_128 (1, 5)
    required_128 envelope_128 pivot_mem_128 child_required_sub_128 child_envelope_sub_128 ?_
  intro b hb
  exact common_sub_128 (mem_commonEnvelope childrenD_128 b hb)

theorem finite_children_work_132 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_132 j) (childrenD_132 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_131 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_132 : FiniteTemplate HasSnaky 4 required_132 envelope_132 := by
  refine finite_compose HasSnaky 3 childrenC_132 childrenD_132 finite_children_work_132 (1, 3)
    required_132 envelope_132 pivot_mem_132 child_required_sub_132 child_envelope_sub_132 ?_
  intro b hb
  exact common_sub_132 (mem_commonEnvelope childrenD_132 b hb)

theorem finite_children_work_141 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_141 j) (childrenD_141 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_53.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_53 6 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_76 1 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_141 : FiniteTemplate HasSnaky 4 required_141 envelope_141 := by
  refine finite_compose HasSnaky 3 childrenC_141 childrenD_141 finite_children_work_141 (1, 4)
    required_141 envelope_141 pivot_mem_141 child_required_sub_141 child_envelope_sub_141 ?_
  intro b hb
  exact common_sub_141 (mem_commonEnvelope childrenD_141 b hb)

theorem finite_children_work_148 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_148 j) (childrenD_148 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_21 0 (1, 1)).mono (by decide +kernel)

theorem finite_row_works_148 : FiniteTemplate HasSnaky 4 required_148 envelope_148 := by
  refine finite_compose HasSnaky 3 childrenC_148 childrenD_148 finite_children_work_148 (1, 4)
    required_148 envelope_148 pivot_mem_148 child_required_sub_148 child_envelope_sub_148 ?_
  intro b hb
  exact common_sub_148 (mem_commonEnvelope childrenD_148 b hb)

end FiniteCongruenceChecks.SnakyFinite
