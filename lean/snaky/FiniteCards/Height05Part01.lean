/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part01
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part03

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_19 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_19 j) (childrenD_19 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_19 : FiniteTemplate HasSnaky 5 required_19 envelope_19 := by
  refine finite_compose HasSnaky 4 childrenC_19 childrenD_19 finite_children_work_19 (0, 1)
    required_19 envelope_19 pivot_mem_19 child_required_sub_19 child_envelope_sub_19 ?_
  intro b hb
  exact common_sub_19 (mem_commonEnvelope childrenD_19 b hb)

theorem finite_children_work_47 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_47 j) (childrenD_47 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_46 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_47 : FiniteTemplate HasSnaky 5 required_47 envelope_47 := by
  refine finite_compose HasSnaky 4 childrenC_47 childrenD_47 finite_children_work_47 (4, 2)
    required_47 envelope_47 pivot_mem_47 child_required_sub_47 child_envelope_sub_47 ?_
  intro b hb
  exact common_sub_47 (mem_commonEnvelope childrenD_47 b hb)

theorem finite_children_work_59 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_59 j) (childrenD_59 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_28 5 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_31 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_58 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_59 : FiniteTemplate HasSnaky 5 required_59 envelope_59 := by
  refine finite_compose HasSnaky 4 childrenC_59 childrenD_59 finite_children_work_59 (3, 2)
    required_59 envelope_59 pivot_mem_59 child_required_sub_59 child_envelope_sub_59 ?_
  intro b hb
  exact common_sub_59 (mem_commonEnvelope childrenD_59 b hb)

theorem finite_children_work_71 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_71 j) (childrenD_71 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 2 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_71 : FiniteTemplate HasSnaky 5 required_71 envelope_71 := by
  refine finite_compose HasSnaky 4 childrenC_71 childrenD_71 finite_children_work_71 (2, 1)
    required_71 envelope_71 pivot_mem_71 child_required_sub_71 child_envelope_sub_71 ?_
  intro b hb
  exact common_sub_71 (mem_commonEnvelope childrenD_71 b hb)

theorem finite_children_work_72 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_72 j) (childrenD_72 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 3 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_46.mono (by decide +kernel)

theorem finite_row_works_72 : FiniteTemplate HasSnaky 5 required_72 envelope_72 := by
  refine finite_compose HasSnaky 4 childrenC_72 childrenD_72 finite_children_work_72 (3, 2)
    required_72 envelope_72 pivot_mem_72 child_required_sub_72 child_envelope_sub_72 ?_
  intro b hb
  exact common_sub_72 (mem_commonEnvelope childrenD_72 b hb)

theorem finite_children_work_81 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_81 j) (childrenD_81 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_42 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_81 : FiniteTemplate HasSnaky 5 required_81 envelope_81 := by
  refine finite_compose HasSnaky 4 childrenC_81 childrenD_81 finite_children_work_81 (3, 2)
    required_81 envelope_81 pivot_mem_81 child_required_sub_81 child_envelope_sub_81 ?_
  intro b hb
  exact common_sub_81 (mem_commonEnvelope childrenD_81 b hb)

theorem finite_children_work_84 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_84 j) (childrenD_84 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 6 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_84 : FiniteTemplate HasSnaky 5 required_84 envelope_84 := by
  refine finite_compose HasSnaky 4 childrenC_84 childrenD_84 finite_children_work_84 (1, 5)
    required_84 envelope_84 pivot_mem_84 child_required_sub_84 child_envelope_sub_84 ?_
  intro b hb
  exact common_sub_84 (mem_commonEnvelope childrenD_84 b hb)

theorem finite_children_work_100 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_100 j) (childrenD_100 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 4 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_100 : FiniteTemplate HasSnaky 5 required_100 envelope_100 := by
  refine finite_compose HasSnaky 4 childrenC_100 childrenD_100 finite_children_work_100 (4, 1)
    required_100 envelope_100 pivot_mem_100 child_required_sub_100 child_envelope_sub_100 ?_
  intro b hb
  exact common_sub_100 (mem_commonEnvelope childrenD_100 b hb)

theorem finite_children_work_104 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_104 j) (childrenD_104 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_10 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 4 (0, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_52 6 (1, 6)).mono (by decide +kernel)

theorem finite_row_works_104 : FiniteTemplate HasSnaky 5 required_104 envelope_104 := by
  refine finite_compose HasSnaky 4 childrenC_104 childrenD_104 finite_children_work_104 (1, 4)
    required_104 envelope_104 pivot_mem_104 child_required_sub_104 child_envelope_sub_104 ?_
  intro b hb
  exact common_sub_104 (mem_commonEnvelope childrenD_104 b hb)

theorem finite_children_work_107 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_107 j) (childrenD_107 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_107 : FiniteTemplate HasSnaky 5 required_107 envelope_107 := by
  refine finite_compose HasSnaky 4 childrenC_107 childrenD_107 finite_children_work_107 (1, 2)
    required_107 envelope_107 pivot_mem_107 child_required_sub_107 child_envelope_sub_107 ?_
  intro b hb
  exact common_sub_107 (mem_commonEnvelope childrenD_107 b hb)

theorem finite_children_work_111 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_111 j) (childrenD_111 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_17 1 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_55 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_111 : FiniteTemplate HasSnaky 5 required_111 envelope_111 := by
  refine finite_compose HasSnaky 4 childrenC_111 childrenD_111 finite_children_work_111 (4, 3)
    required_111 envelope_111 pivot_mem_111 child_required_sub_111 child_envelope_sub_111 ?_
  intro b hb
  exact common_sub_111 (mem_commonEnvelope childrenD_111 b hb)

theorem finite_children_work_114 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_114 j) (childrenD_114 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_14 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_114 : FiniteTemplate HasSnaky 5 required_114 envelope_114 := by
  refine finite_compose HasSnaky 4 childrenC_114 childrenD_114 finite_children_work_114 (3, 4)
    required_114 envelope_114 pivot_mem_114 child_required_sub_114 child_envelope_sub_114 ?_
  intro b hb
  exact common_sub_114 (mem_commonEnvelope childrenD_114 b hb)

theorem finite_children_work_122 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_122 j) (childrenD_122 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_46 3 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_122 : FiniteTemplate HasSnaky 5 required_122 envelope_122 := by
  refine finite_compose HasSnaky 4 childrenC_122 childrenD_122 finite_children_work_122 (2, 4)
    required_122 envelope_122 pivot_mem_122 child_required_sub_122 child_envelope_sub_122 ?_
  intro b hb
  exact common_sub_122 (mem_commonEnvelope childrenD_122 b hb)

theorem finite_children_work_133 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_133 j) (childrenD_133 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_132.mono (by decide +kernel)

theorem finite_row_works_133 : FiniteTemplate HasSnaky 5 required_133 envelope_133 := by
  refine finite_compose HasSnaky 4 childrenC_133 childrenD_133 finite_children_work_133 (1, 1)
    required_133 envelope_133 pivot_mem_133 child_required_sub_133 child_envelope_sub_133 ?_
  intro b hb
  exact common_sub_133 (mem_commonEnvelope childrenD_133 b hb)

theorem finite_children_work_142 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_142 j) (childrenD_142 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_141 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_142 : FiniteTemplate HasSnaky 5 required_142 envelope_142 := by
  refine finite_compose HasSnaky 4 childrenC_142 childrenD_142 finite_children_work_142 (1, 2)
    required_142 envelope_142 pivot_mem_142 child_required_sub_142 child_envelope_sub_142 ?_
  intro b hb
  exact common_sub_142 (mem_commonEnvelope childrenD_142 b hb)

theorem finite_children_work_144 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_144 j) (childrenD_144 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_46.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_103 3 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_143 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_144 : FiniteTemplate HasSnaky 5 required_144 envelope_144 := by
  refine finite_compose HasSnaky 4 childrenC_144 childrenD_144 finite_children_work_144 (3, 2)
    required_144 envelope_144 pivot_mem_144 child_required_sub_144 child_envelope_sub_144 ?_
  intro b hb
  exact common_sub_144 (mem_commonEnvelope childrenD_144 b hb)

theorem finite_children_work_145 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_145 j) (childrenD_145 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_10 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_145 : FiniteTemplate HasSnaky 5 required_145 envelope_145 := by
  refine finite_compose HasSnaky 4 childrenC_145 childrenD_145 finite_children_work_145 (3, 2)
    required_145 envelope_145 pivot_mem_145 child_required_sub_145 child_envelope_sub_145 ?_
  intro b hb
  exact common_sub_145 (mem_commonEnvelope childrenD_145 b hb)

theorem finite_children_work_147 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_147 j) (childrenD_147 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_39 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_147 : FiniteTemplate HasSnaky 5 required_147 envelope_147 := by
  refine finite_compose HasSnaky 4 childrenC_147 childrenD_147 finite_children_work_147 (3, 2)
    required_147 envelope_147 pivot_mem_147 child_required_sub_147 child_envelope_sub_147 ?_
  intro b hb
  exact common_sub_147 (mem_commonEnvelope childrenD_147 b hb)

theorem finite_children_work_152 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_152 j) (childrenD_152 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_99 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_152 : FiniteTemplate HasSnaky 5 required_152 envelope_152 := by
  refine finite_compose HasSnaky 4 childrenC_152 childrenD_152 finite_children_work_152 (2, 3)
    required_152 envelope_152 pivot_mem_152 child_required_sub_152 child_envelope_sub_152 ?_
  intro b hb
  exact common_sub_152 (mem_commonEnvelope childrenD_152 b hb)

theorem finite_children_work_155 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_155 j) (childrenD_155 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 3 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_46 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_155 : FiniteTemplate HasSnaky 5 required_155 envelope_155 := by
  refine finite_compose HasSnaky 4 childrenC_155 childrenD_155 finite_children_work_155 (4, 2)
    required_155 envelope_155 pivot_mem_155 child_required_sub_155 child_envelope_sub_155 ?_
  intro b hb
  exact common_sub_155 (mem_commonEnvelope childrenD_155 b hb)

theorem finite_children_work_164 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_164 j) (childrenD_164 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_55.mono (by decide +kernel)

theorem finite_row_works_164 : FiniteTemplate HasSnaky 5 required_164 envelope_164 := by
  refine finite_compose HasSnaky 4 childrenC_164 childrenD_164 finite_children_work_164 (3, 3)
    required_164 envelope_164 pivot_mem_164 child_required_sub_164 child_envelope_sub_164 ?_
  intro b hb
  exact common_sub_164 (mem_commonEnvelope childrenD_164 b hb)

theorem finite_children_work_175 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_175 j) (childrenD_175 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (1, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 1 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_60 4 (0, 6)).mono (by decide +kernel)

theorem finite_row_works_175 : FiniteTemplate HasSnaky 5 required_175 envelope_175 := by
  refine finite_compose HasSnaky 4 childrenC_175 childrenD_175 finite_children_work_175 (1, 5)
    required_175 envelope_175 pivot_mem_175 child_required_sub_175 child_envelope_sub_175 ?_
  intro b hb
  exact common_sub_175 (mem_commonEnvelope childrenD_175 b hb)

theorem finite_children_work_176 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_176 j) (childrenD_176 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_60 2 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_176 : FiniteTemplate HasSnaky 5 required_176 envelope_176 := by
  refine finite_compose HasSnaky 4 childrenC_176 childrenD_176 finite_children_work_176 (2, 2)
    required_176 envelope_176 pivot_mem_176 child_required_sub_176 child_envelope_sub_176 ?_
  intro b hb
  exact common_sub_176 (mem_commonEnvelope childrenD_176 b hb)

theorem finite_children_work_179 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_179 j) (childrenD_179 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_178.mono (by decide +kernel)

theorem finite_row_works_179 : FiniteTemplate HasSnaky 5 required_179 envelope_179 := by
  refine finite_compose HasSnaky 4 childrenC_179 childrenD_179 finite_children_work_179 (1, 3)
    required_179 envelope_179 pivot_mem_179 child_required_sub_179 child_envelope_sub_179 ?_
  intro b hb
  exact common_sub_179 (mem_commonEnvelope childrenD_179 b hb)

end FiniteCongruenceChecks.SnakyFinite
