/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height03Part02
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_108 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_108 j) (childrenD_108 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_102 3 (0, 3)).mono (by decide +kernel)

theorem finite_row_works_108 : FiniteTemplate HasSnaky 3 required_108 envelope_108 := by
  refine finite_compose HasSnaky 2 childrenC_108 childrenD_108 finite_children_work_108 (1, 1)
    required_108 envelope_108 pivot_mem_108 child_required_sub_108 child_envelope_sub_108 ?_
  intro b hb
  exact common_sub_108 (mem_commonEnvelope childrenD_108 b hb)

theorem finite_children_work_113 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_113 j) (childrenD_113 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 0 (0, 2)).mono (by decide +kernel)

theorem finite_row_works_113 : FiniteTemplate HasSnaky 3 required_113 envelope_113 := by
  refine finite_compose HasSnaky 2 childrenC_113 childrenD_113 finite_children_work_113 (1, 3)
    required_113 envelope_113 pivot_mem_113 child_required_sub_113 child_envelope_sub_113 ?_
  intro b hb
  exact common_sub_113 (mem_commonEnvelope childrenD_113 b hb)

theorem finite_children_work_124 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_124 j) (childrenD_124 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_123 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_124 : FiniteTemplate HasSnaky 3 required_124 envelope_124 := by
  refine finite_compose HasSnaky 2 childrenC_124 childrenD_124 finite_children_work_124 (2, 1)
    required_124 envelope_124 pivot_mem_124 child_required_sub_124 child_envelope_sub_124 ?_
  intro b hb
  exact common_sub_124 (mem_commonEnvelope childrenD_124 b hb)

theorem finite_children_work_126 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_126 j) (childrenD_126 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_123 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_126 : FiniteTemplate HasSnaky 3 required_126 envelope_126 := by
  refine finite_compose HasSnaky 2 childrenC_126 childrenD_126 finite_children_work_126 (1, 2)
    required_126 envelope_126 pivot_mem_126 child_required_sub_126 child_envelope_sub_126 ?_
  intro b hb
  exact common_sub_126 (mem_commonEnvelope childrenD_126 b hb)

theorem finite_children_work_130 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_130 j) (childrenD_130 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact finite_row_works_129.mono (by decide +kernel)

theorem finite_row_works_130 : FiniteTemplate HasSnaky 3 required_130 envelope_130 := by
  refine finite_compose HasSnaky 2 childrenC_130 childrenD_130 finite_children_work_130 (1, 4)
    required_130 envelope_130 pivot_mem_130 child_required_sub_130 child_envelope_sub_130 ?_
  intro b hb
  exact common_sub_130 (mem_commonEnvelope childrenD_130 b hb)

theorem finite_children_work_131 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_131 j) (childrenD_131 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_15.mono (by decide +kernel)

theorem finite_row_works_131 : FiniteTemplate HasSnaky 3 required_131 envelope_131 := by
  refine finite_compose HasSnaky 2 childrenC_131 childrenD_131 finite_children_work_131 (1, 3)
    required_131 envelope_131 pivot_mem_131 child_required_sub_131 child_envelope_sub_131 ?_
  intro b hb
  exact common_sub_131 (mem_commonEnvelope childrenD_131 b hb)

theorem finite_children_work_139 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_139 j) (childrenD_139 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_138 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_139 : FiniteTemplate HasSnaky 3 required_139 envelope_139 := by
  refine finite_compose HasSnaky 2 childrenC_139 childrenD_139 finite_children_work_139 (1, 3)
    required_139 envelope_139 pivot_mem_139 child_required_sub_139 child_envelope_sub_139 ?_
  intro b hb
  exact common_sub_139 (mem_commonEnvelope childrenD_139 b hb)

theorem finite_children_work_140 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_140 j) (childrenD_140 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 1 (0, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_43 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_140 : FiniteTemplate HasSnaky 3 required_140 envelope_140 := by
  refine finite_compose HasSnaky 2 childrenC_140 childrenD_140 finite_children_work_140 (1, 3)
    required_140 envelope_140 pivot_mem_140 child_required_sub_140 child_envelope_sub_140 ?_
  intro b hb
  exact common_sub_140 (mem_commonEnvelope childrenD_140 b hb)

theorem finite_children_work_143 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_143 j) (childrenD_143 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 3 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_143 : FiniteTemplate HasSnaky 3 required_143 envelope_143 := by
  refine finite_compose HasSnaky 2 childrenC_143 childrenD_143 finite_children_work_143 (4, 1)
    required_143 envelope_143 pivot_mem_143 child_required_sub_143 child_envelope_sub_143 ?_
  intro b hb
  exact common_sub_143 (mem_commonEnvelope childrenD_143 b hb)

theorem finite_children_work_157 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_157 j) (childrenD_157 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_156 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_157 : FiniteTemplate HasSnaky 3 required_157 envelope_157 := by
  refine finite_compose HasSnaky 2 childrenC_157 childrenD_157 finite_children_work_157 (4, 0)
    required_157 envelope_157 pivot_mem_157 child_required_sub_157 child_envelope_sub_157 ?_
  intro b hb
  exact common_sub_157 (mem_commonEnvelope childrenD_157 b hb)

theorem finite_children_work_158 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_158 j) (childrenD_158 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_158 : FiniteTemplate HasSnaky 3 required_158 envelope_158 := by
  refine finite_compose HasSnaky 2 childrenC_158 childrenD_158 finite_children_work_158 (0, 4)
    required_158 envelope_158 pivot_mem_158 child_required_sub_158 child_envelope_sub_158 ?_
  intro b hb
  exact common_sub_158 (mem_commonEnvelope childrenD_158 b hb)

theorem finite_children_work_159 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_159 j) (childrenD_159 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_23 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_66 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_159 : FiniteTemplate HasSnaky 3 required_159 envelope_159 := by
  refine finite_compose HasSnaky 2 childrenC_159 childrenD_159 finite_children_work_159 (3, 1)
    required_159 envelope_159 pivot_mem_159 child_required_sub_159 child_envelope_sub_159 ?_
  intro b hb
  exact common_sub_159 (mem_commonEnvelope childrenD_159 b hb)

theorem finite_children_work_160 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_160 j) (childrenD_160 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 4 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_160 : FiniteTemplate HasSnaky 3 required_160 envelope_160 := by
  refine finite_compose HasSnaky 2 childrenC_160 childrenD_160 finite_children_work_160 (1, 2)
    required_160 envelope_160 pivot_mem_160 child_required_sub_160 child_envelope_sub_160 ?_
  intro b hb
  exact common_sub_160 (mem_commonEnvelope childrenD_160 b hb)

theorem finite_children_work_163 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_163 j) (childrenD_163 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_3 1 (0, 0)).mono (by decide +kernel)
  · exact finite_row_works_129.mono (by decide +kernel)

theorem finite_row_works_163 : FiniteTemplate HasSnaky 3 required_163 envelope_163 := by
  refine finite_compose HasSnaky 2 childrenC_163 childrenD_163 finite_children_work_163 (0, 2)
    required_163 envelope_163 pivot_mem_163 child_required_sub_163 child_envelope_sub_163 ?_
  intro b hb
  exact common_sub_163 (mem_commonEnvelope childrenD_163 b hb)

theorem finite_children_work_177 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_177 j) (childrenD_177 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_23.mono (by decide +kernel)

theorem finite_row_works_177 : FiniteTemplate HasSnaky 3 required_177 envelope_177 := by
  refine finite_compose HasSnaky 2 childrenC_177 childrenD_177 finite_children_work_177 (1, 1)
    required_177 envelope_177 pivot_mem_177 child_required_sub_177 child_envelope_sub_177 ?_
  intro b hb
  exact common_sub_177 (mem_commonEnvelope childrenD_177 b hb)

theorem finite_children_work_198 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_198 j) (childrenD_198 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 6)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_6 4 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_198 : FiniteTemplate HasSnaky 3 required_198 envelope_198 := by
  refine finite_compose HasSnaky 2 childrenC_198 childrenD_198 finite_children_work_198 (1, 5)
    required_198 envelope_198 pivot_mem_198 child_required_sub_198 child_envelope_sub_198 ?_
  intro b hb
  exact common_sub_198 (mem_commonEnvelope childrenD_198 b hb)

theorem finite_children_work_201 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_201 j) (childrenD_201 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_146 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_201 : FiniteTemplate HasSnaky 3 required_201 envelope_201 := by
  refine finite_compose HasSnaky 2 childrenC_201 childrenD_201 finite_children_work_201 (3, 0)
    required_201 envelope_201 pivot_mem_201 child_required_sub_201 child_envelope_sub_201 ?_
  intro b hb
  exact common_sub_201 (mem_commonEnvelope childrenD_201 b hb)

theorem finite_children_work_205 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_205 j) (childrenD_205 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_6 4 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_23 2 (1, 2)).mono (by decide +kernel)

theorem finite_row_works_205 : FiniteTemplate HasSnaky 3 required_205 envelope_205 := by
  refine finite_compose HasSnaky 2 childrenC_205 childrenD_205 finite_children_work_205 (1, 5)
    required_205 envelope_205 pivot_mem_205 child_required_sub_205 child_envelope_sub_205 ?_
  intro b hb
  exact common_sub_205 (mem_commonEnvelope childrenD_205 b hb)

theorem finite_children_work_207 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_207 j) (childrenD_207 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_77 5 (4, 0)).mono (by decide +kernel)

theorem finite_row_works_207 : FiniteTemplate HasSnaky 3 required_207 envelope_207 := by
  refine finite_compose HasSnaky 2 childrenC_207 childrenD_207 finite_children_work_207 (3, 1)
    required_207 envelope_207 pivot_mem_207 child_required_sub_207 child_envelope_sub_207 ?_
  intro b hb
  exact common_sub_207 (mem_commonEnvelope childrenD_207 b hb)

theorem finite_children_work_209 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_209 j) (childrenD_209 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_138 6 (1, 4)).mono (by decide +kernel)

theorem finite_row_works_209 : FiniteTemplate HasSnaky 3 required_209 envelope_209 := by
  refine finite_compose HasSnaky 2 childrenC_209 childrenD_209 finite_children_work_209 (1, 4)
    required_209 envelope_209 pivot_mem_209 child_required_sub_209 child_envelope_sub_209 ?_
  intro b hb
  exact common_sub_209 (mem_commonEnvelope childrenD_209 b hb)

theorem finite_children_work_212 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_212 j) (childrenD_212 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_76 0 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_212 : FiniteTemplate HasSnaky 3 required_212 envelope_212 := by
  refine finite_compose HasSnaky 2 childrenC_212 childrenD_212 finite_children_work_212 (1, 4)
    required_212 envelope_212 pivot_mem_212 child_required_sub_212 child_envelope_sub_212 ?_
  intro b hb
  exact common_sub_212 (mem_commonEnvelope childrenD_212 b hb)

theorem finite_children_work_215 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_215 j) (childrenD_215 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 2 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_215 : FiniteTemplate HasSnaky 3 required_215 envelope_215 := by
  refine finite_compose HasSnaky 2 childrenC_215 childrenD_215 finite_children_work_215 (3, 1)
    required_215 envelope_215 pivot_mem_215 child_required_sub_215 child_envelope_sub_215 ?_
  intro b hb
  exact common_sub_215 (mem_commonEnvelope childrenD_215 b hb)

theorem finite_children_work_218 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_218 j) (childrenD_218 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_83 4 (0, 4)).mono (by decide +kernel)

theorem finite_row_works_218 : FiniteTemplate HasSnaky 3 required_218 envelope_218 := by
  refine finite_compose HasSnaky 2 childrenC_218 childrenD_218 finite_children_work_218 (1, 2)
    required_218 envelope_218 pivot_mem_218 child_required_sub_218 child_envelope_sub_218 ?_
  intro b hb
  exact common_sub_218 (mem_commonEnvelope childrenD_218 b hb)

theorem finite_children_work_219 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_219 j) (childrenD_219 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 7 (1, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 6 (1, 5)).mono (by decide +kernel)

theorem finite_row_works_219 : FiniteTemplate HasSnaky 3 required_219 envelope_219 := by
  refine finite_compose HasSnaky 2 childrenC_219 childrenD_219 finite_children_work_219 (1, 1)
    required_219 envelope_219 pivot_mem_219 child_required_sub_219 child_envelope_sub_219 ?_
  intro b hb
  exact common_sub_219 (mem_commonEnvelope childrenD_219 b hb)

end FiniteCongruenceChecks.SnakyFinite
