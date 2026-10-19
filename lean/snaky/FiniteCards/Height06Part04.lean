/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height06Part04
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height02Part02
import FiniteCards.Height03Part01
import FiniteCards.Height03Part02
import FiniteCards.Height04Part01
import FiniteCards.Height04Part02
import FiniteCards.Height04Part04
import FiniteCards.Height04Part05
import FiniteCards.Height05Part02
import FiniteCards.Height05Part04
import FiniteCards.Height05Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_378_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_378_i0 j) (childrenD_378_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_18 0 (2, 0)).mono (by decide +kernel)

theorem finite_row_works_378_i0 : FiniteTemplate HasSnaky 5 required_378_i0 envelope_378_i0 := by
  refine finite_compose HasSnaky 4 childrenC_378_i0 childrenD_378_i0 finite_children_work_378_i0 (3, 3)
    required_378_i0 envelope_378_i0 pivot_mem_378_i0 child_required_sub_378_i0 child_envelope_sub_378_i0 ?_
  intro b hb
  exact common_sub_378_i0 (mem_commonEnvelope childrenD_378_i0 b hb)

theorem finite_children_work_378 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_378 j) (childrenD_378 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_378_i0.mono (by decide +kernel)

theorem finite_row_works_378 : FiniteTemplate HasSnaky 6 required_378 envelope_378 := by
  refine finite_compose HasSnaky 5 childrenC_378 childrenD_378 finite_children_work_378 (3, 1)
    required_378 envelope_378 pivot_mem_378 child_required_sub_378 child_envelope_sub_378 ?_
  intro b hb
  exact common_sub_378 (mem_commonEnvelope childrenD_378 b hb)

theorem finite_children_work_384 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_384 j) (childrenD_384 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_383 7 (5, 4)).mono (by decide +kernel)

theorem finite_row_works_384 : FiniteTemplate HasSnaky 6 required_384 envelope_384 := by
  refine finite_compose HasSnaky 5 childrenC_384 childrenD_384 finite_children_work_384 (3, 3)
    required_384 envelope_384 pivot_mem_384 child_required_sub_384 child_envelope_sub_384 ?_
  intro b hb
  exact common_sub_384 (mem_commonEnvelope childrenD_384 b hb)

theorem finite_children_work_387 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_387 j) (childrenD_387 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_200 1 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_376 1 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_386 1 (0, 0)).mono (by decide +kernel)

theorem finite_row_works_387 : FiniteTemplate HasSnaky 6 required_387 envelope_387 := by
  refine finite_compose HasSnaky 5 childrenC_387 childrenD_387 finite_children_work_387 (4, 2)
    required_387 envelope_387 pivot_mem_387 child_required_sub_387 child_envelope_sub_387 ?_
  intro b hb
  exact common_sub_387 (mem_commonEnvelope childrenD_387 b hb)

theorem finite_children_work_390 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_390 j) (childrenD_390 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_17 0 (0, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_389 6 (1, 7)).mono (by decide +kernel)

theorem finite_row_works_390 : FiniteTemplate HasSnaky 6 required_390 envelope_390 := by
  refine finite_compose HasSnaky 5 childrenC_390 childrenD_390 finite_children_work_390 (1, 7)
    required_390 envelope_390 pivot_mem_390 child_required_sub_390 child_envelope_sub_390 ?_
  intro b hb
  exact common_sub_390 (mem_commonEnvelope childrenD_390 b hb)

theorem finite_children_work_392 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_392 j) (childrenD_392 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_391.mono (by decide +kernel)

theorem finite_row_works_392 : FiniteTemplate HasSnaky 6 required_392 envelope_392 := by
  refine finite_compose HasSnaky 5 childrenC_392 childrenD_392 finite_children_work_392 (3, 3)
    required_392 envelope_392 pivot_mem_392 child_required_sub_392 child_envelope_sub_392 ?_
  intro b hb
  exact common_sub_392 (mem_commonEnvelope childrenD_392 b hb)

theorem finite_children_work_393 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_393 j) (childrenD_393 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 0 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_20 0 (0, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_391 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_393 : FiniteTemplate HasSnaky 6 required_393 envelope_393 := by
  refine finite_compose HasSnaky 5 childrenC_393 childrenD_393 finite_children_work_393 (1, 4)
    required_393 envelope_393 pivot_mem_393 child_required_sub_393 child_envelope_sub_393 ?_
  intro b hb
  exact common_sub_393 (mem_commonEnvelope childrenD_393 b hb)

theorem finite_children_work_403_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_403_i0 j) (childrenD_403_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_4 5 (3, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_381 5 (4, 2)).mono (by decide +kernel)

theorem finite_row_works_403_i0 : FiniteTemplate HasSnaky 5 required_403_i0 envelope_403_i0 := by
  refine finite_compose HasSnaky 4 childrenC_403_i0 childrenD_403_i0 finite_children_work_403_i0 (2, 5)
    required_403_i0 envelope_403_i0 pivot_mem_403_i0 child_required_sub_403_i0 child_envelope_sub_403_i0 ?_
  intro b hb
  exact common_sub_403_i0 (mem_commonEnvelope childrenD_403_i0 b hb)

theorem finite_children_work_403 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_403 j) (childrenD_403 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_86.mono (by decide +kernel)
  · exact finite_row_works_403_i0.mono (by decide +kernel)

theorem finite_row_works_403 : FiniteTemplate HasSnaky 6 required_403 envelope_403 := by
  refine finite_compose HasSnaky 5 childrenC_403 childrenD_403 finite_children_work_403 (1, 5)
    required_403 envelope_403 pivot_mem_403 child_required_sub_403 child_envelope_sub_403 ?_
  intro b hb
  exact common_sub_403 (mem_commonEnvelope childrenD_403 b hb)

theorem finite_children_work_414 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_414 j) (childrenD_414 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 3 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_413.mono (by decide +kernel)

theorem finite_row_works_414 : FiniteTemplate HasSnaky 6 required_414 envelope_414 := by
  refine finite_compose HasSnaky 5 childrenC_414 childrenD_414 finite_children_work_414 (1, 4)
    required_414 envelope_414 pivot_mem_414 child_required_sub_414 child_envelope_sub_414 ?_
  intro b hb
  exact common_sub_414 (mem_commonEnvelope childrenD_414 b hb)

theorem finite_children_work_417 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_417 j) (childrenD_417 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_416.mono (by decide +kernel)

theorem finite_row_works_417 : FiniteTemplate HasSnaky 6 required_417 envelope_417 := by
  refine finite_compose HasSnaky 5 childrenC_417 childrenD_417 finite_children_work_417 (3, 2)
    required_417 envelope_417 pivot_mem_417 child_required_sub_417 child_envelope_sub_417 ?_
  intro b hb
  exact common_sub_417 (mem_commonEnvelope childrenD_417 b hb)

theorem finite_children_work_423_i0 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_423_i0 j) (childrenD_423_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_244.mono (by decide +kernel)

theorem finite_row_works_423_i0 : FiniteTemplate HasSnaky 3 required_423_i0 envelope_423_i0 := by
  refine finite_compose HasSnaky 2 childrenC_423_i0 childrenD_423_i0 finite_children_work_423_i0 (1, 2)
    required_423_i0 envelope_423_i0 pivot_mem_423_i0 child_required_sub_423_i0 child_envelope_sub_423_i0 ?_
  intro b hb
  exact common_sub_423_i0 (mem_commonEnvelope childrenD_423_i0 b hb)

theorem finite_children_work_423 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_423 j) (childrenD_423 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_383 4 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_423_i0.mono (by decide +kernel)

theorem finite_row_works_423 : FiniteTemplate HasSnaky 6 required_423 envelope_423 := by
  refine finite_compose HasSnaky 5 childrenC_423 childrenD_423 finite_children_work_423 (2, 3)
    required_423 envelope_423 pivot_mem_423 child_required_sub_423 child_envelope_sub_423 ?_
  intro b hb
  exact common_sub_423 (mem_commonEnvelope childrenD_423 b hb)

theorem finite_children_work_429_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_429_i0 j) (childrenD_429_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_46 5 (5, 1)).mono (by decide +kernel)

theorem finite_row_works_429_i0 : FiniteTemplate HasSnaky 5 required_429_i0 envelope_429_i0 := by
  refine finite_compose HasSnaky 4 childrenC_429_i0 childrenD_429_i0 finite_children_work_429_i0 (4, 3)
    required_429_i0 envelope_429_i0 pivot_mem_429_i0 child_required_sub_429_i0 child_envelope_sub_429_i0 ?_
  intro b hb
  exact common_sub_429_i0 (mem_commonEnvelope childrenD_429_i0 b hb)

theorem finite_children_work_429 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_429 j) (childrenD_429 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_7 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_8 1 (2, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_9 0 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_429_i0.mono (by decide +kernel)

theorem finite_row_works_429 : FiniteTemplate HasSnaky 6 required_429 envelope_429 := by
  refine finite_compose HasSnaky 5 childrenC_429 childrenD_429 finite_children_work_429 (3, 4)
    required_429 envelope_429 pivot_mem_429 child_required_sub_429 child_envelope_sub_429 ?_
  intro b hb
  exact common_sub_429 (mem_commonEnvelope childrenD_429 b hb)

theorem finite_children_work_435_i1 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_435_i1 j) (childrenD_435_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 4 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_212 2 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_435_i1 : FiniteTemplate HasSnaky 4 required_435_i1 envelope_435_i1 := by
  refine finite_compose HasSnaky 3 childrenC_435_i1 childrenD_435_i1 finite_children_work_435_i1 (3, 2)
    required_435_i1 envelope_435_i1 pivot_mem_435_i1 child_required_sub_435_i1 child_envelope_sub_435_i1 ?_
  intro b hb
  exact common_sub_435_i1 (mem_commonEnvelope childrenD_435_i1 b hb)

theorem finite_children_work_435_i3 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_435_i3 j) (childrenD_435_i3 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (3, 5)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 2 (3, 1)).mono (by decide +kernel)

theorem finite_row_works_435_i3 : FiniteTemplate HasSnaky 3 required_435_i3 envelope_435_i3 := by
  refine finite_compose HasSnaky 2 childrenC_435_i3 childrenD_435_i3 finite_children_work_435_i3 (3, 2)
    required_435_i3 envelope_435_i3 pivot_mem_435_i3 child_required_sub_435_i3 child_envelope_sub_435_i3 ?_
  intro b hb
  exact common_sub_435_i3 (mem_commonEnvelope childrenD_435_i3 b hb)

theorem finite_children_work_435_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_435_i2 j) (childrenD_435_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_76 2 (4, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_130 4 (3, 5)).mono (by decide +kernel)
  · exact finite_row_works_435_i3.mono (by decide +kernel)

theorem finite_row_works_435_i2 : FiniteTemplate HasSnaky 4 required_435_i2 envelope_435_i2 := by
  refine finite_compose HasSnaky 3 childrenC_435_i2 childrenD_435_i2 finite_children_work_435_i2 (3, 5)
    required_435_i2 envelope_435_i2 pivot_mem_435_i2 child_required_sub_435_i2 child_envelope_sub_435_i2 ?_
  intro b hb
  exact common_sub_435_i2 (mem_commonEnvelope childrenD_435_i2 b hb)

theorem finite_children_work_435_i0 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_435_i0 j) (childrenD_435_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_52 1 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_76 5 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_435_i1.mono (by decide +kernel)
  · exact finite_row_works_435_i2.mono (by decide +kernel)

theorem finite_row_works_435_i0 : FiniteTemplate HasSnaky 5 required_435_i0 envelope_435_i0 := by
  refine finite_compose HasSnaky 4 childrenC_435_i0 childrenD_435_i0 finite_children_work_435_i0 (3, 4)
    required_435_i0 envelope_435_i0 pivot_mem_435_i0 child_required_sub_435_i0 child_envelope_sub_435_i0 ?_
  intro b hb
  exact common_sub_435_i0 (mem_commonEnvelope childrenD_435_i0 b hb)

theorem finite_children_work_435 : ∀ j, FiniteTemplate HasSnaky 5 (childrenC_435 j) (childrenD_435 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_130 3 (1, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_140 3 (0, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_183 4 (0, 5)).mono (by decide +kernel)
  · exact finite_row_works_435_i0.mono (by decide +kernel)

theorem finite_row_works_435 : FiniteTemplate HasSnaky 6 required_435 envelope_435 := by
  refine finite_compose HasSnaky 5 childrenC_435 childrenD_435 finite_children_work_435 (4, 2)
    required_435 envelope_435 pivot_mem_435 child_required_sub_435 child_envelope_sub_435 ?_
  intro b hb
  exact common_sub_435 (mem_commonEnvelope childrenD_435 b hb)

end FiniteCongruenceChecks.SnakyFinite
