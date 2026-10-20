/- Derived from openai/math SnakyTwentyOne card proofs at
1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).
Modified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/
import SnakySemantics
import OAI.GameTheory.SnakyTwentyOne.Cards.Height05Part05
import FiniteCards.Height01Part01
import FiniteCards.Height02Part01
import FiniteCards.Height03Part01
import FiniteCards.Height03Part03
import FiniteCards.Height04Part02
import FiniteCards.Height04Part05

namespace FiniteCongruenceChecks.SnakyFinite
open OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21

theorem finite_children_work_391_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_391_i1 j) (childrenD_391_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 1)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_36 4 (2, 4)).mono (by decide +kernel)

theorem finite_row_works_391_i1 : FiniteTemplate HasSnaky 3 required_391_i1 envelope_391_i1 := by
  refine finite_compose HasSnaky 2 childrenC_391_i1 childrenD_391_i1 finite_children_work_391_i1 (3, 1)
    required_391_i1 envelope_391_i1 pivot_mem_391_i1 child_required_sub_391_i1 child_envelope_sub_391_i1 ?_
  intro b hb
  exact common_sub_391_i1 (mem_commonEnvelope childrenD_391_i1 b hb)

theorem finite_children_work_391_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_391_i0 j) (childrenD_391_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 3 (1, 4)).mono (by decide +kernel)
  · exact finite_row_works_391_i1.mono (by decide +kernel)

theorem finite_row_works_391_i0 : FiniteTemplate HasSnaky 4 required_391_i0 envelope_391_i0 := by
  refine finite_compose HasSnaky 3 childrenC_391_i0 childrenD_391_i0 finite_children_work_391_i0 (2, 1)
    required_391_i0 envelope_391_i0 pivot_mem_391_i0 child_required_sub_391_i0 child_envelope_sub_391_i0 ?_
  intro b hb
  exact common_sub_391_i0 (mem_commonEnvelope childrenD_391_i0 b hb)

theorem finite_children_work_391 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_391 j) (childrenD_391 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_391_i0.mono (by decide +kernel)

theorem finite_row_works_391 : FiniteTemplate HasSnaky 5 required_391 envelope_391 := by
  refine finite_compose HasSnaky 4 childrenC_391 childrenD_391 finite_children_work_391 (2, 4)
    required_391 envelope_391 pivot_mem_391 child_required_sub_391 child_envelope_sub_391 ?_
  intro b hb
  exact common_sub_391 (mem_commonEnvelope childrenD_391 b hb)

theorem finite_children_work_413_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_413_i0 j) (childrenD_413_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 7 (2, 4)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_45 1 (0, 1)).mono (by decide +kernel)

theorem finite_row_works_413_i0 : FiniteTemplate HasSnaky 4 required_413_i0 envelope_413_i0 := by
  refine finite_compose HasSnaky 3 childrenC_413_i0 childrenD_413_i0 finite_children_work_413_i0 (2, 3)
    required_413_i0 envelope_413_i0 pivot_mem_413_i0 child_required_sub_413_i0 child_envelope_sub_413_i0 ?_
  intro b hb
  exact common_sub_413_i0 (mem_commonEnvelope childrenD_413_i0 b hb)

theorem finite_children_work_413 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_413 j) (childrenD_413 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 1 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_413_i0.mono (by decide +kernel)

theorem finite_row_works_413 : FiniteTemplate HasSnaky 5 required_413 envelope_413 := by
  refine finite_compose HasSnaky 4 childrenC_413 childrenD_413 finite_children_work_413 (2, 4)
    required_413 envelope_413 pivot_mem_413 child_required_sub_413 child_envelope_sub_413 ?_
  intro b hb
  exact common_sub_413 (mem_commonEnvelope childrenD_413 b hb)

theorem finite_children_work_416_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_416_i0 j) (childrenD_416_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_239 4 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_416_i0 : FiniteTemplate HasSnaky 4 required_416_i0 envelope_416_i0 := by
  refine finite_compose HasSnaky 3 childrenC_416_i0 childrenD_416_i0 finite_children_work_416_i0 (3, 1)
    required_416_i0 envelope_416_i0 pivot_mem_416_i0 child_required_sub_416_i0 child_envelope_sub_416_i0 ?_
  intro b hb
  exact common_sub_416_i0 (mem_commonEnvelope childrenD_416_i0 b hb)

theorem finite_children_work_416 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_416 j) (childrenD_416 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 0 (0, 2)).mono (by decide +kernel)
  · exact finite_row_works_416_i0.mono (by decide +kernel)

theorem finite_row_works_416 : FiniteTemplate HasSnaky 5 required_416 envelope_416 := by
  refine finite_compose HasSnaky 4 childrenC_416 childrenD_416 finite_children_work_416 (3, 3)
    required_416 envelope_416 pivot_mem_416 child_required_sub_416 child_envelope_sub_416 ?_
  intro b hb
  exact common_sub_416 (mem_commonEnvelope childrenD_416 b hb)

theorem finite_children_work_425_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_425_i0 j) (childrenD_425_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 0 (0, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_44 0 (3, 0)).mono (by decide +kernel)

theorem finite_row_works_425_i0 : FiniteTemplate HasSnaky 4 required_425_i0 envelope_425_i0 := by
  refine finite_compose HasSnaky 3 childrenC_425_i0 childrenD_425_i0 finite_children_work_425_i0 (3, 2)
    required_425_i0 envelope_425_i0 pivot_mem_425_i0 child_required_sub_425_i0 child_envelope_sub_425_i0 ?_
  intro b hb
  exact common_sub_425_i0 (mem_commonEnvelope childrenD_425_i0 b hb)

theorem finite_children_work_425 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_425 j) (childrenD_425 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_2 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_425_i0.mono (by decide +kernel)

theorem finite_row_works_425 : FiniteTemplate HasSnaky 5 required_425 envelope_425 := by
  refine finite_compose HasSnaky 4 childrenC_425 childrenD_425 finite_children_work_425 (4, 3)
    required_425 envelope_425 pivot_mem_425 child_required_sub_425 child_envelope_sub_425 ?_
  intro b hb
  exact common_sub_425 (mem_commonEnvelope childrenD_425 b hb)

theorem finite_children_work_426_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_426_i0 j) (childrenD_426_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (5, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_221 2 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_426_i0 : FiniteTemplate HasSnaky 4 required_426_i0 envelope_426_i0 := by
  refine finite_compose HasSnaky 3 childrenC_426_i0 childrenD_426_i0 finite_children_work_426_i0 (3, 3)
    required_426_i0 envelope_426_i0 pivot_mem_426_i0 child_required_sub_426_i0 child_envelope_sub_426_i0 ?_
  intro b hb
  exact common_sub_426_i0 (mem_commonEnvelope childrenD_426_i0 b hb)

theorem finite_children_work_426 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_426 j) (childrenD_426 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (2, 0)).mono (by decide +kernel)
  · exact finite_row_works_426_i0.mono (by decide +kernel)

theorem finite_row_works_426 : FiniteTemplate HasSnaky 5 required_426 envelope_426 := by
  refine finite_compose HasSnaky 4 childrenC_426 childrenD_426 finite_children_work_426 (2, 4)
    required_426 envelope_426 pivot_mem_426 child_required_sub_426 child_envelope_sub_426 ?_
  intro b hb
  exact common_sub_426 (mem_commonEnvelope childrenD_426 b hb)

theorem finite_children_work_433 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_433 j) (childrenD_433 j) := by
  intro j
  fin_cases j
  · exact finite_row_works_86.mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_432 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_433 : FiniteTemplate HasSnaky 5 required_433 envelope_433 := by
  refine finite_compose HasSnaky 4 childrenC_433 childrenD_433 finite_children_work_433 (3, 4)
    required_433 envelope_433 pivot_mem_433 child_required_sub_433 child_envelope_sub_433 ?_
  intro b hb
  exact common_sub_433 (mem_commonEnvelope childrenD_433 b hb)

theorem finite_children_work_445_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_445_i0 j) (childrenD_445_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_20 0 (2, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_29 2 (3, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_221 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_445_i0 : FiniteTemplate HasSnaky 4 required_445_i0 envelope_445_i0 := by
  refine finite_compose HasSnaky 3 childrenC_445_i0 childrenD_445_i0 finite_children_work_445_i0 (3, 3)
    required_445_i0 envelope_445_i0 pivot_mem_445_i0 child_required_sub_445_i0 child_envelope_sub_445_i0 ?_
  intro b hb
  exact common_sub_445_i0 (mem_commonEnvelope childrenD_445_i0 b hb)

theorem finite_children_work_445 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_445 j) (childrenD_445 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_5 4 (0, 1)).mono (by decide +kernel)
  · exact finite_row_works_445_i0.mono (by decide +kernel)

theorem finite_row_works_445 : FiniteTemplate HasSnaky 5 required_445 envelope_445 := by
  refine finite_compose HasSnaky 4 childrenC_445 childrenD_445 finite_children_work_445 (3, 0)
    required_445 envelope_445 pivot_mem_445 child_required_sub_445 child_envelope_sub_445 ?_
  intro b hb
  exact common_sub_445 (mem_commonEnvelope childrenD_445 b hb)

theorem finite_children_work_451_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_451_i0 j) (childrenD_451_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact finite_row_works_402.mono (by decide +kernel)

theorem finite_row_works_451_i0 : FiniteTemplate HasSnaky 4 required_451_i0 envelope_451_i0 := by
  refine finite_compose HasSnaky 3 childrenC_451_i0 childrenD_451_i0 finite_children_work_451_i0 (2, 3)
    required_451_i0 envelope_451_i0 pivot_mem_451_i0 child_required_sub_451_i0 child_envelope_sub_451_i0 ?_
  intro b hb
  exact common_sub_451_i0 (mem_commonEnvelope childrenD_451_i0 b hb)

theorem finite_children_work_451 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_451 j) (childrenD_451 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_11 2 (1, 0)).mono (by decide +kernel)
  · exact finite_row_works_451_i0.mono (by decide +kernel)

theorem finite_row_works_451 : FiniteTemplate HasSnaky 5 required_451 envelope_451 := by
  refine finite_compose HasSnaky 4 childrenC_451 childrenD_451 finite_children_work_451 (1, 4)
    required_451 envelope_451 pivot_mem_451 child_required_sub_451 child_envelope_sub_451 ?_
  intro b hb
  exact common_sub_451 (mem_commonEnvelope childrenD_451 b hb)

theorem finite_children_work_464_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_464_i1 j) (childrenD_464_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 5 (1, 0)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_11 0 (1, 0)).mono (by decide +kernel)

theorem finite_row_works_464_i1 : FiniteTemplate HasSnaky 3 required_464_i1 envelope_464_i1 := by
  refine finite_compose HasSnaky 2 childrenC_464_i1 childrenD_464_i1 finite_children_work_464_i1 (1, 1)
    required_464_i1 envelope_464_i1 pivot_mem_464_i1 child_required_sub_464_i1 child_envelope_sub_464_i1 ?_
  intro b hb
  exact common_sub_464_i1 (mem_commonEnvelope childrenD_464_i1 b hb)

theorem finite_children_work_464_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_464_i0 j) (childrenD_464_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 2 (4, 2)).mono (by decide +kernel)
  · exact finite_row_works_464_i1.mono (by decide +kernel)

theorem finite_row_works_464_i0 : FiniteTemplate HasSnaky 4 required_464_i0 envelope_464_i0 := by
  refine finite_compose HasSnaky 3 childrenC_464_i0 childrenD_464_i0 finite_children_work_464_i0 (2, 2)
    required_464_i0 envelope_464_i0 pivot_mem_464_i0 child_required_sub_464_i0 child_envelope_sub_464_i0 ?_
  intro b hb
  exact common_sub_464_i0 (mem_commonEnvelope childrenD_464_i0 b hb)

theorem finite_children_work_464_i2 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_464_i2 j) (childrenD_464_i2 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_29 2 (1, 2)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_38 3 (0, 5)).mono (by decide +kernel)

theorem finite_row_works_464_i2 : FiniteTemplate HasSnaky 4 required_464_i2 envelope_464_i2 := by
  refine finite_compose HasSnaky 3 childrenC_464_i2 childrenD_464_i2 finite_children_work_464_i2 (1, 5)
    required_464_i2 envelope_464_i2 pivot_mem_464_i2 child_required_sub_464_i2 child_envelope_sub_464_i2 ?_
  intro b hb
  exact common_sub_464_i2 (mem_commonEnvelope childrenD_464_i2 b hb)

theorem finite_children_work_464 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_464 j) (childrenD_464 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_15 2 (1, 1)).mono (by decide +kernel)
  · exact finite_row_works_464_i0.mono (by decide +kernel)
  · exact finite_row_works_464_i2.mono (by decide +kernel)

theorem finite_row_works_464 : FiniteTemplate HasSnaky 5 required_464 envelope_464 := by
  refine finite_compose HasSnaky 4 childrenC_464 childrenD_464 finite_children_work_464 (1, 2)
    required_464 envelope_464 pivot_mem_464 child_required_sub_464 child_envelope_sub_464 ?_
  intro b hb
  exact common_sub_464 (mem_commonEnvelope childrenD_464 b hb)

theorem finite_children_work_492_i1 : ∀ j, FiniteTemplate HasSnaky 2 (childrenC_492_i1 j) (childrenD_492_i1 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 6 (4, 3)).mono (by decide +kernel)
  · exact (finite_placed21_template finite_row_works_32 5 (4, 1)).mono (by decide +kernel)

theorem finite_row_works_492_i1 : FiniteTemplate HasSnaky 3 required_492_i1 envelope_492_i1 := by
  refine finite_compose HasSnaky 2 childrenC_492_i1 childrenD_492_i1 finite_children_work_492_i1 (2, 3)
    required_492_i1 envelope_492_i1 pivot_mem_492_i1 child_required_sub_492_i1 child_envelope_sub_492_i1 ?_
  intro b hb
  exact common_sub_492_i1 (mem_commonEnvelope childrenD_492_i1 b hb)

theorem finite_children_work_492_i0 : ∀ j, FiniteTemplate HasSnaky 3 (childrenC_492_i0 j) (childrenD_492_i0 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_0 7 (1, 5)).mono (by decide +kernel)
  · exact finite_row_works_492_i1.mono (by decide +kernel)

theorem finite_row_works_492_i0 : FiniteTemplate HasSnaky 4 required_492_i0 envelope_492_i0 := by
  refine finite_compose HasSnaky 3 childrenC_492_i0 childrenD_492_i0 finite_children_work_492_i0 (1, 3)
    required_492_i0 envelope_492_i0 pivot_mem_492_i0 child_required_sub_492_i0 child_envelope_sub_492_i0 ?_
  intro b hb
  exact common_sub_492_i0 (mem_commonEnvelope childrenD_492_i0 b hb)

theorem finite_children_work_492 : ∀ j, FiniteTemplate HasSnaky 4 (childrenC_492 j) (childrenD_492 j) := by
  intro j
  fin_cases j
  · exact (finite_placed21_template finite_row_works_78 7 (4, 4)).mono (by decide +kernel)
  · exact finite_row_works_492_i0.mono (by decide +kernel)

theorem finite_row_works_492 : FiniteTemplate HasSnaky 5 required_492 envelope_492 := by
  refine finite_compose HasSnaky 4 childrenC_492 childrenD_492 finite_children_work_492 (1, 2)
    required_492 envelope_492 pivot_mem_492 child_required_sub_492 child_envelope_sub_492 ?_
  intro b hb
  exact common_sub_492 (mem_commonEnvelope childrenD_492 b hb)

end FiniteCongruenceChecks.SnakyFinite
