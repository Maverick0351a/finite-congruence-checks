import MachineChecks

/- Exact machines for tm-pair:tiny-stay:v1. The two entries in the right
   table are both intentional, even though only the first is reached here. -/
namespace TMOracle.TinyPair
open OAI.AlternatingNS

def leftMachine : Machine := (0, 1, 0, [], [none, none])
def rightMachine : Machine :=
  (1, 1, 0, [1], [some (1, 1, 1), some (1, 1, 1), none, none])
def blankInput : List Nat := []

theorem left_initial_active : leftMachine.isHalting (leftMachine.run blankInput 0) = false := by decide
theorem right_initial_active : rightMachine.isHalting (rightMachine.run blankInput 0) = false := by decide
theorem left_halts_one : leftMachine.isHalting (leftMachine.run blankInput 1) = true := by decide
theorem right_halts_one : rightMachine.isHalting (rightMachine.run blankInput 1) = true := by decide
theorem left_head_one : (leftMachine.run blankInput 1).head = 0 := by decide
theorem right_head_one : (rightMachine.run blankInput 1).head = 0 := by decide

theorem left_tape_one (i : Int) : (leftMachine.run blankInput 1).tape i = 0 := by
  change (if 0 ≤ i then 0 else 0) = 0
  simp

theorem right_tape_one (i : Int) :
    (rightMachine.run blankInput 1).tape i = if i = 0 then 1 else 0 := by
  change (Function.update (fun j : Int => if 0 ≤ j then 0 else 0) 0 1) i = _
  simp [Function.update_apply]

theorem tapes_differ : (leftMachine.run blankInput 1).tape ≠ (rightMachine.run blankInput 1).tape := by
  intro same
  have at_zero := congrFun same 0
  rw [left_tape_one, right_tape_one] at at_zero
  simp at at_zero

/- The time quantifier is exactly steps 0 and 1 on this input. The tape
   quantifier is every integer position, including cells outside any picture. -/
theorem exact_result :
    leftMachine.isHalting (leftMachine.run blankInput 0) = false ∧
    rightMachine.isHalting (rightMachine.run blankInput 0) = false ∧
    leftMachine.isHalting (leftMachine.run blankInput 1) = true ∧
    rightMachine.isHalting (rightMachine.run blankInput 1) = true ∧
    (leftMachine.run blankInput 1).head = 0 ∧
    (rightMachine.run blankInput 1).head = 0 ∧
    (∀ i : Int, (leftMachine.run blankInput 1).tape i = 0) ∧
    (∀ i : Int, (rightMachine.run blankInput 1).tape i = if i = 0 then 1 else 0) ∧
    (leftMachine.run blankInput 1).tape ≠ (rightMachine.run blankInput 1).tape :=
  ⟨left_initial_active, right_initial_active, left_halts_one, right_halts_one,
   left_head_one, right_head_one, left_tape_one, right_tape_one, tapes_differ⟩

end TMOracle.TinyPair
