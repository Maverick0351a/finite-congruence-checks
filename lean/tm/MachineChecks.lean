import MachineExtract

namespace TMOracle.Checks

open OAI.AlternatingNS

theorem halted_fixed (M : Machine) (c : Machine.Configuration)
    (halted : M.isHalting c = true) : M.step c = c := by
  simp [Machine.step, halted]

theorem missing_instruction (M : Machine) (c : Machine.Configuration)
    (active : M.isHalting c = false)
    (missing : M.instruction c.state (c.tape c.head) = none) :
    M.step c = { c with state := M.states } := by
  simp [Machine.step, active, missing]

theorem instruction_step (M : Machine) (c : Machine.Configuration) (r : Rule)
    (active : M.isHalting c = false)
    (instruction : M.instruction c.state (c.tape c.head) = some r) :
    M.step c = {
      state := r.1
      head := c.head + ((r.2.2.val : Int) - 1)
      tape := Function.update c.tape c.head r.2.1 } := by
  simp [Machine.step, active, instruction]

theorem instruction_writes (M : Machine) (c : Machine.Configuration) (r : Rule)
    (active : M.isHalting c = false)
    (instruction : M.instruction c.state (c.tape c.head) = some r) :
    (M.step c).tape c.head = r.2.1 := by
  rw [instruction_step M c r active instruction]
  simp

theorem instruction_preserves_other_cells (M : Machine) (c : Machine.Configuration) (r : Rule)
    (active : M.isHalting c = false)
    (instruction : M.instruction c.state (c.tape c.head) = some r)
    (i : Int) (different : i ≠ c.head) :
    (M.step c).tape i = c.tape i := by
  rw [instruction_step M c r active instruction]
  simp [different]

#print axioms halted_fixed
#print axioms missing_instruction
#print axioms instruction_step
#print axioms instruction_writes
#print axioms instruction_preserves_other_cells

end TMOracle.Checks
