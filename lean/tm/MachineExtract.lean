/- Extracted from pinned openai/math; see source/manifest.json.
   Changes: narrow imports and namespace wrapper only. Machine definitions unchanged. -/
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Int.Basic

namespace OAI.AlternatingNS

abbrev Rule := ℕ × ℕ × Fin 3

abbrev Machine := ℕ × ℕ × ℕ × List ℕ × List (Option Rule)

namespace Machine

def states (M : Machine) : ℕ := M.1 + 1

def alphabet (M : Machine) : ℕ := M.2.1 + 1

def initialState (M : Machine) : ℕ := M.2.2.1

def haltingStates (M : Machine) : List ℕ := M.2.2.2.1

def table (M : Machine) : List (Option Rule) := M.2.2.2.2

def instruction (M : Machine) (q a : ℕ) : Option Rule :=
  (M.table[q * M.alphabet + a]?).join

def WellFormed (M : Machine) : Prop :=
  M.initialState < M.states ∧
  (∀ q ∈ M.haltingStates, q < M.states) ∧
  ∀ q a r, q < M.states → a < M.alphabet → M.instruction q a = some r →
    r.1 < M.states ∧ r.2.1 < M.alphabet

def ValidInput (M : Machine) (w : List ℕ) : Prop :=
  ∀ a ∈ w, a < M.alphabet

structure Configuration where
  state : ℕ
  head : ℤ
  tape : ℤ → ℕ

def isHalting (M : Machine) (c : Configuration) : Bool :=
  decide (c.state = M.states ∨ c.state ∈ M.haltingStates)

def initial (M : Machine) (w : List ℕ) : Configuration where
  state := M.initialState
  head := 0
  tape := fun i => if 0 ≤ i then w[i.toNat]?.getD 0 else 0

def step (M : Machine) (c : Configuration) : Configuration :=
  if M.isHalting c then c else
    match M.instruction c.state (c.tape c.head) with
    | none => { c with state := M.states }
    | some r =>
      { state := r.1
        head := c.head + ((r.2.2.val : ℤ) - 1)
        tape := Function.update c.tape c.head r.2.1 }

def run (M : Machine) (w : List ℕ) (n : ℕ) : Configuration :=
  (M.step)^[n] (M.initial w)

def Halts (M : Machine) (w : List ℕ) : Prop :=
  ∃ n : ℕ, M.isHalting (M.run w n) = true

end Machine

end OAI.AlternatingNS
