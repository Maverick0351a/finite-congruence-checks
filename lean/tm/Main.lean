import MachineExtract
import Lean.Data.Json

/- This executable is a finite differential oracle, not an equivalence proof. -/
open Lean OAI.AlternatingNS

namespace TMOracle

structure Case where
  id : String
  machine : Machine
  input : List Nat
  steps : Nat

def natural (value : Json) : Except String Nat :=
  match value with
  | .num ⟨.ofNat n, 0⟩ => .ok n
  | _ => .error "expected a nonnegative integer JSON number"

def naturals (value : Json) : Except String (List Nat) := do
  let values ← value.getArr?
  (values.toList).mapM natural

def rule (value : Json) : Except String (Option Rule) := do
  if value.isNull then return none
  let values ← value.getArr?
  if values.size != 3 then throw "a rule must be null or exactly [next_state,write,move]"
  let state ← natural (← value.getArrVal? 0)
  let write ← natural (← value.getArrVal? 1)
  let move ← natural (← value.getArrVal? 2)
  if h : move < 3 then return some (state, write, ⟨move, h⟩)
  else throw "move must be 0, 1, or 2"

def decode (value : Json) : Except String Case := do
  let id ← (← value.getObjVal? "id").getStr?
  let m ← value.getObjVal? "machine"
  let states ← natural (← m.getObjVal? "n_states_minus_one")
  let alphabet ← natural (← m.getObjVal? "n_alphabet_minus_one")
  let initial ← natural (← m.getObjVal? "initial_state")
  let halting ← naturals (← m.getObjVal? "halting_states")
  let entries ← (← m.getObjVal? "table").getArr?
  let table ← entries.toList.mapM rule
  let input ← naturals (← value.getObjVal? "input")
  let steps ← natural (← value.getObjVal? "steps")
  return ⟨id, (states, alphabet, initial, halting, table), input, steps⟩

/-- Enumerate the complete possible support after `steps` steps, in increasing order.
    Starting support is in [0,input.length-1], and each step moves at most one cell. -/
def observe (c : Case) : Json := Id.run do
  let result := c.machine.run c.input c.steps
  let upper := max c.steps (c.input.length - 1)
  let mut tape : Array Json := #[]
  for offset in List.range (c.steps + upper + 1) do
    let position : Int := (offset : Int) - (c.steps : Int)
    let symbol := result.tape position
    if symbol != 0 then
      tape := tape.push (.arr #[toJson position, toJson symbol])
  return Json.mkObj [
    ("id", toJson c.id),
    ("steps", toJson c.steps),
    ("state", toJson result.state),
    ("head", toJson result.head),
    ("halted", toJson (c.machine.isHalting result)),
    ("tape", .arr tape)]

/-- Preserve the integer-token boundary used by the Python JSON decoder.
    Lean's JSON parser normalizes `1e0` to an integer, so reject decimal/exponent
    number tokens before parsing; quoted IDs and property names remain unrestricted. -/
def integerTokens (line : String) : Except String Unit := do
  let mut quoted := false
  let mut escaped := false
  let mut number := false
  for c in line.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then
      quoted := true
      number := false
    else if c.isWhitespace || c == ',' || c == ':' || c == '[' || c == ']' || c == '{' || c == '}' then
      number := false
    else if number && (c == '.' || c == 'e' || c == 'E') then
      throw "decimal and exponent number tokens are not integer JSON inputs"
    else if c.isDigit || c == '-' then
      number := true

def parseCase (line : String) : Except String Case := do
  integerTokens line
  decode (← Json.parse line)

partial def readCases (stdin stdout stderr : IO.FS.Stream) (lineNumber : Nat) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  match parseCase line with
  | .error error =>
    stderr.putStrLn s!"tmOracle: line {lineNumber}: {error}"
    return 1
  | .ok c =>
    stdout.putStrLn (observe c).compress
    stdout.flush
    readCases stdin stdout stderr (lineNumber + 1)

end TMOracle

def main : IO UInt32 := do
  TMOracle.readCases (← IO.getStdin) (← IO.getStdout) (← IO.getStderr) 1
