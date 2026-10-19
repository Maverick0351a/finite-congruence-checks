import GroupingChecker

open Lean GroupingChecker

def output (w : Word) : Json :=
  let d := decode w
  let pair := match findViolation w with
    | none => Json.null
    | some (x, y) => toJson [x.val, y.val]
  Json.mkObj [
    ("status", toJson "checked"),
    ("word", toJson w.val),
    ("operation", toJson (vertices.map fun i => (d.operation i).val)),
    ("group_labels", toJson (vertices.map fun i => (d.labels i).val)),
    ("roundtrip_word", toJson (encode d).val),
    ("preserves", toJson (!(check w))),
    ("violating_pair", pair)]

def invalid (raw : String) : Json :=
  Json.mkObj [("status", toJson "invalid_input"), ("input", toJson raw)]

-- The text adapter accepts decimal integer tokens only, without whitespace.
-- It is outside the pure checker theorem and is tested separately.
def parseWord (raw : String) : Option Word := do
  let digits := if raw.startsWith "-" then raw.drop 1 |>.toString else raw
  if digits.isEmpty || !digits.toList.all Char.isDigit then none else
    let z ← raw.toInt?
    decodeInt z

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  if args == ["--all"] then
    for n in List.range 65536 do
      if h : n < 65536 then
        stdout.putStrLn ((output ⟨n, h⟩).compress)
    return 0
  if args.isEmpty then
    (← IO.getStderr).putStrLn "usage: grouping_checker --all | DECIMAL_WORD ..."
    return 2
  let mut failed := false
  for raw in args do
    match parseWord raw with
    | some w => stdout.putStrLn ((output w).compress)
    | none =>
      stdout.putStrLn ((invalid raw).compress)
      failed := true
  return if failed then 2 else 0
