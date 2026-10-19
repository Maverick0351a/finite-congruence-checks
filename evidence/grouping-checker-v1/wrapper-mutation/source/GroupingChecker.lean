import Lean

/-!
Four-object unary grouping checker, contract unary-grouping-v1.
All proofs are kernel checked. The decoder uses base-4 arithmetic; its bit-field
correspondence is stated separately from checker correctness.
-/

namespace GroupingChecker

abbrev V := Fin 4
abbrev Word := Fin 65536

structure Input where
  operation : V → V
  labels : V → V

def digit (w : Nat) (i : Nat) : V := ⟨w / 4 ^ i % 4, Nat.mod_lt _ (by decide)⟩

def decode (w : Word) : Input :=
  ⟨fun i => digit w.val i.val, fun i => digit w.val (4 + i.val)⟩

theorem low_two_bits (n : Nat) : n &&& 3 = n % 4 :=
  Nat.and_two_pow_sub_one_eq_mod n 2

theorem decode_operation_bits (w : Word) (i : V) :
    ((decode w).operation i).val = (w.val >>> (2 * i.val)) &&& 3 := by
  rw [low_two_bits, Nat.shiftRight_eq_div_pow]
  have cases4 : ∀ i : V, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases cases4 i with rfl | rfl | rfl | rfl <;> rfl

theorem decode_label_bits (w : Word) (i : V) :
    ((decode w).labels i).val = (w.val >>> (8 + 2 * i.val)) &&& 3 := by
  rw [low_two_bits, Nat.shiftRight_eq_div_pow]
  have cases4 : ∀ i : V, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases cases4 i with rfl | rfl | rfl | rfl <;> rfl

def encodedNat (d : Input) : Nat :=
  (d.operation 0).val + 4 * (d.operation 1).val +
  16 * (d.operation 2).val + 64 * (d.operation 3).val +
  256 * (d.labels 0).val + 1024 * (d.labels 1).val +
  4096 * (d.labels 2).val + 16384 * (d.labels 3).val

theorem encodedNat_lt (d : Input) : encodedNat d < 65536 := by
  have := (d.operation 0).isLt
  have := (d.operation 1).isLt
  have := (d.operation 2).isLt
  have := (d.operation 3).isLt
  have := (d.labels 0).isLt
  have := (d.labels 1).isLt
  have := (d.labels 2).isLt
  have := (d.labels 3).isLt
  unfold encodedNat
  omega

def encode (d : Input) : Word := ⟨encodedNat d, encodedNat_lt d⟩

theorem fin4_cases (i : V) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  exact (by decide : ∀ i : V, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i

theorem encode_decode (w : Word) : encode (decode w) = w := by
  apply Fin.ext
  have h3 : (3 : V).val = 3 := by decide
  simp [encode, encodedNat, decode, digit, h3]
  have := w.isLt
  omega

theorem decode_encode_operation (d : Input) (i : V) :
    (decode (encode d)).operation i = d.operation i := by
  have := (d.operation 0).isLt
  have := (d.operation 1).isLt
  have := (d.operation 2).isLt
  have := (d.operation 3).isLt
  have := (d.labels 0).isLt
  have := (d.labels 1).isLt
  have := (d.labels 2).isLt
  have := (d.labels 3).isLt
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  all_goals apply Fin.ext
  all_goals have h3 : (3 : V).val = 3 := by decide
  all_goals simp [encode, encodedNat, decode, digit, h3]
  all_goals omega

theorem decode_encode_labels (d : Input) (i : V) :
    (decode (encode d)).labels i = d.labels i := by
  have := (d.operation 0).isLt
  have := (d.operation 1).isLt
  have := (d.operation 2).isLt
  have := (d.operation 3).isLt
  have := (d.labels 0).isLt
  have := (d.labels 1).isLt
  have := (d.labels 2).isLt
  have := (d.labels 3).isLt
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  all_goals apply Fin.ext
  all_goals have h3 : (3 : V).val = 3 := by decide
  all_goals simp [encode, encodedNat, decode, digit, h3]
  all_goals omega

theorem decode_encode (d : Input) : decode (encode d) = d := by
  cases d with
  | mk f g =>
    have hf := funext (decode_encode_operation ⟨f, g⟩)
    have hg := funext (decode_encode_labels ⟨f, g⟩)
    change Input.mk (decode (encode ⟨f, g⟩)).operation
      (decode (encode ⟨f, g⟩)).labels = Input.mk f g
    rw [hf, hg]

def decodeInt (z : Int) : Option Word :=
  if h : 0 ≤ z ∧ z < 65536 then some ⟨z.toNat, by omega⟩ else none

theorem decodeInt_invalid (z : Int) :
    decodeInt z = none ↔ z < 0 ∨ z ≥ 65536 := by
  unfold decodeInt
  split <;> simp_all <;> omega

theorem decodeInt_value (z : Int) (w : Word) (h : decodeInt z = some w) :
    (w.val : Int) = z := by
  unfold decodeInt at h
  split at h
  · cases h
    change (z.toNat : Int) = z
    omega
  · contradiction

theorem decodeInt_valid (w : Word) : decodeInt (w.val : Int) = some w := by
  have h := w.isLt
  have hz : (w.val : Int) < 65536 := by omega
  simp [decodeInt, hz]

def Respects (d : Input) : Prop :=
  ∀ x y : V, d.labels x = d.labels y →
    d.labels (d.operation x) = d.labels (d.operation y)

def Violates (d : Input) (p : V × V) : Prop :=
  d.labels p.1 = d.labels p.2 ∧
  d.labels (d.operation p.1) ≠ d.labels (d.operation p.2)

instance (d : Input) (p : V × V) : Decidable (Violates d p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def scan (d : Input) : List (V × V) → Option (V × V)
  | [] => none
  | p :: ps => if Violates d p then some p else scan d ps

theorem scan_some (d : Input) (ps : List (V × V)) (p : V × V)
    (h : scan d ps = some p) : Violates d p := by
  induction ps with
  | nil => simp [scan] at h
  | cons q qs ih =>
    simp only [scan] at h
    split at h
    · cases h
      assumption
    · exact ih h

theorem scan_none (d : Input) (ps : List (V × V)) :
    scan d ps = none ↔ ∀ p ∈ ps, ¬ Violates d p := by
  induction ps with
  | nil => simp [scan]
  | cons p ps ih =>
    by_cases h : Violates d p <;> simp [scan, h, ih]

def vertices : List V := [0, 1, 2, 3]
def pairs : List (V × V) := vertices.flatMap fun x => vertices.map fun y => (x, y)

theorem pair_mem (x y : V) : (x, y) ∈ pairs := by
  rcases fin4_cases x with rfl | rfl | rfl | rfl
  all_goals rcases fin4_cases y with rfl | rfl | rfl | rfl
  all_goals decide

def findViolation (w : Word) : Option (V × V) := scan (decode w) pairs
def check (w : Word) : Bool := (findViolation w).isNone

theorem witness_sound (w : Word) (p : V × V)
    (h : findViolation w = some p) : Violates (decode w) p :=
  scan_some (decode w) pairs p h

theorem findViolation_none_iff (w : Word) :
    findViolation w = none ↔ Respects (decode w) := by
  rw [findViolation, scan_none]
  constructor
  · intro h x y hxy
    by_cases he : (decode w).labels ((decode w).operation x) =
        (decode w).labels ((decode w).operation y)
    · exact he
    · exact False.elim (h (x, y) (pair_mem x y) ⟨hxy, he⟩)
  · intro h p _ hv
    exact hv.2 (h p.1 p.2 hv.1)

theorem check_iff (w : Word) : check w = true ↔ Respects (decode w) := by
  rw [← findViolation_none_iff]
  simp [check]

theorem rejected_has_witness (w : Word) (h : check w = false) :
    ∃ p, findViolation w = some p ∧ Violates (decode w) p := by
  cases hf : findViolation w with
  | none => simp [check, hf] at h
  | some p => exact ⟨p, rfl, witness_sound w p hf⟩

theorem labels_equivalence (d : Input) : Equivalence (fun x y => d.labels x = d.labels y) :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

end GroupingChecker
