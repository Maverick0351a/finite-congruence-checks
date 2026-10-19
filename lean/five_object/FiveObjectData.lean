import FiveObjectBase

namespace FiniteCongruenceChecks.FiveObject

namespace A

def op1 : V → V := table (0, 0, 4, 0, 0)
def op2 : V → V := table (0, 3, 1, 1, 4)
def op3 : V → V := table (1, 1, 3, 3, 3)
def ops (i : Fin 3) : V → V :=
  match i.val with | 0 => op1 | 1 => op2 | _ => op3
def partition (a : Fin 8) : Table :=
  match a.val with
  | 0 => (0,0,0,0,0)
  | 1 => (0,0,1,0,0)
  | 2 => (0,0,1,0,2)
  | 3 => (0,1,1,1,0)
  | 4 => (0,1,2,1,0)
  | 5 => (0,1,2,1,1)
  | 6 => (0,1,2,1,3)
  | _ => (0,1,2,3,4)
def theta (a : Fin 8) : Rel := graph (partition a)

/-- Extra equivalences that no pair of compatible rules can all exclude. -/
def obstruction (i : Fin 4) : Rel := graph <|
  match i.val with
  | 0 => (0,0,0,0,1)
  | 1 => (0,0,1,2,3)
  | 2 => (0,1,2,3,0)
  | _ => (0,1,2,3,1)

end A

namespace B

def op1 : V → V := table (4,1,3,2,4)
def op2 : V → V := table (1,2,3,3,3)
def ops (i : Fin 2) : V → V := if i.val = 0 then op1 else op2
def partition (a : Fin 8) : Table :=
  match a.val with
  | 0 => (0,0,0,0,0)
  | 1 => (0,1,1,1,0)
  | 2 => (0,1,1,1,1)
  | 3 => (0,1,1,1,2)
  | 4 => (0,1,2,2,1)
  | 5 => (0,1,2,2,2)
  | 6 => (0,1,2,2,3)
  | _ => (0,1,2,3,4)
def theta (a : Fin 8) : Rel := graph (partition a)
def obstruction (i : Fin 2) : Rel := graph <|
  if i.val = 0 then (0,0,0,0,1) else (0,0,1,1,0)

end B

/-- A-index to B-index for the explicit inclusion-order isomorphism. -/
def correspondence (a : Fin 8) : Fin 8 :=
  match a.val with
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | _ => 7
def inverseCorrespondence (a : Fin 8) : Fin 8 :=
  match a.val with
  | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | _ => 7

/-- Explicit shared eight-element order, indexed by A's lexicographic partitions. -/
def le (a b : Fin 8) : Bool :=
  match a.val, b.val with
  | 0, 0 => true
  | 1, 0 | 1, 1 => true
  | 2, 0 | 2, 1 | 2, 2 => true
  | 3, 0 | 3, 3 => true
  | 4, 0 | 4, 1 | 4, 3 | 4, 4 => true
  | 5, 0 | 5, 1 | 5, 5 => true
  | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 6 => true
  | 7, _ => true
  | _, _ => false

end FiniteCongruenceChecks.FiveObject
