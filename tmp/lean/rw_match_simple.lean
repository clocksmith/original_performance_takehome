import Mathlib

namespace RwMatchSimple

example (e : Option Nat) (h : e = none) :
    (match e with
      | none => 0
      | some _ => 1) = 0 := by
  rw [h]
  simp

end RwMatchSimple

