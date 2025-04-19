import LeanLTL.Examples.Scenic.MedianDistanceFilterSemantics.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace MedianDistanceFilterSemantics

theorem imp_assumptions : ⊨ LLTL[(assumptions ∧ fprops) → guarantees] := by
  simp [push_ltl, CF_N3, CF, ComponentFunc]
