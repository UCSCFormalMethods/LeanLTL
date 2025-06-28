import LeanLTLExamples.Scenic.MedianDistanceFilterSemantics.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace MedianDistanceFilterSemantics

theorem imp_assumptions : LLTL[fprops] ⇒ LLTL[assumptions → guarantees] := by
  simp [push_ltl, CF_N3, CF, ComponentFunc]
