import LeanLTL.Examples.Scenic.AccurateDistanceKnownRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace AccurateDistanceKnownRefinement

theorem imp_assumptions : ⊨ LLTL[(assumptions) → i_assumptions] := by
  simp_all [push_ltl]
