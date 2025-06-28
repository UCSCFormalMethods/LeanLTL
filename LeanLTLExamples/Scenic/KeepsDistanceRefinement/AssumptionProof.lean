import LeanLTLExamples.Scenic.KeepsDistanceRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace KeepsDistanceRefinement

theorem imp_assumptions : ⊨ LLTL[(assumptions) → i_assumptions] := by
  intro t a
  simp [push_ltl]
