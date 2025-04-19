import LeanLTL.Examples.Scenic.KeepsDistanceRefinement.Lib

open LeanLTL
open LeanLTL.Notation
open TraceSet

namespace KeepsDistanceRefinement

theorem imp_assumptions : ⊨ LLTL[(assumptions) → i_assumptions] := by
  intro t a
  simp [push_ltl]
  simp [sat_and_iff] at a
  have this := a.left
  simp [push_ltl] at this
  trivial
