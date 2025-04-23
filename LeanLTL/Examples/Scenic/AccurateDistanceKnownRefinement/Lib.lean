import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateDistanceKnownRefinement

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
  N4: ℚ
  N5: ℚ
  N6: ℚ
deriving Inhabited

-- Prop Signals

-- Numerical Signals
abbrev SCENIC_INTERNAL_VAR_0 : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev SCENIC_INTERNAL_VAR_1 : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev SCENIC_INTERNAL_VAR_2 : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev SCENIC_INTERNAL_VAR_3 : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev lead_distances_lead_car_ : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev params__lead_car_width__ : TraceFun TraceState ℚ := TraceFun.of (·.N5)
abbrev params__weather__ : TraceFun TraceState ℚ := TraceFun.of (·.N6)

-- Defs
abbrev lead_dist := LLTLV[(lead_distances_lead_car_)]
abbrev behind_car := LLTLV[((lead_dist)) ≤ (1000)]

-- Top Level Assumptions 
abbrev A0 := LLTL[((((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))) ∧ (((←params__lead_car_width__)) ≥ (1.8))]

abbrev assumptions : TraceSet TraceState := LLTL[A0]

-- Internal Assumptions 
abbrev IA0 := LLTL[((←params__lead_car_width__)) ≥ (1.8)]
abbrev IA1 := LLTL[(((←params__weather__)) = (0)) ∨ (((←params__weather__)) = (1))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1]

-- Internal Guarantees 
abbrev IG0 := LLTL[𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ (((←lead_dist)) + (0.1)))))]
abbrev IG1 := LLTL[𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←SCENIC_INTERNAL_VAR_1))) ∧ (((←SCENIC_INTERNAL_VAR_1)) ≤ (((←lead_dist)) + (0.1)))))]
abbrev IG2 := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_3)) = (((((←SCENIC_INTERNAL_VAR_0)) ⊔ ((←SCENIC_INTERNAL_VAR_1))) ⊓ (((←SCENIC_INTERNAL_VAR_0)) ⊔ ((←SCENIC_INTERNAL_VAR_1)))) ⊓ (((←SCENIC_INTERNAL_VAR_1)) ⊔ ((←SCENIC_INTERNAL_VAR_2)))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2]

-- Top Level Guarantees 
abbrev G0 := LLTL[𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←SCENIC_INTERNAL_VAR_3))) ∧ (((←SCENIC_INTERNAL_VAR_3)) ≤ (((←lead_dist)) + (0.1)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

