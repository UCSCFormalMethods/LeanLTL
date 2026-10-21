import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace AccurateDistanceKnownRefinement

set_option linter.style.nameCheck false

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
abbrev A0 := LLTL[((((←ˢparams__weather__)) = (0)) ∨ (((←ˢparams__weather__)) = (1))) ∧ (((←ˢparams__lead_car_width__)) ≥ (1.8))]

abbrev assumptions : TraceSet TraceState := LLTL[A0]

-- Internal Assumptions 
abbrev IA0 := LLTL[((←ˢparams__lead_car_width__)) ≥ (1.8)]
abbrev IA1 := LLTL[(((←ˢparams__weather__)) = (0)) ∨ (((←ˢparams__weather__)) = (1))]

abbrev i_assumptions : TraceSet TraceState := LLTL[IA0 ∧ IA1]

-- Internal Guarantees 
abbrev IG0 := LLTL[𝐆 (((←ˢbehind_car)) → (((((←ˢlead_dist)) - (0.1)) ≤ ((←ˢSCENIC_INTERNAL_VAR_0))) ∧ (((←ˢSCENIC_INTERNAL_VAR_0)) ≤ (((←ˢlead_dist)) + (0.1)))))]
abbrev IG1 := LLTL[𝐆 (((←ˢbehind_car)) → (((((←ˢlead_dist)) - (0.1)) ≤ ((←ˢSCENIC_INTERNAL_VAR_1))) ∧ (((←ˢSCENIC_INTERNAL_VAR_1)) ≤ (((←ˢlead_dist)) + (0.1)))))]
abbrev IG2 := LLTL[𝐆 (((←ˢSCENIC_INTERNAL_VAR_3)) = (((((←ˢSCENIC_INTERNAL_VAR_0)) ⊔ ((←ˢSCENIC_INTERNAL_VAR_1))) ⊓ (((←ˢSCENIC_INTERNAL_VAR_0)) ⊔ ((←ˢSCENIC_INTERNAL_VAR_1)))) ⊓ (((←ˢSCENIC_INTERNAL_VAR_1)) ⊔ ((←ˢSCENIC_INTERNAL_VAR_2)))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2]

-- Top Level Guarantees 
abbrev G0 := LLTL[𝐆 (((←ˢbehind_car)) → (((((←ˢlead_dist)) - (0.1)) ≤ ((←ˢSCENIC_INTERNAL_VAR_3))) ∧ (((←ˢSCENIC_INTERNAL_VAR_3)) ≤ (((←ˢlead_dist)) + (0.1)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]
