import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsDistanceRefinement

structure TraceState where
  -- Props
  P0: Prop
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
  N4: ℚ
  N5: ℚ
deriving Inhabited

-- Prop Signals
abbrev self._lane_is_not_None : TraceSet TraceState := TraceSet.of (·.P0)

-- Numerical Signals
abbrev SCENIC_INTERNAL_VAR_0 : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev SCENIC_INTERNAL_VAR_1 : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev SCENIC_INTERNAL_VAR_4 : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev lead_car.speed : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev lead_distances_lead_car_ : TraceFun TraceState ℚ := TraceFun.of (·.N4)
abbrev self.speed : TraceFun TraceState ℚ := TraceFun.of (·.N5)

-- Defs
abbrev lead_dist := LLTLV[(lead_distances_lead_car_)]
abbrev behind_car := LLTLV[((lead_dist)) ≤ (1000)]
abbrev p_relative_speed := LLTLV[((SCENIC_INTERNAL_VAR_0)) - (𝐗 ((SCENIC_INTERNAL_VAR_0)))]
abbrev p_stopping_time := LLTLV[⌈(𝐗 ((SCENIC_INTERNAL_VAR_1))) / (0.9)⌉]
abbrev p_rel_dist_covered := LLTLV[((p_stopping_time)) * (((p_relative_speed)) + (1.6))]
abbrev p_delta_stopping_time := LLTLV[⌈((𝐗 ((SCENIC_INTERNAL_VAR_1))) + (0.5)) / (0.9)⌉]
abbrev p_max_rdc_delta := LLTLV[(((p_delta_stopping_time)) * (((((p_relative_speed)) + (0.9)) + (0.5)) + ((2) * (1.6)))) - ((p_rel_dist_covered))]
abbrev p_buffer_dist := LLTLV[(((5) + ((0) ⊔ (((p_max_rdc_delta)) + ((p_rel_dist_covered))))) + (5.4)) + (1)]
abbrev true_relative_speed := LLTLV[((self.speed)) - ((lead_car.speed))]
abbrev stopping_time := LLTLV[⌈((self.speed)) / (0.9)⌉]
abbrev rel_dist_covered := LLTLV[((stopping_time)) * (((true_relative_speed)) + (1.6))]
abbrev delta_stopping_time := LLTLV[⌈(((self.speed)) + (0.5)) / (0.9)⌉]
abbrev max_rdc_delta := LLTLV[(((delta_stopping_time)) * (((((true_relative_speed)) + (0.9)) + (0.5)) + (1.6))) - ((rel_dist_covered))]
abbrev buffer_dist := LLTLV[(((5) + ((0) ⊔ (((max_rdc_delta)) + ((rel_dist_covered))))) + (5.4)) + (1)]

-- Top Level Assumptions 
abbrev A0 := LLTL[𝐆 ((←self._lane_is_not_None))]
abbrev A1 := LLTL[𝐆 (((0) ≤ ((←self.speed))) ∧ (((←self.speed)) ≤ (5.4)))]
abbrev A2 := LLTL[𝐆 (((0) ≤ ((←lead_car.speed))) ∧ (((←lead_car.speed)) ≤ (5.4)))]
abbrev A3 := LLTL[𝐆 (((-(0.9)) ≤ ((𝐗 ((←self.speed))) - ((←self.speed)))) ∧ (((𝐗 ((←self.speed))) - ((←self.speed))) ≤ (0.5)))]
abbrev A4 := LLTL[𝐆 (((-(0.9)) ≤ ((𝐗 ((←lead_car.speed))) - ((←lead_car.speed)))) ∧ (((𝐗 ((←lead_car.speed))) - ((←lead_car.speed))) ≤ (0.5)))]
abbrev A5 := LLTL[(((←lead_dist)) > ((←buffer_dist))) ∧ (((←self.speed)) = (0))]
abbrev A6 := LLTL[𝐆 ((𝐗 ((←lead_dist))) = (((←lead_dist)) - ((←true_relative_speed))))]

abbrev assumptions : TraceSet TraceState := LLTL[A0 ∧ A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6]

-- Internal Assumptions 

abbrev i_assumptions : TraceSet TraceState := LLTL[⊤]

-- Internal Guarantees 
abbrev IG0 := LLTL[𝐆 (((←behind_car)) → (((((←lead_dist)) - (0.1)) ≤ ((←SCENIC_INTERNAL_VAR_0))) ∧ (((←SCENIC_INTERNAL_VAR_0)) ≤ (((←lead_dist)) + (0.1)))))]
abbrev IG1 := LLTL[𝐆 (((←SCENIC_INTERNAL_VAR_1)) = ((←self.speed)))]
abbrev IG2 := LLTL[𝐆 (((𝐗 ((←SCENIC_INTERNAL_VAR_0))) ≤ (((←p_buffer_dist)) + (0.1))) → ((𝐗 ((←SCENIC_INTERNAL_VAR_4))) = (-(1))))]
abbrev IG3 := LLTL[𝐆 ((((←SCENIC_INTERNAL_VAR_4)) = (-(1))) → (((𝐗 ((←self.speed))) = (0)) ∨ ((𝐗 ((←self.speed))) = (((←self.speed)) - (0.9)))))]

abbrev i_guarantees : TraceSet TraceState := LLTL[IG0 ∧ IG1 ∧ IG2 ∧ IG3]

-- Top Level Guarantees 
abbrev G0 := LLTL[𝐆 (((←lead_dist)) > (5))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

