import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace SafeThrottleFilter

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
  N4: ℚ
deriving Inhabited

structure FuncOutput where
  N2: ℚ
  N1: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let dist := t.N0;
  let speed := t.N3;
  let throttle := t.N4;
  let last_dist := t.N1;

  let p_relative_speed := (last_dist) - (dist);
  let p_stopping_time := ⌈(speed) / (0.9)⌉;
  let p_rel_dist_covered := (p_stopping_time) * ((p_relative_speed) + (1.6));
  let p_delta_stopping_time := ⌈((speed) + (0.5)) / (0.9)⌉;
  let p_max_rdc_delta := ((p_delta_stopping_time) * ((((p_relative_speed) + (0.9)) + (0.5)) + ((2) * (1.6)))) - (p_rel_dist_covered);
  let p_buffer_dist := (((5) + ((0) ⊔ ((p_max_rdc_delta) + (p_rel_dist_covered)))) + (5.4)) + (1);
  let last_dist := dist;
  if ((dist) < ((p_buffer_dist) + (1)))
  then
    {N2 := (-(1.0)), N1 := (last_dist)}
  else
    {N2 := (throttle), N1 := (last_dist)}
  

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N2 : TraceFun TraceState ℚ := TraceFun.map (·.N2) CF 
def CF_N1 : TraceFun TraceState ℚ := TraceFun.map (·.N1) CF 

-- Prop Signals

-- Numerical Signals
abbrev dist : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev last_dist : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev modulated_throttle : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev speed : TraceFun TraceState ℚ := TraceFun.of (·.N3)
abbrev throttle : TraceFun TraceState ℚ := TraceFun.of (·.N4)

-- Defs
abbrev p_relative_speed := LLTLV[((dist)) - (𝐗 ((dist)))]
abbrev p_stopping_time := LLTLV[⌈(𝐗 ((speed))) / (0.9)⌉]
abbrev p_rel_dist_covered := LLTLV[((p_stopping_time)) * (((p_relative_speed)) + (1.6))]
abbrev p_delta_stopping_time := LLTLV[⌈((𝐗 ((speed))) + (0.5)) / (0.9)⌉]
abbrev p_max_rdc_delta := LLTLV[(((p_delta_stopping_time)) * (((((p_relative_speed)) + (0.9)) + (0.5)) + ((2) * (1.6)))) - ((p_rel_dist_covered))]
abbrev p_buffer_dist := LLTLV[(((5) + ((0) ⊔ (((p_max_rdc_delta)) + ((p_rel_dist_covered))))) + (5.4)) + (1)]

-- Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties 
abbrev F0 := LLTL[(←last_dist) = (←0.0)]
abbrev F1 := LLTL[𝐆 ((←modulated_throttle) = (←CF_N2))]
abbrev F2 := LLTL[𝐆 ((𝐗 (←last_dist) = (←CF_N1)))]

abbrev fprops : TraceSet TraceState := LLTL[F0 ∧ F1 ∧ F2]

-- Guarantees 
abbrev G0 := LLTL[𝐆 (((𝐗 ((←dist))) ≤ (((←p_buffer_dist)) + (0.1))) → ((𝐗 ((←modulated_throttle))) = (-(1))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

