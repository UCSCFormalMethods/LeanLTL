import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

namespace MedianDistanceFilterSemantics

structure TraceState where
  -- Props
  -- Numbers
  N0: ℚ
  N1: ℚ
  N2: ℚ
  N3: ℚ
deriving Inhabited

structure FuncOutput where
  N3: ℚ
deriving Inhabited

def ComponentFunc (t: TraceState) : FuncOutput :=
  let dist1 := t.N0;
  let dist2 := t.N1;
  let dist3 := t.N2;

  let out_dist := (((dist1) ⊔ (dist2)) ⊓ ((dist1) ⊔ (dist2))) ⊓ ((dist2) ⊔ (dist3));
  {N3 := (out_dist)}

def CF : TraceFun TraceState FuncOutput := TraceFun.of ComponentFunc
def CF_N3 : TraceFun TraceState ℚ := TraceFun.map (·.N3) CF 

-- Prop Signals

-- Numerical Signals
abbrev dist1 : TraceFun TraceState ℚ := TraceFun.of (·.N0)
abbrev dist2 : TraceFun TraceState ℚ := TraceFun.of (·.N1)
abbrev dist3 : TraceFun TraceState ℚ := TraceFun.of (·.N2)
abbrev out_dist : TraceFun TraceState ℚ := TraceFun.of (·.N3)

-- Defs

-- Assumptions 

abbrev assumptions : TraceSet TraceState := LLTL[⊤]

-- Function Properties 
abbrev F0 := LLTL[𝐆 ((←ˢout_dist) = (←ˢCF_N3))]

abbrev fprops : TraceSet TraceState := LLTL[F0]

-- Guarantees 
abbrev G0 := LLTL[𝐆 (((←ˢout_dist)) = (((((←ˢdist1)) ⊔ ((←ˢdist2))) ⊓ (((←ˢdist1)) ⊔ ((←ˢdist2)))) ⊓ (((←ˢdist2)) ⊔ ((←ˢdist3)))))]

abbrev guarantees : TraceSet TraceState := LLTL[G0]

