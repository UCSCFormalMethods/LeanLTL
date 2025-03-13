import LeanLTL.TraceSet.Defs
import LeanLTL.TraceFun.Defs
import LeanLTL.TraceFun.Operations

import Mathlib

/-!
# LTL notation

This module defines common LTL-like notation.

The `LTL[...]` macro is used to re-intepret Lean term syntax as corresponding LTL operations.

The notations are scoped to the `LeanLTL.Notation` namespace.
Use `open scoped LeanLTL.Notation` to enable.
-/

namespace LeanLTL

namespace Notation

/-- `Xˢ f` is *strong next* (`TraceSet.snext`). Requires that there is a next state in the trace. -/
scoped prefix:100 "Xˢ" => TraceSet.snext

/-- `Xʷ f` is *weak next* (`TraceSet.wnext`). Allows there to not be a next state in the trace. -/
scoped prefix:100 "Xʷ" => TraceSet.wnext


/--
`f U g` is *until* (`TraceSet.until`).
True if there is a point at which a strong shift makes `g` true,
and all shifts of `f` until that point are true.
That is, "there is a point where `g` is strongly true, before which `f` is always weakly true".
-/
scoped infixl:41 " U " => TraceSet.until

/--
`f R g` is *release* (`TraceSet.release`).
True if at every point, if every strong shift to before that point makes `f` false,
then the weak shift to the point makes `g` true.
That is, "`g` is weakly true at the first point `f` is strongly true".
-/
scoped infixl:41 " R " => TraceSet.release

/-- `F f` is *finally* (`TraceSet.finally`).
True if some strong shift is true. -/
scoped prefix:40 "F " => TraceSet.finally

/-- `G f` is *globally* (`TraceSet.globally`).
True if every weak shift is true. -/
scoped prefix:40 "G " => TraceSet.globally

scoped syntax "LLTL[" term "]" : term

macro_rules
  -- Num -> Num Operators
  | `(LLTL[$x - $y])       => `(TraceFun.sub LLTL[$x] LLTL[$y])
  | `(LLTL[$x + $y])       => `(TraceFun.add LLTL[$x] LLTL[$y])
  | `(LLTL[$x / $y])       => `(TraceFun.div LLTL[$x] LLTL[$y])
  | `(LLTL[$x * $y])       => `(TraceFun.mul LLTL[$x] LLTL[$y])
  | `(LLTL[- $x])          => `(TraceFun.neg LLTL[$x])
  | `(LLTL[⌈$x⌉])          => `(TraceFun.ceil LLTL[$x])
  -- Num -> Prop Operators
  | `(LLTL[$x == $y])      => `(TraceFun.eq LLTL[$x] LLTL[$y])
  | `(LLTL[$x < $y])       => `(TraceFun.lt LLTL[$x] LLTL[$y])
  | `(LLTL[$x > $y])       => `(TraceFun.gt LLTL[$x] LLTL[$y])
  | `(LLTL[$x ≤ $y])       => `(TraceFun.leq LLTL[$x] LLTL[$y])
  | `(LLTL[$x ≥ $y])       => `(TraceFun.geq LLTL[$x] LLTL[$y])
  | `(LLTL[$x ⊓ $y])       => `(TraceFun.min LLTL[$x] LLTL[$y])
  | `(LLTL[$x ⊔ $y])       => `(TraceFun.max LLTL[$x] LLTL[$y])
  -- Boolean -> Boolean Operators
  | `(LLTL[$x → $y])       => `(TraceSet.imp LLTL[$x] LLTL[$y])
  | `(LLTL[$x ↔ $y])       => `(TraceSet.iff LLTL[$x] LLTL[$y])
  | `(LLTL[$x ∧ $y])       => `(TraceSet.and LLTL[$x] LLTL[$y])
  | `(LLTL[$x ∨ $y])       => `(TraceSet.or LLTL[$x] LLTL[$y])
  | `(LLTL[¬$x])           => `(TraceSet.not LLTL[$x])
  -- General Temporal Operators
  | `(LLTL[Xˢ $x])         => `(TraceSet.snext LLTL[$x])
  | `(LLTL[Xʷ $x])         => `(TraceSet.wnext LLTL[$x])
  | `(LLTL[X $x])          => `(TraceFun.next LLTL[$x])
  -- Prop Temporal Operators
  | `(LLTL[F $x])          => `(TraceSet.finally LLTL[$x])
  | `(LLTL[G $x])          => `(TraceSet.globally LLTL[$x])
  | `(LLTL[$x U $y])       => `(TraceSet.until LLTL[$x] LLTL[$y])
  | `(LLTL[$x R $y])       => `(TraceSet.release LLTL[$x] LLTL[$y])
  -- Parentheses, Constants, and Base Cases
  | `(LLTL[($x)])          => `(LLTL[$x])
  | `(LLTL[⊤])             => `(TraceSet.true)
  | `(LLTL[⊥])             => `(TraceSet.false)
  | `(LLTL[$x:scientific]) => `(TraceFun.const $x)
  | `(LLTL[$x:num])        => `(TraceFun.const $x)
  | `(LLTL[$x])            => return x


end Notation
end LeanLTL
