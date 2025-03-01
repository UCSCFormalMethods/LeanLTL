import LeanLTL.TraceSet.Defs

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

-- scoped syntax "FLTL[" term "]" : term

-- macro_rules
--   -- Num -> Num Operators
--   | `(FLTL[$x - $y])       => `(TraceFun.sub FLTL[$x] FLTL[$y])
--   | `(FLTL[$x + $y])       => `(TraceFun.add FLTL[$x] FLTL[$y])
--   | `(FLTL[$x / $y])       => `(TraceFun.div FLTL[$x] FLTL[$y])
--   | `(FLTL[$x * $y])       => `(TraceFun.mul FLTL[$x] FLTL[$y])
--   | `(FLTL[- $x])          => `(TraceFun.neg FLTL[$x])
--   | `(FLTL[⌈$x⌉])          => `(TraceFun.ceil FLTL[$x])
--   -- Num -> Prop Operators
--   | `(FLTL[$x == $y])      => `(TraceFun.eq FLTL[$x] FLTL[$y])
--   | `(FLTL[$x < $y])       => `(TraceFun.lt FLTL[$x] FLTL[$y])
--   | `(FLTL[$x > $y])       => `(TraceFun.gt FLTL[$x] FLTL[$y])
--   | `(FLTL[$x ≤ $y])       => `(TraceFun.leq FLTL[$x] FLTL[$y])
--   | `(FLTL[$x ≥ $y])       => `(TraceFun.geq FLTL[$x] FLTL[$y])
--   | `(FLTL[$x ⊓ $y])       => `(TraceFun.min FLTL[$x] FLTL[$y])
--   | `(FLTL[$x ⊔ $y])       => `(TraceFun.max FLTL[$x] FLTL[$y])
--   -- Boolean -> Boolean Operators
--   | `(FLTL[$x → $y])       => `(TraceSet.imp FLTL[$x] FLTL[$y])
--   | `(FLTL[$x ∧ $y])       => `(TraceSet.and FLTL[$x] FLTL[$y])
--   | `(FLTL[$x ∨ $y])       => `(TraceSet.or FLTL[$x] FLTL[$y])
--   | `(FLTL[¬$x])           => `(TraceSet.not FLTL[$x])
--   -- General Temporal Operators
--   | `(FLTL[Xˢ $x])         => `(TraceSet.snext FLTL[$x])
--   | `(FLTL[Xʷ $x])         => `(TraceSet.wnext FLTL[$x])
--   | `(FLTL[X $x])          => `(TraceFun.next FLTL[$x])
--   -- Prop Temporal Operators
--   | `(FLTL[F $x])          => `(TraceSet.finally FLTL[$x])
--   | `(FLTL[G $x])          => `(TraceSet.globally FLTL[$x])
--   | `(FLTL[$x U $y])       => `(TraceSet.until FLTL[$x] FLTL[$y])
--   -- | `(FLTL[$x R $y])       => `(TraceSet.release FLTL[$x] FLTL[$y])
--   -- Parentheses, Constants, and Base Cases
--   | `(FLTL[($x)])          => `(FLTL[$x])
--   | `(FLTL[⊤])             => `(TraceSet.true)
--   | `(FLTL[⊥])             => `(TraceSet.false)
--   | `(FLTL[$x:scientific]) => `(TraceFun.const $x)
--   | `(FLTL[$x:num])        => `(TraceFun.const $x)
--   | `(FLTL[$x])            => return x


end Notation
end LeanLTL
