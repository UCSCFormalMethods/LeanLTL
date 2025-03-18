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

open Lean

/-- `Xˢ f` is *strong next* (`TraceSet.snext`). Requires that there is a next state in the trace. -/
scoped prefix:100 "Xˢ " => TraceSet.snext

/-- `Xʷ f` is *weak next* (`TraceSet.wnext`). Allows there to not be a next state in the trace. -/
scoped prefix:100 "Xʷ " => TraceSet.wnext

/-- `X f` is *next* for values (`TraceFun.next`). Undefined if there is no next state in the trace. -/
scoped prefix:100 "X " => TraceFun.next

/--
`(←ˢ f)` is *strong get* for values, for use in `LLTL[...]` and `LLTLV[...]`.
Requires that the value exists, otherwise the surrounding proposition evaluates to false.
Uses `TraceFun.sget`.
-/
scoped syntax:min "←ˢ " term : term

/--
`(←ʷ f)` is *weak get* for values, for use in `LLTL[...]` and `LLTLV[...]`.
Allows the value to not exist, in which case the surrounding proposition evaluates to true.
uses `TraceFun.wget`.
-/
scoped syntax:min "←ʷ " term : term

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

/-- Macro to interpret a Lean expression as an LTL proposition. Results in a `TraceSet`. -/
scoped syntax "LLTL[" term "]" : term

/-- Macro to interpret a Lean expression as an LTL value. Results in a `TraceFun`. -/
scoped syntax "LLTLV[" term "]" : term

/--
Pushes any `X` operators into strong/weak get operators.

Example: `X ((←ˢ x) < 10)` becomes `(←ˢ X x) < 10`
-/
partial def pushNexts (stx : Term) : MacroM Term :=
  return ⟨(← go [] stx)⟩
where
  go (xstack : List Syntax) (stx : Syntax) : MacroM Syntax := do
    match stx with
    | `(←ˢ%$tk $x) => `(←ˢ%$tk $(← wrapXs xstack x))
    | `(←ʷ%$tk $x) => `(←ʷ%$tk $(← wrapXs xstack x))
    | `(X%$tk $stx') => go (tk :: xstack) stx'
    | _ =>
      if let .node _ k args := stx then
        let args ← args.mapM (go xstack)
        return Syntax.node (.fromRef stx (canonical := true)) k args
      else
        return stx
  wrapXs (xstack : List Syntax) (stx : Term) : MacroM Term := do
    match xstack with
    | [] => return stx
    | tk::xstack' =>
      let stx' ← wrapXs xstack' stx
      `(X%$tk $stx')

/--
Lifts any strong/weak get operators out of the syntax, creating a TraceSet.

Example:
```lean
(←ˢ x) < 10
```
becomes
```lean
TraceFun.sget LLTLV[x] fun x' => TraceSet.const (x' < 10)
```

Assumption: `pushNexts` has already pushed all `X`'s into the strong/weak get operators.
-/
partial def liftGets (stx : Term) : MacroM Term := do
  let (stx, quantifiers) ← (go stx).run #[]
  let stx ← `(TraceSet.const $(⟨stx⟩))
  quantifiers.foldrM (init := stx) fun (q, n) stx => do
    `($q fun $n => $stx)
where
  /--
  Descend into the expression, extracting strong/weak get operators, adding them to the state.
  The state consists of quantifier/binder tuples.
  -/
  go (stx : Syntax) : StateT (Array (Term × Ident)) MacroM Syntax := do
    match stx with
    | `(←ˢ%$tk $x) => mkBinderFor x (← withRef tk `(TraceFun.sget LLTLV[$x]))
    | `(←ʷ%$tk $x) => mkBinderFor x (← withRef tk `(TraceFun.wget LLTLV[$x]))
    | `(←%$tk $x)  => mkBinderFor x (← withRef tk `(TraceFun.sget LLTLV[$x]))
    | _ =>
      if let .node _ k args := stx then
        let args ← args.mapM go
        return Syntax.node (.fromRef stx (canonical := true)) k args
      else
        return stx
  /--
  Find a pre-existing quantifier in the state, or add a new one with a fresh variable name for the binder.
  -/
  mkBinderFor (x : Term) (q : Term) : StateT (Array (Term × Ident)) MacroM Ident := do
    if let some (_, n) := (← get).find? fun (q', _) => q == q' then
      return n
    else
      let name ← withFreshMacroScope <| MonadQuotation.addMacroScope <| Name.mkSimple <| mkBaseNameFor x
      let n := mkIdentFrom stx name (canonical := true)
      modify fun s => s.push (q, n)
      return n
  /-- Try to make a variable name for the syntax. Concatenates all atoms/names, separeted by underscores. -/
  mkBaseNameFor (stx : Syntax) : String :=
    match stx with
    | .node _ _ args => String.intercalate "_" (args.map mkBaseNameFor).toList
    | .ident _ _ val _ => val.eraseMacroScopes.toString
    | .atom _ s => s
    | .missing => "x"

/--
Converts a term to a trace set, for use in the LLTL macro.
-/
def termToTraceSet (stx : Term) : MacroM Term := do
  let stx ← pushNexts stx
  let stx ← liftGets stx
  return stx

macro_rules
  /- Connectives and quantifiers -/
  | `(LLTL[$x → $y])        => `(TraceSet.imp LLTL[$x] LLTL[$y])
  | `(LLTL[$x ↔ $y])        => `(TraceSet.iff LLTL[$x] LLTL[$y])
  | `(LLTL[$x ∧ $y])        => `(TraceSet.and LLTL[$x] LLTL[$y])
  | `(LLTL[$x ∨ $y])        => `(TraceSet.or LLTL[$x] LLTL[$y])
  | `(LLTL[¬$x])            => `(TraceSet.not LLTL[$x])
  -- todo: support full quantifier syntaxes
  | `(LLTL[∃ $n:ident, $y]) => `(TraceSet.exists fun $n => LLTL[$y])
  | `(LLTL[∀ $n:ident, $y]) => `(TraceSet.forall fun $n => LLTL[$y])
  /- Temporal Operators -/
  | `(LLTL[Xˢ $x])         => `(TraceSet.snext LLTL[$x])
  | `(LLTL[Xʷ $x])         => `(TraceSet.wnext LLTL[$x])
  | `(LLTL[F $x])          => `(TraceSet.finally LLTL[$x])
  | `(LLTL[G $x])          => `(TraceSet.globally LLTL[$x])
  | `(LLTL[$x U $y])       => `(TraceSet.until LLTL[$x] LLTL[$y])
  | `(LLTL[$x R $y])       => `(TraceSet.release LLTL[$x] LLTL[$y])
  /- Parentheses, Constants, and Base Cases -/
  | `(LLTL[($x)])          => `(LLTL[$x])
  | `(LLTL[⊤])             => `(TraceSet.true)
  | `(LLTL[⊥])             => `(TraceSet.false)
  -- Assuming constants are TraceSet constants,
  | `(LLTL[$c:ident])      => `($c)
  -- Process embedded nexts and gets and treat the result as a `Prop`.
  | `(LLTL[$x])            => termToTraceSet x

macro_rules
  -- -- Num -> Num Operators
  -- | `(LLTLV[$x - $y])       => `(TraceFun.sub LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x + $y])       => `(TraceFun.add LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x / $y])       => `(TraceFun.div LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x * $y])       => `(TraceFun.mul LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[- $x])          => `(TraceFun.neg LLTLV[$x])
  -- | `(LLTLV[⌈$x⌉])          => `(TraceFun.ceil LLTLV[$x])
  -- | `(LLTLV[$x ⊓ $y])       => `(TraceFun.min LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x ⊔ $y])       => `(TraceFun.max LLTLV[$x] LLTLV[$y])
  -- -- Num -> Prop Operators
  -- | `(LLTLV[$x == $y])      => `(TraceFun.eq LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x < $y])       => `(TraceFun.lt LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x > $y])       => `(TraceFun.gt LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x ≤ $y])       => `(TraceFun.leq LLTLV[$x] LLTLV[$y])
  -- | `(LLTLV[$x ≥ $y])       => `(TraceFun.geq LLTLV[$x] LLTLV[$y])
  -- Temporal Operators
  | `(LLTLV[X $x])          => `(TraceFun.next LLTLV[$x])
  | `(LLTLV[←ˢ $_])         => Macro.throwError "Unexpected unlifted strong get"
  | `(LLTLV[←ʷ $_])         => Macro.throwError "Unexpected unlifted weak get"
  -- Parentheses, Constants, and Base Cases
  | `(LLTLV[($x)])          => `(LLTLV[$x])
  | `(LLTLV[$x:scientific]) => `(TraceFun.const $x)
  | `(LLTLV[$x:num])        => `(TraceFun.const $x)
  | `(LLTLV[$x])            => return x

section Example
variable {σ : Type} (x y : TraceFun σ Nat)

-- #check LLTL[(←ˢ x) + (←ˢ x) < X (←ˢ x)]
-- /-
-- x.sget fun x_1 ↦ (X x).sget fun X_x ↦ TraceSet.const (x_1 + x_1 < X_x) : TraceSet σ
-- -/

-- #check LLTL[(←ˢ x) = (←ʷ x)]
-- /-
-- x.sget fun x_1 ↦ x.wget fun x ↦ TraceSet.const (x_1 = x) : TraceSet σ
-- -/
-- #check LLTL[(←ʷ x) = (←ˢ x)]
-- /-
-- x.wget fun x_1 ↦ x.sget fun x ↦ TraceSet.const (x_1 = x) : TraceSet σ
-- -/

-- #check LLTL[Xˢ ∃ y, (←ˢ x) < y]
-- /-
-- Xˢ TraceSet.exists fun y ↦ x.sget fun x ↦ TraceSet.const (x < y) : TraceSet σ
-- -/
end Example

end Notation
end LeanLTL
