import LeanLTL.TraceSet.Defs
import LeanLTL.TraceFun.Defs
import LeanLTL.TraceFun.Operations
import Lean.Elab.AuxDef

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

open Lean Meta Elab Term

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
Elaborates the term, coercing it to a trace set.
-/
elab "ensure_trace_set% " t:term : term => do
  let e ← withSynthesizeLight <| elabTerm t none
  let ty ← whnf (← inferType e)
  if ty.isForall then
    let fn ← mkConstWithFreshMVarLevels ``TraceSet.of
    elabAppArgs fn #[] #[.expr e] none false false
  else if ← Meta.isProp ty then
    let fn ← mkConstWithFreshMVarLevels ``TraceSet.const
    elabAppArgs fn #[] #[.expr e] none false false
  else
    -- TODO use ensureHasType
    return e

/--
Elaborates the term, coercing it to a trace set.
-/
elab "ensure_trace_fun% " t:term : term => do
  let e ← withSynthesizeLight <| elabTerm t none
  let ty ← whnf (← inferType e)
  if ty.isForall then
    let fn ← mkConstWithFreshMVarLevels ``TraceFun.of
    elabAppArgs fn #[] #[.expr e] none false false
  else
    -- TODO use ensureHasType
    return e

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
    | `(←%$tk $x)  => `(←%$tk $(← wrapXs xstack x))
    | `(←ʷ%$tk $x) => `(←ʷ%$tk $(← wrapXs xstack x))
    | `(X%$tk $stx') =>
      let res ← go (tk :: xstack) stx'
      if (res.find? (·==tk)).isNone then
        Macro.throwErrorAt tk "superfluous X, expression is time-invariant"
      return res
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

All strong gets come before weak gets.

Assumption: `pushNexts` has already pushed all `X`'s into the strong/weak get operators.
-/
partial def liftGets (stx : Term) : MacroM Term := do
  let (stx, quantifiers) ← (go stx).run #[]
  let stx ← ``(TraceSet.const $(⟨stx⟩))
  let quantifiers := quantifiers.filter (·.1) ++ quantifiers.filter (!·.1)
  quantifiers.foldrM (init := stx) fun (strong, ref, x, n) stx => do
    let qname := if strong then ``TraceFun.sget else ``TraceFun.wget
    let q := mkIdentFrom ref qname (canonical := true)
    `($q LLTLV[$x] fun $n => $stx)
where
  /--
  Descend into the expression, extracting strong/weak get operators, adding them to the state.
  The state consists of strong/ref/value/ident tuples.
  -/
  go (stx : Syntax) : StateT (Array (Bool × Syntax × Term × Ident)) MacroM Syntax := do
    match stx with
    | `(←ˢ%$tk $x) => mkBinderFor true tk x
    | `(←ʷ%$tk $x) => mkBinderFor false tk x
    | `(←%$tk $x)  => mkBinderFor true tk x
    | _ =>
      if let .node _ k args := stx then
        let args ← args.mapM go
        return Syntax.node (.fromRef stx (canonical := true)) k args
      else
        return stx
  /--
  Find a pre-existing quantifier in the state, or add a new one with a fresh variable name for the binder.
  -/
  mkBinderFor (strong : Bool) (ref : Syntax) (x : Term) : StateT (Array (Bool × Syntax × Term × Ident)) MacroM Ident := do
    if let some (_, _, _, n) := (← get).find? fun (strong', _, x', _) => strong == strong' && x == x' then
      return n
    else
      let name ← withFreshMacroScope <| MonadQuotation.addMacroScope <| Name.mkSimple <| mkBaseNameFor x
      let n := mkIdentFrom stx name (canonical := true)
      modify fun s => s.push (strong, ref, x, n)
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
  | `(LLTL[$p]) => withRef p do
    match p with
    | `(∃ $n:ident, $y) => `(TraceSet.exists fun $n => LLTL[$y])
    | `(∀ $n:ident, $y) => `(TraceSet.forall fun $n => LLTL[$y])
    /- Parentheses, Constants, and Base Cases -/
    | `(($p))          => `(LLTL[$p])
    | `(⊤)             => `(TraceSet.true)
    | `(⊥)             => `(TraceSet.false)
    -- Assume constants are TraceSet constants
    | `($c:ident)      => `(ensure_trace_set% $c)
    -- Process embedded nexts and gets and treat the result as a `Prop`.
    | _                => termToTraceSet p

macro_rules
  | `(LLTLV[$v]) => withRef v do
    match v with
    -- Temporal Operators
    | `(X $x)          => `(TraceFun.next LLTLV[$x])
    | `(←ˢ $_)         => Macro.throwError "Unexpected unlifted strong get"
    | `(←ʷ $_)         => Macro.throwError "Unexpected unlifted weak get"
    -- Parentheses, Constants, and Base Cases
    | `(($x))          => `(LLTLV[$x])
    | `($x:scientific) => `(TraceFun.const $x)
    | `($x:num)        => `(TraceFun.const $x)
    | `($x)            => `(ensure_trace_fun% $x)

def stripLLTL (stx : Term) : PrettyPrinter.UnexpandM Term := do
  match stx with
  | `(LLTL[$x]) => return x
  | `($c:ident) => return c
  | _ => return stx

open scoped Elab.Command
open Syntax

/-- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
  | stx => match stx with
  | `($id:ident) =>
    if vars.any (fun var => var.getId == id.getId) then
      mkAntiquotNode id (kind := `term) (isPseudoKind := true)
    else
      stx
  | _ => match stx with
    | Syntax.node i k args => Syntax.node i k (args.map (antiquote vars))
    | stx => stx

local macro "declare_lltl_notation " vars:ident* " : " ltl:term " => " t:term : command => do
  let (c, args) ←
    match t with
    | `($c:ident $args*) => pure (c, args)
    | `($c:ident)        => pure (c, #[])
    | _                  => Macro.throwUnsupported
  let macroLHS : Term := ⟨antiquote vars ltl⟩
  let macroRHSargs : Array Term ← args.mapM (fun arg => `(LLTL[$(⟨antiquote vars arg⟩)]))
  let macroRHS := Syntax.mkApp c macroRHSargs
  let unexpandLHS : Term := Syntax.mkApp (← `($$_:ident)) <| args.map (⟨antiquote vars ·⟩)
  let unexpandRHS ← `(`(LLTL[$macroLHS]))
  let unexpandRHS ← vars.foldrM (init := unexpandRHS) fun var unexpandRHS => `((stripLLTL $var) >>= fun $var => $unexpandRHS)
  `(
  macro_rules
    | `(LLTL[$macroLHS]) => `($macroRHS)
  @[scoped app_unexpander $c]
  aux_def unexpand : PrettyPrinter.Unexpander := fun
    | `($unexpandLHS) => $unexpandRHS
    | _ => throw ()
  )

/- Connectives and quantifiers -/
declare_lltl_notation p q : p → q => TraceSet.imp p q
declare_lltl_notation p q : p ↔ q => TraceSet.iff p q
declare_lltl_notation p q : p ∧ q => TraceSet.and p q
declare_lltl_notation p q : p ∨ q => TraceSet.or p q
declare_lltl_notation p   : ¬ p   => TraceSet.not p

/- Temporal Operators -/
declare_lltl_notation p : Xˢ p => TraceSet.snext p
declare_lltl_notation p : Xʷ p => TraceSet.wnext p
declare_lltl_notation p : F p  => TraceSet.finally p
declare_lltl_notation p : G p  => TraceSet.globally p
declare_lltl_notation p q : p U q => TraceSet.until p q
declare_lltl_notation p q : p R q => TraceSet.release p q

section Example
variable {σ : Type} (p q : TraceSet σ) (x y : TraceFun σ Nat)

/-- info: LLTL[p → ¬q] : TraceSet σ -/
#guard_msgs in #check LLTL[p → ¬ q]

/-- info: LLTL[p → G ¬q] : TraceSet σ -/
#guard_msgs in #check LLTL[p → G (¬ q)]
/-- info: LLTL[G (p → ¬q)] : TraceSet σ -/
#guard_msgs in #check LLTL[G (p → ¬ q)]

-- #check LLTL[1 + 2 < 3]
-- #check LLTL[1 + (←ˢ x) < 3]
-- #check LLTL[(←ˢ x) + (←ˢ x) < X (←ˢ x)]
-- /-
-- x.sget fun x_1 ↦ (X x).sget fun X_x ↦ TraceSet.const (x_1 + x_1 < X_x) : TraceSet σ
-- -/

/-- info: x.sget fun x ↦ y.wget fun y ↦ TraceSet.const (x = y) : TraceSet σ -/
#guard_msgs in #check LLTL[(←ˢ x) = (←ʷ y)]
/-- info: y.sget fun y ↦ x.wget fun x ↦ TraceSet.const (x = y) : TraceSet σ -/
#guard_msgs in #check LLTL[(←ʷ x) = (←ˢ y)]

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
