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

open scoped symmDiff

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
  else if ← Meta.isProp e then
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
Pushes any `𝐗` operators into strong/weak get operators.

Example: `𝐗 ((←ˢ x) < 10)` becomes `(←ˢ 𝐗 x) < 10`
-/
partial def pushNexts (stx : Term) : MacroM Term :=
  return ⟨(← go [] stx)⟩
where
  go (xstack : List Syntax) (stx : Syntax) : MacroM Syntax := do
    match stx with
    | `(←ˢ%$tk $x) => `(←ˢ%$tk $(← wrapXs xstack x))
    | `(←%$tk $x)  => `(←%$tk $(← wrapXs xstack x))
    | `(←ʷ%$tk $x) => `(←ʷ%$tk $(← wrapXs xstack x))
    | `(𝐗%$tk $stx') =>
      let res ← go (tk :: xstack) stx'
      if (res.find? (·==tk)).isNone then
        Macro.throwErrorAt tk "superfluous 𝐗, expression is time-invariant"
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
      `(𝐗%$tk $stx')

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
--  let stx ← ``(TraceSet.const $(⟨stx⟩))
  let quantifiers := quantifiers.filter (·.1) ++ quantifiers.filter (!·.1)
  quantifiers.foldrM (init := ⟨stx⟩) fun (strong, ref, x, n) stx => do
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
    -- todo: support full quantifier syntaxes
    | `(∃ $n:ident, $y) => `((⨆ $n:ident, LLTL[$y] : TraceSet _))
    | `(∀ $n:ident, $y) => `((⨅ $n:ident, LLTL[$y] : TraceSet _))
    /- Parentheses, Constants, and Base Cases -/
    | `(($p))          => `(LLTL[$p])
    | `(⊤)             => `((⊤ : TraceSet _))
    | `(⊥)             => `((⊥ : TraceSet _))
    | `($p → $q)       => `((LLTL[$p] ⇨ LLTL[$q] : TraceSet _))
    | `($p ↔ $q)       => `((LLTL[$p] ⇔ LLTL[$q] : TraceSet _))
    | `($p ∧ $q)       => `((LLTL[$p] ⊓ LLTL[$q] : TraceSet _))
    | `($p ∨ $q)       => `((LLTL[$p] ⊔ LLTL[$q] : TraceSet _))
    | `(¬ $p)          => `((LLTL[$p]ᶜ : TraceSet _))
    -- -- Assume constants are TraceSet constants
    -- | `($c:ident)      => `(ensure_trace_set% $c)
    -- | `($c:ident $xs*) => `(ensure_trace_set% ($c $xs*))
    -- Process embedded nexts and gets and treat the result as a `Prop`.
    | _                => termToTraceSet <| ← `(ensure_trace_set% $p)

macro_rules
  | `(LLTLV[$v]) => withRef v do
    match v with
    -- Temporal Operators
    | `(𝐗 $x)          => `(TraceFun.next LLTLV[$x])
    | `(←ˢ $_)         => Macro.throwError "Unexpected unlifted strong get"
    | `(←ʷ $_)         => Macro.throwError "Unexpected unlifted weak get"
    -- Parentheses, Constants, and Base Cases
    | `(($x))          => `(LLTLV[$x])
    | `($x:scientific) => `(TraceFun.const $x)
    | `($x:num)        => `(TraceFun.const $x)
    | `($x)            => `(ensure_trace_fun% $x)

def stripLLTL (stx : Term) : Term :=
  match stx with
  | `(LLTL[$x]) => x
  | `($c:ident) => c
  | _ => stx

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
  let unexpandRHS ← vars.foldrM (init := unexpandRHS) fun var unexpandRHS => `(let $var:ident := stripLLTL $var; $unexpandRHS)
  `(
  macro_rules
    | `(LLTL[$macroLHS]) => `(($macroRHS : TraceSet _))
  @[scoped app_unexpander $c]
  aux_def unexpand : PrettyPrinter.Unexpander := fun
    | `($unexpandLHS) => $unexpandRHS
    | _ => throw ()
  )

/- Temporal Operators -/
declare_lltl_notation p : 𝐗ˢ(i) p => SShift.sshift i p
declare_lltl_notation p : 𝐗ʷ(i) p => WShift.wshift i p
declare_lltl_notation p : 𝐗ˢ p => SShift.sshift 1 p
declare_lltl_notation p : 𝐗ʷ p => WShift.wshift 1 p
declare_lltl_notation p : 𝐅 p  => HasFinally.finally p
declare_lltl_notation p : 𝐆 p  => HasGlobally.globally p
declare_lltl_notation p q : p 𝐔 q => HasUntil.until p q
declare_lltl_notation p q : p 𝐑 q => HasRelease.release p q

open PrettyPrinter Delaborator SubExpr

@[scoped app_delab HImp.himp]
def delab_himp : Delab := whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
  let_expr HImp.himp ty _ _ _ := (← getExpr) | failure
  let ty ← whnfR ty
  guard <| ty.isAppOf ``TraceSet
  let p := stripLLTL (← withAppFn <| withAppArg delab)
  let q := stripLLTL (← withAppArg delab)
  let stx ← annotateCurPos <| ← `($p → $q)
  `(LLTL[$stx])

@[scoped app_delab Min.min]
def delab_inf : Delab := whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
  let_expr Min.min ty _ _ _ := (← getExpr) | failure
  let ty ← whnfR ty
  guard <| ty.isAppOf ``TraceSet
  let p := stripLLTL (← withAppFn <| withAppArg delab)
  let q := stripLLTL (← withAppArg delab)
  let stx ← annotateCurPos <| ← `($p ∧ $q)
  `(LLTL[$stx])

@[scoped app_delab Max.max]
def delab_sup : Delab := whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
  let_expr Max.max ty _ _ _ := (← getExpr) | failure
  let ty ← whnfR ty
  guard <| ty.isAppOf ``TraceSet
  let p := stripLLTL (← withAppFn <| withAppArg delab)
  let q := stripLLTL (← withAppArg delab)
  let stx ← annotateCurPos <| ← `($p ∨ $q)
  `(LLTL[$stx])

@[scoped app_delab HasCompl.compl]
def delab_compl : Delab := whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
  let_expr HasCompl.compl ty _ _ := (← getExpr) | failure
  let ty ← whnfR ty
  guard <| ty.isAppOf ``TraceSet
  let p := stripLLTL (← withAppArg delab)
  let stx ← annotateCurPos <| ← `(¬$p)
  `(LLTL[$stx])

section Example
variable {σ : Type} (p q : TraceSet σ) (x y : TraceFun σ Nat)

/-- info: LLTL[p ∧ q] : TraceSet σ -/
#guard_msgs in #check LLTL[p ∧ q]
/-- info: LLTL[p ∨ q] : TraceSet σ -/
#guard_msgs in #check LLTL[p ∨ q]
/-- info: LLTL[¬p] : TraceSet σ -/
#guard_msgs in #check LLTL[¬ p]
/-- info: LLTL[p → q] : TraceSet σ -/
#guard_msgs in #check LLTL[p → q]
/-- info: LLTL[p 𝐔 q] : TraceSet σ -/
#guard_msgs in #check LLTL[p 𝐔 q]
/-- info: LLTL[p 𝐑 q] : TraceSet σ -/
#guard_msgs in #check LLTL[p 𝐑 q]
/-- info: LLTL[𝐅 p] : TraceSet σ -/
#guard_msgs in #check LLTL[𝐅 p]
/-- info: LLTL[𝐆 p] : TraceSet σ -/
#guard_msgs in #check LLTL[𝐆 p]
/-- info: LLTL[𝐗ˢ p] : TraceSet σ -/
#guard_msgs in #check LLTL[𝐗ˢ p]
/-- info: LLTL[𝐗ʷ p] : TraceSet σ -/
#guard_msgs in #check LLTL[𝐗ʷ p]

/-- info: LLTL[p → ¬q] : TraceSet σ -/
#guard_msgs in #check LLTL[p → ¬ q]

/-- info: LLTL[p → 𝐆 ¬q] : TraceSet σ -/
#guard_msgs in #check LLTL[p → 𝐆 (¬ q)]
/-- info: LLTL[𝐆 (p → ¬q)] : TraceSet σ -/
#guard_msgs in #check LLTL[𝐆 (p → ¬ q)]

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
