import LeanLTL.Trace.Defs

/-!
# Functions on traces
-/

namespace LeanLTL
variable {σ σ' σ'' α α' β β': Type*}

/--
A `TraceFun` is a partially-defined function on traces.
Each trace over `Trace α` evaluates to a value in `Option α`.

We need partially definedness for FLTL.
-/
@[ext]
structure TraceFun (σ α : Type*) where
  eval : Trace σ → Option α

instance {σ α : Type*} : CoeFun (TraceFun σ α) (fun _ => Trace σ → (Option α)) where
  coe := TraceFun.eval

attribute [coe] TraceFun.eval

namespace TraceFun

/-!
### Transformations
-/

/-- `TraceFun.map g f` is the composition of `g` and `f`, with `g` mapped to operate on `Option`. -/
protected def map (g : α → α') (f : TraceFun σ α) : TraceFun σ α' where
  eval := Option.map g ∘ f

/-- `TraceFun.map₂ g f f'` composes `g` with "`f ⊗ f'`"
(that's to say, it feeds the outputs of `f` and `f'` into the inputs of `g`). -/
protected def map₂ (g : α → α' → β) (f : TraceFun σ α) (f' : TraceFun σ α') : TraceFun σ β where
  eval t := (f t).bind fun v1 => (f' t).bind fun v2 => g v1 v2

/-- `TraceFun.comap g f` transforms the traces before giving them to `f`. -/
protected def comap (g : Trace σ → Trace σ') (f : TraceFun σ' α) : TraceFun σ α where
  eval := f ∘ g

/-- `TraceFun.lift g f` transforms the states using `g` before giving them to `f`. -/
protected def lift (g : σ → σ') (f : TraceFun σ' α) : TraceFun σ α := f.comap (Trace.map g)

/-!
### Basic trace functions
-/

/-- The constant `TraceFun`. -/
protected def const (c : α) : TraceFun σ α where eval _ := c

/-- Projection of state 0. -/
def proj0 : TraceFun σ σ where eval t := t.toFun 0

/-- Lifts a function on states to a `TraceFun` by applying it to state 0. -/
protected def of (f : σ → α) : TraceFun σ α := proj0.map f

/-- Replaces undefined values in `f` with `c`. -/
def fixConst (f : TraceFun σ Prop) (c : Prop) : TraceFun σ Prop where
  eval t := some <| (f t).getD c

/-- Replaces undefined values in `f` with `False`. -/
def fixFalse (f : TraceFun σ Prop) : TraceFun σ Prop := TraceFun.fixConst f False

/-- Replaces undefined values in `f` with `True`. -/
def fixTrue (f : TraceFun σ Prop) : TraceFun σ Prop := TraceFun.fixConst f True

/-!
### Temporal Operators
-/
protected def shift (f : TraceFun σ α) (i : ℕ) : TraceFun σ α where
  eval t :=
    if h : i < t.length
    then f (t.shift i h)
    else none

protected abbrev next  (f : TraceFun σ α) : TraceFun σ α := f.shift 1

end TraceFun
