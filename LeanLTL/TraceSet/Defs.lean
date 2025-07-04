import LeanLTL.Trace.Defs
import LeanLTL.TraceFun.Defs
import LeanLTL.Logics.Notation

/-!
# Sets of traces

In our theory, we use sets of traces as a core object.

Given an LTL formula, we can replace it with its interpretation as a set of traces that satisfy it.
-/

namespace LeanLTL
variable {σ σ' σ'' α α' β β': Type*}

/--
A `TraceSet` is a set of traces.
We use `t ⊨ f` notation (`t` satisfies `f`) instead of `t ∈ f`.

The variable `f` here is used to represent a trace set since it is a generalization of a formula.
-/
structure TraceSet (σ : Type*) where
  sat : Trace σ → Prop

/--
`t ⊨ p` means that `t` satisfies `p`. That is, `t` is an element of the trace set `p`.
-/
notation t " ⊨ " p => TraceSet.sat p t

namespace TraceSet

def sem_entail (p : TraceSet σ) : Prop := ∀ (t : Trace σ), t ⊨ p
def sem_entail_fin (p : TraceSet σ) : Prop := ∀ (t : Trace σ), t.Finite → t ⊨ p
def sem_entail_inf (p : TraceSet σ) : Prop := ∀ (t : Trace σ), t.Infinite → t ⊨ p

notation "⊨ " p => TraceSet.sem_entail p
notation "⊨ᶠ " p => TraceSet.sem_entail_fin p
notation "⊨ⁱ " p => TraceSet.sem_entail_inf p

/-- Semantic implication. -/
def sem_imp (f₁ f₂ : TraceSet σ) : Prop := ∀ (t : Trace σ), (t ⊨ f₁) → (t ⊨ f₂)
def sem_imp_fin (f₁ f₂ : TraceSet σ) : Prop := ∀ (t : Trace σ) (_: t.Finite), (t ⊨ f₁) → (t ⊨ f₂)
def sem_imp_inf (f₁ f₂ : TraceSet σ) : Prop := ∀ (t : Trace σ) (_: t.Infinite), (t ⊨ f₁) → (t ⊨ f₂)

/-- `f₁ ⇒ f₂` means that whenever a trace satisfies `f₁` then it satisfies `f₂` -/
notation f₁ " ⇒ " f₂ => TraceSet.sem_imp f₁ f₂

/-- `f₁ ⇒ᶠ f₂` means that whenever a finite trace satisfies `f₁` then it satisfies `f₂` -/
notation f₁ " ⇒ᶠ " f₂ => TraceSet.sem_imp_fin f₁ f₂

/-- `f₁ ⇒ⁱ f₂` means that whenever a finite trace satisfies `f₁` then it satisfies `f₂` -/
notation f₁ " ⇒ⁱ " f₂ => TraceSet.sem_imp_inf f₁ f₂

/-- Creates a trace set of all those traces whose state 0 satisfies `p`. -/
protected def of (p : σ → Prop) : TraceSet σ where
  sat t := p (t.toFun 0)

protected def map (g : Prop → Prop) (f : TraceSet σ) : TraceSet σ where
  sat t := g (t ⊨ f)

protected def map₂ (g : Prop → Prop → Prop) (f₁ f₂ : TraceSet σ) : TraceSet σ where
  sat t := g (t ⊨ f₁) (t ⊨ f₂)

end TraceSet


/-!
### LTL constants and operators
-/

/-!
#### Propositional logic
-/

protected def TraceSet.const (p : Prop) : TraceSet σ where
  sat _ := p

protected def TraceSet.true : TraceSet σ := TraceSet.const True
protected def TraceSet.false : TraceSet σ := TraceSet.const False

protected def TraceSet.not (f : TraceSet σ) : TraceSet σ := TraceSet.map (¬ ·) f
protected def TraceSet.and (f₁ f₂ : TraceSet σ) : TraceSet σ := TraceSet.map₂ (· ∧ ·) f₁ f₂
protected def TraceSet.or (f₁ f₂ : TraceSet σ) : TraceSet σ := TraceSet.map₂ (· ∨ ·) f₁ f₂
protected def TraceSet.imp (f₁ f₂ : TraceSet σ) : TraceSet σ := TraceSet.map₂ (· → ·) f₁ f₂
protected def TraceSet.iff (f₁ f₂ : TraceSet σ) : TraceSet σ := TraceSet.map₂ (· ↔ ·) f₁ f₂

protected def TraceSet.exists (p : α → TraceSet σ) : TraceSet σ where
  sat t := ∃ x, (t ⊨ p x)
protected def TraceSet.forall (p : α → TraceSet σ) : TraceSet σ where
  sat t := ∀ x, (t ⊨ p x)

protected def TraceSet.some (s : Set (TraceSet σ)) : TraceSet σ where
  sat t := ∃ p ∈ s, (t ⊨ p)
protected def TraceSet.all (s : Set (TraceSet σ)) : TraceSet σ where
  sat t := ∀ p ∈ s, (t ⊨ p)

/-!
#### Temporal operators
-/

def TraceFun.get (d: Prop) (a : TraceFun σ α) (f : α -> TraceSet σ) : TraceSet σ where
  sat t :=
    match a t with
    | none => d
    | some val => t ⊨ (f val)

def TraceFun.wget (a : TraceFun σ α) (f : α -> TraceSet σ) : TraceSet σ := TraceFun.get True a f
def TraceFun.sget (a : TraceFun σ α) (f : α -> TraceSet σ) : TraceSet σ := TraceFun.get False a f

/--
Weak shift.
-/
protected def TraceSet.wshift (i : ℕ) (f : TraceSet σ) : TraceSet σ where
  sat t := ∀ h : i < t.length, t.shift i h ⊨ f

/--
Strong shift.
-/
protected def TraceSet.sshift (i : ℕ) (f : TraceSet σ) : TraceSet σ where
  sat t := ∃ h : i < t.length, t.shift i h ⊨ f
-- TODO: thm for (f.toFun.shift i).fixFalseConvert

protected abbrev TraceSet.wnext (f : TraceSet σ) : TraceSet σ := f.wshift 1
protected abbrev TraceSet.snext (f : TraceSet σ) : TraceSet σ := f.sshift 1

-- TODO: @Daniel, do we want wshift for f₁ here?
-- TODO: Prove that f₁ can use strong shift instead, or maybe just normal shift?
protected def TraceSet.until (f₁ f₂ : TraceSet σ) : TraceSet σ where
  sat t := ∃ n, (∀ i < n, t ⊨ f₁.wshift i) ∧ (t ⊨ f₂.sshift n)

protected def TraceSet.release (f₁ f₂ : TraceSet σ) : TraceSet σ :=
  (f₁.not.until f₂.not).not

protected def TraceSet.finally (f : TraceSet σ) : TraceSet σ := TraceSet.true.until f

protected def TraceSet.globally (f : TraceSet σ) : TraceSet σ := f.not.finally.not

instance : HasFinally (TraceSet σ) := ⟨TraceSet.finally⟩
instance : HasGlobally (TraceSet σ) := ⟨TraceSet.globally⟩
instance : HasUntil (TraceSet σ) := ⟨TraceSet.until⟩
instance : HasRelease (TraceSet σ) := ⟨TraceSet.release⟩

instance : WShift (TraceSet σ) := ⟨TraceSet.wshift⟩
instance : SShift (TraceSet σ) := ⟨TraceSet.sshift⟩
