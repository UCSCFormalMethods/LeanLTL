import LeanLTL.TraceSet.Defs
import Mathlib

/-!
# Basic theory about traces
-/

namespace LeanLTL

namespace TraceSet
variable {σ σ' σ'' α α' β β': Type*}

@[ext]
protected def ext {f g : TraceSet σ} (h : ∀ t, (t ⊨ f) ↔ (t ⊨ g)) : f = g := by
  cases f
  cases g
  rw [mk.injEq]
  funext t
  apply propext
  apply h

@[simp] protected def toFun_defined (s : TraceSet σ) (t : Trace σ) :
    (s.toFun t).isSome := rfl

@[simp] lemma toTraceSet_toFun (f : TraceSet σ) (c : Prop) : f.toFun.toTraceSet c = f := rfl
