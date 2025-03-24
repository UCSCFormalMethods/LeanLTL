import LeanLTL.TraceFun.Defs
import LeanLTL.Trace.Basic
import LeanLTL.Util.SimpAttrs
import Mathlib

/-!
# Basic theory about traces
-/

namespace LeanLTL

namespace TraceFun
variable {σ σ' σ'' α α' β β': Type*}

theorem isSome_fixConst (c: Prop) (f : TraceFun σ Prop) (t : Trace σ) : (f.fixConst c) t |>.isSome := by
  simp [TraceFun.fixConst]

theorem isSome_fixFalse (f : TraceFun σ Prop) (t : Trace σ) : f.fixFalse t |>.isSome := isSome_fixConst False f t

theorem isSome_fixTrue (f : TraceFun σ Prop) (t : Trace σ) : f.fixTrue t |>.isSome := isSome_fixConst True f t

theorem mapPreservesSome (g : α → α') (f : TraceFun σ α) (h : ∀ (t : Trace σ), (f t).isSome) :
    (∀ (t : Trace σ), ((TraceFun.map g f) t).isSome) := by simp_all [TraceFun.map]

theorem map₂PreservesSome (g : α → α' → β) (f : TraceFun σ α) (f' : TraceFun σ α')
    (h₁ : ∀ (t : Trace σ), (f t).isSome) (h₂ : ∀ (t : Trace σ), (f' t).isSome) :
    (∀ (t : Trace σ), ((TraceFun.map₂ g f f') t).isSome) := by
  intro t; specialize h₁ t; specialize h₂ t
  simp_all [TraceFun.map₂, Option.bind, Option.isSome]
  aesop

/-!
### Semantics lemmas
-/

@[push_ltl] lemma const_apply (t : Trace σ) (c : α) : TraceFun.const c t = c := by rfl

@[simp] lemma eval_of_eq [Inhabited α] (f : σ → α) (t : Trace σ) : TraceFun.of f t = (TraceFun.of f).eval! t := rfl

@[simp] lemma eval_proj0_eq [Inhabited σ] (t : Trace σ) : TraceFun.proj0 t = TraceFun.proj0.eval! t := rfl

@[simp] lemma shift_apply (t : Trace σ) (h : t.Infinite) (f : TraceFun σ α) (n : ℕ) :
    (f.shift n) t = f (t.shift n (by simp [h])) := by
  simp [TraceFun.shift, h]
