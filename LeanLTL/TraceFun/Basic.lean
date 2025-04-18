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

@[simp] lemma shift_apply_eq_some_iff (t : Trace σ) (f : TraceFun σ α) (n : ℕ) (x : α) :
    (f.shift n) t = some x ↔ ∃ h, f (t.shift n h) = some x := by
  simp [TraceFun.shift]

@[simp]
theorem of_eval!_apply_singleton {σ α} [Inhabited α] (p : σ → α) {s} :
    (TraceFun.of p).eval! (Trace.singleton s) = p s := rfl

@[simp]
theorem of_eval!_apply_unshift {σ α} [Inhabited α] (p : σ → α) {s t} :
    (TraceFun.of p).eval! (Trace.unshift s t) = p s := rfl

@[simp]
theorem next_apply_unshift {σ α} (f : TraceFun σ α) (s : σ) (t : Trace σ) :
    (TraceFun.next f) (Trace.unshift s t) = f t := by
  simp [TraceFun.next, TraceFun.shift]

/- TODO

@[simp]
lemma eval_map (f: TraceFun σ α) (q : α → α') (t) :
    (TraceFun.map q f) t = (f t).map q := by rfl
@[simp]
lemma eval_map₂ (g : α → α' → β) (f₁ : TraceFun σ α) (f₂ : TraceFun σ α') (t):
    ((TraceFun.map₂ g f₁ f₂) t) = ((f₁ t).bind fun v1 => (f₂ t).bind fun v2 => some (g v1 v2)) := by rfl

def _root_.Option.fixFalse (op: Option Prop) : Prop := op.getD False
@[simp]
lemma _root_.Option.fixFalse_some (p: Prop) : (some p).fixFalse ↔ p := Iff.rfl
@[simp]
lemma _root_.Option.fixFalse_none : none.fixFalse ↔ False := Iff.rfl

def _root_.Option.fixTrue (op: Option Prop) : Prop := op.getD True
@[simp]
lemma _root_.Option.fixTrue_some (p: Prop) : (some p).fixTrue ↔ p := Iff.rfl
@[simp]
lemma _root_.Option.fixTrue_none : none.fixTrue ↔ True := Iff.rfl


@[push_ltl] lemma apply_neg_eq (t: Trace σ) (f : TraceFun σ 𝕜) : (f.neg) t = (f t).map (-·) := by rfl
@[push_ltl] lemma apply_ceil_eq (t: Trace σ) (f : TraceFun σ ℚ) : (f.ceil) t = (f t).map (⌈·⌉) := by
  simp [TraceFun.ceil]; cases f t <;> rfl
@[push_ltl] lemma apply_add_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  ((f₁.add f₂) t) = (f₁ t |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 + v2)) := by rfl
@[push_ltl] lemma apply_sub_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  ((f₁.sub f₂) t) = ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 - v2)) := by rfl
@[push_ltl] lemma apply_mul_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  ((f₁.mul f₂) t) = ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 * v2)) := by rfl
@[push_ltl] lemma apply_div_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  ((f₁.div f₂) t) = ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 / v2)) := by rfl
@[push_ltl] lemma apply_min_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  ((f₁.min f₂) t) = ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 ⊓ v2)) := by rfl
@[push_ltl] lemma apply_max_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  ((f₁.max f₂) t) = ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 ⊔ v2)) := by rfl
@[push_ltl] lemma apply_eq_eq (t: Trace σ) (f₁ f₂ : TraceFun σ α) :
  (t ⊨ (f₁.eq f₂)) ↔ ((f₁ t) |>.bind fun v1 => f₂ t |>.bind fun v2 => (v1 = v2)).fixTrue := by
  cases h₁: f₁ t <;> cases h₂: f₂ t <;>
  simp_all [TraceSet.mem, TraceFun.eq, TraceFun.map₂, TraceFun.fixConstConvert, TraceFun.fixConst, Option.get]
  <;> repeat split
  <;> simp_all

@[push_ltl] lemma apply_lt_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  (t⊨(f₁.lt f₂)) ↔ ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 < v2)).fixTrue := by
  cases h₁: f₁ t <;> cases h₂: f₂ t <;>
  simp_all [TraceSet.mem, TraceFun.lt, TraceFun.map₂, TraceFun.fixConstConvert, TraceFun.fixConst, Option.get]
  <;> repeat split
  <;> simp_all
@[push_ltl] lemma apply_gt_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  (t⊨(f₁.gt f₂)) ↔ ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 > v2)).fixTrue := by
  cases h₁: f₁ t <;> cases h₂: f₂ t <;>
  simp_all [TraceSet.mem, TraceFun.gt, TraceFun.map₂, TraceFun.fixConstConvert, TraceFun.fixConst, Option.get]
  <;> repeat split
  <;> simp_all
@[push_ltl] lemma apply_leq_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  (t⊨(f₁.leq f₂)) ↔ ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 ≤ v2)).fixTrue := by
  cases h₁: f₁ t <;> cases h₂: f₂ t <;>
  simp_all [TraceSet.mem, TraceFun.leq, TraceFun.map₂, TraceFun.fixConstConvert, TraceFun.fixConst, Option.get]
  <;> repeat split
  <;> simp_all
@[push_ltl] lemma apply_geq_eq (t: Trace σ) (f₁ f₂ : TraceFun σ 𝕜) :
  (t⊨(f₁.geq f₂)) ↔ ((f₁ t) |>.bind fun v1 => f₂.eval t |>.bind fun v2 => (v1 ≥ v2)).fixTrue := by
  cases h₁: f₁ t <;> cases h₂: f₂ t <;>
  simp_all [TraceSet.mem, TraceFun.geq, TraceFun.map₂, TraceFun.fixConstConvert, TraceFun.fixConst, Option.get]
  <;> repeat split
  <;> simp_all


@[push_ltl] lemma apply_shift_eq (t: Trace σ) (f : TraceFun σ α) (c: ℕ) : ((f.shift c) t) =
  if h: c < t.length
  then f (t.shift c h)
  else none := by
  rfl
-/
