import LeanLTL.TraceSet.ToFun
import Mathlib

/-!
# Basic arithmetic operations for trace functions
-/

namespace LeanLTL
variable {σ σ' σ'' α α' β β' γ : Type*}

variable {𝕜 : Type*} [LinearOrderedField 𝕜]

-- ## Num -> Num Operators
protected def TraceFun.neg (f : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map (- ·) f
protected def TraceFun.ceil (f : TraceFun σ ℚ) : TraceFun σ ℚ := TraceFun.map (⌈·⌉) f
protected def TraceFun.add (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· + ·) f₁ f₂
protected def TraceFun.sub (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· - ·) f₁ f₂
protected def TraceFun.mul (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· * ·) f₁ f₂
protected def TraceFun.div (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· / ·) f₁ f₂
protected def TraceFun.min (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· ⊓ ·) f₁ f₂
protected def TraceFun.max (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· ⊔ ·) f₁ f₂

-- ## Num -> Prop Operators
protected def TraceFun.eq (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· = ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.lt (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· < ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.gt (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· > ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.le (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· ≤ ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.ge (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· ≥ ·) f₁ f₂ |>.toTraceSetTrue

variable {f g : TraceFun σ 𝕜} {t : Trace σ} {x y : 𝕜}

@[push_ltl] theorem TraceFun.neg_apply : (TraceFun.neg f) t = (f t).map (-·) := rfl
@[push_ltl] theorem TraceFun.ceil_apply {f : TraceFun σ ℚ} : (TraceFun.ceil f) t = (f t).map (fun x => (⌈x⌉ : ℚ)) := by
  simp [TraceFun.ceil, TraceFun.map]
@[push_ltl] theorem TraceFun.add_apply : (TraceFun.add f g) t = (f t).bind fun x => (g t).bind fun y => some (x + y) := rfl
@[push_ltl] theorem TraceFun.sub_apply : (TraceFun.sub f g) t = (f t).bind fun x => (g t).bind fun y => some (x - y) := rfl
@[push_ltl] theorem TraceFun.mul_apply : (TraceFun.mul f g) t = (f t).bind fun x => (g t).bind fun y => some (x * y) := rfl
@[push_ltl] theorem TraceFun.div_apply : (TraceFun.div f g) t = (f t).bind fun x => (g t).bind fun y => some (x / y) := rfl
@[push_ltl] theorem TraceFun.min_apply : (TraceFun.min f g) t = (f t).bind fun x => (g t).bind fun y => some (x ⊓ y) := rfl
@[push_ltl] theorem TraceFun.max_apply : (TraceFun.max f g) t = (f t).bind fun x => (g t).bind fun y => some (x ⊔ y) := rfl

@[push_ltl] theorem TraceFun.sat_toTraceSet {f : TraceFun σ Prop} {c : Prop} : (t ⊨ f.toTraceSet c) = (f t).getD c := rfl
@[push_ltl] theorem TraceFun.map_apply {f : TraceFun σ α} {g : α → β} : f.map g t = (f t).map g := rfl
@[push_ltl] theorem TraceFun.map₂_apply {f : TraceFun σ α} {f' : TraceFun σ β} {g : α → β → γ} :
    TraceFun.map₂ g f f' t = (f t).bind fun x => (f' t).bind fun x' => some (g x x') := rfl

@[simp]
theorem _root_.Option.bind_getD_true (x? : Option α) (f : α → Option Prop) :
    (x?.bind f).getD True ↔ ∀ x : α, x? = some x → (f x).getD True := by
  cases x? <;> simp

@[push_ltl] theorem TraceFun.sat_eq_apply (f g : TraceFun σ α):
    (t ⊨ TraceFun.eq f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x = y)) := by
  simp [TraceFun.eq, push_ltl]

@[push_ltl] theorem TraceFun.sat_lt_apply :
    (t ⊨ TraceFun.lt f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x < y)) := by
  simp [TraceFun.lt, push_ltl]

@[push_ltl] theorem TraceFun.sat_gt_apply :
    (t ⊨ TraceFun.gt f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x > y)) := by
  simp [TraceFun.gt, push_ltl]

@[push_ltl] theorem TraceFun.sat_leq_apply :
    (t ⊨ TraceFun.le f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x ≤ y)) := by
  simp [TraceFun.le, push_ltl]

@[push_ltl] theorem TraceFun.sat_ge_apply :
    (t ⊨ TraceFun.ge f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x ≥ y)) := by
  simp [TraceFun.ge, push_ltl]

end LeanLTL
