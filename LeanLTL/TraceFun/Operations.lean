import LeanLTL.TraceSet.ToFun
import Mathlib

/-!
# Basic arithmetic operations for trace functions
-/

namespace LeanLTL
variable {σ σ' σ'' α α' β β' γ : Type*}

variable {𝕜 : Type*}

-- ## Num -> Num Operators
protected def TraceFun.neg [Neg 𝕜] (f : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map (- ·) f
protected def TraceFun.ceil (f : TraceFun σ ℚ) : TraceFun σ ℚ := TraceFun.map (⌈·⌉) f
protected def TraceFun.add [Add 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· + ·) f₁ f₂
protected def TraceFun.sub [Sub 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· - ·) f₁ f₂
protected def TraceFun.mul [Mul 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· * ·) f₁ f₂
protected def TraceFun.div [Div 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· / ·) f₁ f₂
protected def TraceFun.min [Min 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· ⊓ ·) f₁ f₂
protected def TraceFun.max [Max 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceFun σ 𝕜 := TraceFun.map₂ (· ⊔ ·) f₁ f₂

-- ## Num -> Prop Operators
protected def TraceFun.eq (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· = ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.lt [LT 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· < ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.gt [LT 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· > ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.le [LE 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· ≤ ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.ge [LE 𝕜] (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· ≥ ·) f₁ f₂ |>.toTraceSetTrue

variable {f g : TraceFun σ 𝕜} {t : Trace σ} {x y : 𝕜}

@[push_ltl] theorem TraceFun.neg_apply [Neg 𝕜] : (TraceFun.neg f) t = (f t).map (-·) := rfl
@[push_ltl] theorem TraceFun.ceil_apply {f : TraceFun σ ℚ} : (TraceFun.ceil f) t = (f t).map (fun x => (⌈x⌉ : ℚ)) := by
  simp [TraceFun.ceil, TraceFun.map]
@[push_ltl] theorem TraceFun.add_apply [Add 𝕜] : (TraceFun.add f g) t = (f t).bind fun x => (g t).bind fun y => some (x + y) := rfl
@[push_ltl] theorem TraceFun.sub_apply [Sub 𝕜] : (TraceFun.sub f g) t = (f t).bind fun x => (g t).bind fun y => some (x - y) := rfl
@[push_ltl] theorem TraceFun.mul_apply [Mul 𝕜] : (TraceFun.mul f g) t = (f t).bind fun x => (g t).bind fun y => some (x * y) := rfl
@[push_ltl] theorem TraceFun.div_apply [Div 𝕜] : (TraceFun.div f g) t = (f t).bind fun x => (g t).bind fun y => some (x / y) := rfl
@[push_ltl] theorem TraceFun.min_apply [Min 𝕜] : (TraceFun.min f g) t = (f t).bind fun x => (g t).bind fun y => some (x ⊓ y) := rfl
@[push_ltl] theorem TraceFun.max_apply [Max 𝕜] : (TraceFun.max f g) t = (f t).bind fun x => (g t).bind fun y => some (x ⊔ y) := rfl

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

@[push_ltl] theorem TraceFun.sat_lt_apply [LT 𝕜] :
    (t ⊨ TraceFun.lt f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x < y)) := by
  simp [TraceFun.lt, push_ltl]

@[push_ltl] theorem TraceFun.sat_gt_apply [LT 𝕜] :
    (t ⊨ TraceFun.gt f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x > y)) := by
  simp [TraceFun.gt, push_ltl]

@[push_ltl] theorem TraceFun.sat_leq_apply [LE 𝕜] :
    (t ⊨ TraceFun.le f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x ≤ y)) := by
  simp [TraceFun.le, push_ltl]

@[push_ltl] theorem TraceFun.sat_ge_apply [LE 𝕜] :
    (t ⊨ TraceFun.ge f g) ↔ (t ⊨ f.wget fun x => g.wget fun y => TraceSet.const (x ≥ y)) := by
  simp [TraceFun.ge, push_ltl]

end LeanLTL
