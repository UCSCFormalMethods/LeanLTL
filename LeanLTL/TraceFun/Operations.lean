import LeanLTL.TraceFun.Defs
import LeanLTL.TraceSet.Defs
import Mathlib

/-!
# Basic arithmetic operations for trace functions
-/

namespace LeanLTL
variable {σ σ' σ'' α α' β β': Type*}

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
protected def TraceFun.leq (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· ≤ ·) f₁ f₂ |>.toTraceSetTrue
protected def TraceFun.geq (f₁ f₂ : TraceFun σ 𝕜) : TraceSet σ := TraceFun.map₂ (· ≥ ·) f₁ f₂ |>.toTraceSetTrue

end LeanLTL
