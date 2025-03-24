import LeanLTL.TraceSet.Basic
import LeanLTL.TraceFun.Basic

/-!
# Converting trace sets to and from trace functions
-/

namespace LeanLTL

variable {σ σ' σ'' α α' β β': Type*}
variable {t : Trace σ} {f f₁ f₂ f₃ : TraceSet σ}

protected def TraceSet.toFun (s : TraceSet σ) : TraceFun σ Prop where
  eval t := some (t ⊨ s)

/--
Converts a `Prop`-valued `TraceFun` to a `TraceSet`
by using `c` as its value wherever it is undefined. -/
protected def TraceFun.toTraceSet (f : TraceFun σ Prop) (c : Prop) : TraceSet σ where
  sat t := (f t).getD c

/--
Converts a `Prop`-valued `TraceFun` to a `TraceSet`, with undefined being `False`.
-/
protected abbrev TraceFun.toTraceSetFalse (f : TraceFun σ Prop) : TraceSet σ := f.toTraceSet False

/--
Converts a `Prop`-valued `TraceFun` to a `TraceSet`, with undefined being `True`.
-/
protected abbrev TraceFun.toTraceSetTrue (f : TraceFun σ Prop) : TraceSet σ := f.toTraceSet True

namespace TraceSet

@[simp] lemma toFun_defined (s : TraceSet σ) (t : Trace σ) : (s.toFun t).isSome := rfl

@[simp] lemma toTraceSet_toFun (f : TraceSet σ) (c : Prop) : f.toFun.toTraceSet c = f := rfl

lemma map_toFun (f : TraceSet σ) (g : Prop → Prop) : f.toFun.map g = (f.map g).toFun := rfl

lemma map₂_toFun (f f' : TraceSet σ) (g : Prop → Prop → Prop) :
    TraceFun.map₂ g f.toFun f'.toFun = (TraceSet.map₂ g f f').toFun := rfl

end TraceSet

end LeanLTL
