import LeanLTL.TraceSet.Defs
import LeanLTL.Util.SimpAttrs
import Mathlib

/-!
# Basic theory about traces
-/

namespace LeanLTL

namespace TraceSet
variable {σ σ' σ'' α α' β β': Type*}
variable {t : Trace σ} {f f₁ f₂ : TraceSet σ}

@[ext]
protected def ext {f g : TraceSet σ} (h : ∀ t, (t ⊨ f) ↔ (t ⊨ g)) : f = g := by
  cases f
  cases g
  rw [mk.injEq]
  funext t
  apply propext
  apply h

/-!
### Semantics lemmas (lemmas about `⊨`)
-/

@[push_fltl] lemma sat_true_iff : (t ⊨ TraceSet.true) ↔ True := by rfl
@[push_fltl] lemma sat_false_iff : (t ⊨ TraceSet.false) ↔ False := by rfl

@[push_fltl] lemma sat_not_iff : (t ⊨ f.not) ↔ ¬(t ⊨ f) := Iff.rfl
@[push_fltl] lemma sat_and_iff : (t ⊨ f₁.and f₂) ↔ (t ⊨ f₁) ∧ (t ⊨ f₂) := Iff.rfl
@[push_fltl] lemma sat_or_iff : (t ⊨ f₁.or f₂) ↔ (t ⊨ f₁) ∨ (t ⊨ f₂) := Iff.rfl
@[push_fltl] lemma sat_imp_iff : (t ⊨ f₁.imp f₂) ↔ ((t ⊨ f₁) → (t ⊨ f₂)) := Iff.rfl

@[push_fltl] lemma sat_wshift_iff (c : ℕ) :
    (t ⊨ f.wshift c) ↔ ∀ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_fltl] lemma sat_sshift_iff (c : ℕ) :
    (t ⊨ f.sshift c) ↔ ∃ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

-- TODO: Unshift simplification for wnext and snext
-- E.g., (t.unshift s) ⊨ (f.wnext) ↔ t⊨f
-- TODO: Dual lemmas for unshift everywhere shift is
@[push_fltl] lemma sat_until_iff :
    (t ⊨ f₁.until f₂) ↔ ∃ n, (∀ i < n, t ⊨ f₁.wshift i) ∧ (t ⊨ f₂.sshift n) := Iff.rfl

@[push_fltl] theorem sat_finally_iff : (t ⊨ f.finally) ↔ ∃ n, t ⊨ f.sshift n := by
  simp [TraceSet.finally, push_fltl]

@[push_fltl] theorem sat_globally_iff : (t ⊨ f.globally) ↔ ∀ n, t ⊨ (f.wshift n) := by
  simp [TraceSet.globally, push_fltl]

@[push_fltl] theorem sem_imp_iff : (f₁ ⇒ f₂) ↔ ∀ (t : Trace σ), t ⊨ f₁.imp f₂ := by
  simp [TraceSet.sem_imp, push_fltl]

/-!
### Negation pushing
-/

@[simp] lemma not_not : f.not.not = f := by ext t; simp [push_fltl]

lemma not_wshift_eq (n : ℕ) : (f.sshift n).not = f.not.wshift n := by ext t; simp [push_fltl]

lemma not_sshift_eq (n : ℕ) : (f.wshift n).not = f.not.sshift n := by ext t; simp [push_fltl]

lemma not_globally_eq : f.finally.not = f.not.globally := by ext t; simp [push_fltl]

lemma not_finally_eq : f.globally.not = f.not.finally := by ext t; simp [push_fltl]


/-!
### Theorems about `TraceSet.toFun`
-/

@[simp] lemma toFun_defined (s : TraceSet σ) (t : Trace σ) : (s.toFun t).isSome := rfl

@[simp] lemma toTraceSet_toFun (f : TraceSet σ) (c : Prop) : f.toFun.toTraceSet c = f := rfl

-- TODO should `toFun` be pushed inward or pushed outward?
lemma map_toFun (f : TraceSet σ) (g : Prop → Prop) : f.toFun.map g = (f.map g).toFun := rfl

lemma map₂_toFun (f f' : TraceSet σ) (g : Prop → Prop → Prop) :
    TraceFun.map₂ g f.toFun f'.toFun = (TraceSet.map₂ g f f').toFun := rfl

-- lemma toTraceSet_shift_toFun (f : TraceSet σ) (i : ℕ) :
--     (f.toFun.shift i).toTraceSetTrue = f.wshift i := by
--   ext
--   simp
