import LeanLTL

namespace LTLf


-- Definitions taken from "Linear temporal logic and linear dynamic logic on finite traces" by De Giacamo et al.
def Var (σ: Type*) := σ -> Prop
structure Trace (σ: Type*) where
  trace : LeanLTL.Trace σ
  finite : trace.Finite

attribute [simp] Trace.finite

inductive Formula (σ: Type*) where
  | var (v: (Var σ))
  | not (f: Formula σ)
  | and (f₁ f₂: Formula σ)
  | next (f: Formula σ)
  | until (f₁ f₂: Formula σ)

def sat {σ: Type*} (t: Trace σ) (f: Formula σ) : Prop :=
  match f with
  | Formula.var v        => v (t.trace.toFun 0 (by simp))
  | Formula.not f        => ¬ (sat t f)
  | Formula.and f₁ f₂     => (sat t f₁) ∧ (sat t f₂)
  | Formula.next f       =>
    ∃ (h_not_last: 1 < t.trace.length),
    let next_t := {
      trace := t.trace.shift 1 h_not_last
      finite := by simp
    }
    (sat next_t f)
  | Formula.until f₁ f₂  =>
    ∃ i ≥ 0, ∃ (h_i: (i: ℕ) < t.trace.length),
    let t_i := {
      trace := (t.trace.shift i h_i)
      finite := by simp
    }
    (∀ j < i, ∀ (h_j: (j: ℕ) < t.trace.length),
    let t_j := {
      trace := (t.trace.shift j h_j)
      finite := by simp
    }
    (sat t_j f₁))
    ∧ (sat t_i f₂)

def toLeanLTL {σ: Type*} (f: Formula σ) : (LeanLTL.TraceSet σ) :=
  match f with
  | Formula.var v        => LeanLTL.TraceSet.of v
  | Formula.not f        => LeanLTL.TraceSet.not (toLeanLTL f)
  | Formula.and f₁ f₂     => LeanLTL.TraceSet.and (toLeanLTL f₁) (toLeanLTL f₂)
  | Formula.next f       => LeanLTL.TraceSet.snext (toLeanLTL f)
  | Formula.until f₁ f₂  => LeanLTL.TraceSet.until (toLeanLTL f₁) (toLeanLTL f₂)

theorem equisat {σ: Type*} (f: Formula σ) (t: LTLf.Trace σ) :
  (LTLf.sat t f) ↔ (t.trace ⊨ (toLeanLTL f)) := by
  induction f generalizing t
  . rename_i v
    simp [sat, toLeanLTL, push_fltl, LeanLTL.TraceSet.of]
  . rename_i f ih
    simp_all [sat, toLeanLTL, push_fltl]
  . rename_i f₁ f₂ ih₁ ih₂
    simp_all [sat, toLeanLTL, push_fltl]
  . rename_i f ih
    simp only [sat, toLeanLTL, push_fltl]
    congr!
    rename_i h_tl
    specialize ih {
      trace := t.trace.shift 1 h_tl
      finite := by simp_all
    }
    simp_all
  . rename_i f₁ f₂ ih₁ ih₂
    simp_all [sat, toLeanLTL, push_fltl]
