import LeanLTL

namespace LTL

-- TODO: Using wikipedia definitions here. Need to find a paper to cite.
def Var (σ: Type*) := σ -> Prop
structure Trace (σ: Type*) where
  trace : LeanLTL.Trace σ
  infinite : trace.Infinite

attribute [simp] Trace.infinite

inductive Formula (σ: Type*) where
  | var (v: (Var σ))
  | not (f: Formula σ)
  | or (f₁ f₂: Formula σ)
  | next (f: Formula σ)
  | until (f₁ f₂: Formula σ)

def sat {σ: Type*} (t: Trace σ) (f: Formula σ) : Prop :=
  match f with
  | Formula.var v        => v (t.trace.toFun 0 (by simp))
  | Formula.not f        => ¬ (sat t f)
  | Formula.or f₁ f₂     => (sat t f₁) ∨ (sat t f₂)
  | Formula.next f       =>
    let next_t := {
      trace := (t.trace.shift 1 (by
        -- @ Kyle, can we reduce this to just simp?
        have := LeanLTL.Trace.infinite_lt_length t.trace t.infinite 1
        simp_all
      ))
      infinite := by simp
    }
    (sat next_t f)
  | Formula.until f₁ f₂  =>
    ∃ i ≥ 0,
    let t_i := {
      trace := (t.trace.shift i (by simp))
      infinite := by simp
    }
    (∀ j < i,
    let t_j := {
      trace := (t.trace.shift j (by simp))
      infinite := by simp
    }
    (sat t_j f₁))
    ∧ (sat t_i f₂)

def toLeanLTL {σ: Type*} (f: Formula σ) : (LeanLTL.TraceSet σ) :=
  match f with
  | Formula.var v        => LeanLTL.TraceSet.of v
  | Formula.not f        => LeanLTL.TraceSet.not (toLeanLTL f)
  | Formula.or f₁ f₂     => LeanLTL.TraceSet.or (toLeanLTL f₁) (toLeanLTL f₂)
  | Formula.next f       => LeanLTL.TraceSet.snext (toLeanLTL f)
  | Formula.until f₁ f₂  => LeanLTL.TraceSet.until (toLeanLTL f₁) (toLeanLTL f₂)

theorem equisat {σ: Type*} (f: Formula σ) (t: LTL.Trace σ) :
  (LTL.sat t f) ↔ (t.trace ⊨ (toLeanLTL f)) := by
  induction f generalizing t
  . rename_i v
    simp [sat, toLeanLTL, push_fltl, LeanLTL.TraceSet.of]
  . rename_i f ih
    simp_all [sat, toLeanLTL, push_fltl]
  . rename_i f₁ f₂ ih₁ ih₂
    simp_all [sat, toLeanLTL, push_fltl]
  . rename_i f ih
    simp only [sat, toLeanLTL, push_fltl]

    have h_tl : 1 < t.trace.length := LeanLTL.Trace.infinite_lt_length t.trace t.infinite 1
    specialize ih {
      trace := t.trace.shift 1 h_tl
      infinite := by simp_all
    }
    simp_all
  . rename_i f₁ f₂ ih₁ ih₂
    simp_all [sat, toLeanLTL, push_fltl]
