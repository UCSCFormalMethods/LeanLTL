import LeanLTL

namespace LTL

-- Definitions taken from "Handbook of model checking", Section 2.3.1 (without past-time operators)
-- Note: Past-time operators add no expressive power to the logic (see source)
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
    simp [sat, toLeanLTL, push_ltl, LeanLTL.TraceSet.of]
  . rename_i f ih
    simp_all [sat, toLeanLTL, push_ltl]
  . rename_i f₁ f₂ ih₁ ih₂
    simp_all [sat, toLeanLTL, push_ltl]
  . rename_i f ih
    simp only [sat, toLeanLTL, push_ltl]

    have h_tl : 1 < t.trace.length := LeanLTL.Trace.infinite_lt_length t.trace t.infinite 1
    specialize ih {
      trace := t.trace.shift 1 h_tl
      infinite := by simp_all
    }
    simp_rw [ih, LeanLTL.TraceSet.sshift_eq_sshift, LeanLTL.TraceSet.shift_sat_iff_sat_sshift]
  . rename_i f₁ f₂ ih₁ ih₂
    simp_all [sat, toLeanLTL, push_ltl]

/-!
# Defining other logical connectives
-/
section Connectives

open LeanLTL
variable {σ : Type*}

def Formula.true : Formula σ := Formula.var (fun _ => True)
def Formula.false : Formula σ := Formula.var (fun _ => False)
def Formula.and (f₁ f₂ : Formula σ) : Formula σ := (f₁.not.or f₂.not).not
def Formula.imp (f₁ f₂ : Formula σ) : Formula σ := f₁.not.or f₂
def Formula.eventually (f₁ : Formula σ) : Formula σ := Formula.true.until f₁
def Formula.globally (f₁ : Formula σ) : Formula σ := f₁.not.eventually.not
def Formula.weak_until (f₁ f₂ : Formula σ) : Formula σ := Formula.or (f₁.until f₂) f₁.globally

variable {f₁ f₂ : Formula σ}

theorem toLeanLTL_true : toLeanLTL (Formula.true : Formula σ) = TraceSet.true := rfl
theorem toLeanLTL_false : toLeanLTL (Formula.false : Formula σ) = TraceSet.false := rfl
theorem toLeanLTL_var {v : Var σ} : toLeanLTL (Formula.var v) = TraceSet.of v := rfl
theorem toLeanLTL_not : toLeanLTL f₁.not = (toLeanLTL f₁).not := rfl
theorem toLeanLTL_or : toLeanLTL (f₁.or f₂) = (toLeanLTL f₁).or (toLeanLTL f₂) := rfl
theorem toLeanLTL_and : toLeanLTL (f₁.and f₂) = (toLeanLTL f₁).and (toLeanLTL f₂) := by
  ext; simp [push_ltl, toLeanLTL, Formula.and]
theorem toLeanLTL_imp : toLeanLTL (f₁.imp f₂) = (toLeanLTL f₁).imp (toLeanLTL f₂) := by
  simp only [Formula.imp, toLeanLTL_or, toLeanLTL_not]
  ext; simp [push_ltl]; tauto
theorem toLeanLTL_next : toLeanLTL (Formula.next f₁) = (toLeanLTL f₁).snext := rfl
theorem toLeanLTL_until : toLeanLTL (f₁.until f₂) = (toLeanLTL f₁).until (toLeanLTL f₂) := rfl
theorem toLeanLTL_eventually : toLeanLTL f₁.eventually = (toLeanLTL f₁).finally := rfl
theorem toLeanLTL_globally : toLeanLTL f₁.globally = (toLeanLTL f₁).globally := rfl
theorem toLeanLTL_weak_until :
    toLeanLTL (f₁.weak_until f₂) = ((toLeanLTL f₁).until (toLeanLTL f₂)).or (toLeanLTL f₁).globally := by
  simp [Formula.weak_until, toLeanLTL_or, toLeanLTL_until, toLeanLTL_globally]

end Connectives
