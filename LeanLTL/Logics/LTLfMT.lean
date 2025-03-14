import LeanLTL

namespace LTLf
variable {σ α: Type*}

-- Definitions taken from "Linear Temporal Logic Modulo Theories over Finite Traces" by Giatti et al.
def Var (σ) (α) := σ -> α
structure Trace (σ: Type*) where
  trace : LeanLTL.Trace σ
  finite : trace.Finite

attribute [simp] Trace.finite

-- TODO: Function and pred type
-- TODO: Add value type restriction

def FuncConst (_: ℕ) := Type*
def FuncVal (n: ℕ) (α) := (args: Fin n → α) → α

def PredConst (_: ℕ) := Type*
def PredVal (n: ℕ) (α) := (args: Fin n → α) → Prop

inductive SigmaTerm (σ) (α) where
  | var (v: Var σ α)
  | qvar (c: α)
  | const (c: α)
  | apply {n: ℕ} (fc: FuncConst n) (args: Fin n → (SigmaTerm σ α))
  | snext (s: SigmaTerm σ α)
  | wnext (s: SigmaTerm σ α)

def sigma_term_contains_snext (s: SigmaTerm σ α) : Prop :=
  match s with
  | SigmaTerm.var _                 => False
  | SigmaTerm.qvar _                => False
  | SigmaTerm.const _               => False
  | SigmaTerm.apply (n:=n) _ args   => ∀ n' : Fin n, sigma_term_contains_snext (args n')
  | SigmaTerm.snext _               => True
  | SigmaTerm.wnext _               => False

structure Alpha (n: ℕ) (σ) (α) where
  pc : PredConst n
  args: Fin n → (SigmaTerm σ α)

inductive Lambda (σ) (α) where
  | pred {n: ℕ} (p: Alpha n σ α)
  | not (f: Lambda σ α)
  | or (f₁ f₂: Lambda σ α)
  | and (f₁ f₂: Lambda σ α)
  | exists (p: α -> Lambda σ α)
  | forall (p: α -> Lambda σ α)

inductive Phi (σ) (α) where
  | top
  | lambda (f: Lambda σ α)
  | or (f₁ f₂: Phi σ α)
  | and (f₁ f₂: Phi σ α)
  | wnext (f: Phi σ α)
  | snext (f: Phi σ α)
  | until (f₁ f₂: Phi σ α)
  | release (f₁ f₂: Phi σ α)

def eval_sigma_term (t: Trace σ) (s: SigmaTerm σ α) (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) : Option α :=
  match s with
  | SigmaTerm.var v                 => some <| v (t.trace.toFun 0 (by simp))
  | SigmaTerm.qvar c                => some c
  | SigmaTerm.const c               => some c
  | SigmaTerm.apply (n:=n) fc args  => ((fs n fc) (fun n' => eval_sigma_term t (args n') fs)) -- TODO: Option to alpha conversion?
  | SigmaTerm.snext s               => if h_not_last: t.trace.length > 1
                                       then
                                        let next_t : Trace σ := {
                                          trace := t.trace.shift 1 h_not_last
                                          finite := by simp
                                        }
                                        eval_sigma_term next_t s fs
                                       else
                                        none
  | SigmaTerm.wnext s               => if h_not_last: t.trace.length > 1
                                       then
                                        let next_t : Trace σ := {
                                          trace := t.trace.shift 1 h_not_last
                                          finite := by simp
                                        }
                                        eval_sigma_term next_t s fs
                                       else
                                        none

-- set_option autoImplicit true

def sat_alpha {an} (t: Trace σ) (a: Alpha an σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)): Prop :=
  let args_def              := ∀ n' : Fin an, ((a.args n') t).isSome;
  let contains_snext        := ∀ n' : Fin an, sigma_term_contains_snext (a.args n');
  let result (d: args_def)  := ((ps an a.pc) (fun n' => eval_sigma_term t (args n') fs)); -- TODO: Option to alpha conversion?
     contains_snext → ∃ (ad: args_def), result ad
  ∧ ¬contains_snext → ∀ (ad: args_def), result ad

def sat_lambda (t: Trace σ) (l: Lambda σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)): Prop :=
  match l with
  | Lambda.pred a       => sat_alpha t a fs ps
  | Lambda.not f        => ¬ (sat_lambda t f fs ps)
  | Lambda.or f₁ f₂     => (sat_lambda t f₁ fs ps) ∧ (sat_lambda t f₂ fs ps)
  | Lambda.and f₁ f₂    => (sat_lambda t f₁ fs ps) ∨ (sat_lambda t f₂ fs ps)
  | Lambda.exists p     => ∃ (x: α), sat_lambda t (p x) fs ps
  | Lambda.forall p     => ∀ (x: α), sat_lambda t (p x) fs ps

def sat_phi (t: Trace σ) (p: Phi σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)): Prop :=
  match p with
  | Phi.top         => True -- TODO: Not listed in paper?
  | Phi.lambda f    => sat_lambda t f fs ps
  | Phi.or f₁ f₂    => (sat_phi t f₁ fs ps) ∧ (sat_phi t f₂ fs ps)
  | Phi.and f₁ f₂   => (sat_phi t f₁ fs ps) ∨ (sat_phi t f₂ fs ps)
  | Phi.snext f     => ∃ (h_not_last: t.trace.length > 1),
                        let next_t : Trace σ := {
                          trace := t.trace.shift 1 h_not_last
                          finite := by simp
                        }
                        sat_phi next_t p fs ps
  | Phi.wnext f     => ∀ (h_not_last: t.trace.length > 1),
                        let next_t : Trace σ := {
                          trace := t.trace.shift 1 h_not_last
                          finite := by simp
                        }
                        sat_phi next_t p fs ps


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
