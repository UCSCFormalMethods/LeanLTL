import LeanLTL

namespace LTLfMT
variable {σ α: Type*}

-- Definitions taken from "Linear Temporal Logic Modulo Theories over Finite Traces" by Giatti et al.
def Var (σ) (α) := σ -> α
structure Trace (σ: Type*) where
  trace : LeanLTL.Trace σ
  finite : trace.Finite

attribute [simp] Trace.finite

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

inductive Lambda (σ) (α) where
  | alpha {an: ℕ} (pc : PredConst an) (args: Fin an → (SigmaTerm σ α))
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

def ofOptions {n : Nat} (f : Fin n → Option α) : Option (Fin n → α) :=
  if h : ∀ k, (f k).isSome then
    some <| fun k => (f k).get (h k)
  else
    none

def eval_sigma_term (t: Trace σ) (s: SigmaTerm σ α) (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) : Option α :=
  match s with
  | SigmaTerm.var v                 => some <| v (t.trace.toFun 0 (by simp))
  | SigmaTerm.qvar c                => some c
  | SigmaTerm.const c               => some c
  | SigmaTerm.apply (n:=n) fc args  => do
    let args' ← ofOptions (fun n' => eval_sigma_term t (args n') fs)
    return (fs n fc) args'
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

def sat_lambda (t: Trace σ) (l: Lambda σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)): Prop :=
  match l with
  | Lambda.alpha (an:=an) pc args =>
      let args_def              := ∀ n', (eval_sigma_term t (args n') fs).isSome;
      let contains_snext        := ∀ n', sigma_term_contains_snext (args n');
      let result (d: args_def)  := ((ps an pc) (fun n' => (eval_sigma_term t (args n') fs).get (by simp_all [args_def])));
        contains_snext → ∃ (ad: args_def), result ad
      ∧ ¬contains_snext → ∀ (ad: args_def), result ad
  | Lambda.not f        => ¬ (sat_lambda t f fs ps)
  | Lambda.or f₁ f₂     => (sat_lambda t f₁ fs ps) ∧ (sat_lambda t f₂ fs ps)
  | Lambda.and f₁ f₂    => (sat_lambda t f₁ fs ps) ∨ (sat_lambda t f₂ fs ps)
  | Lambda.exists p     => ∃ (x: α), sat_lambda t (p x) fs ps
  | Lambda.forall p     => ∀ (x: α), sat_lambda t (p x) fs ps

def sat_phi (t: Trace σ) (p: Phi σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)): Prop :=
  match p with
  | Phi.top           => True -- TODO: Not listed in paper?
  | Phi.lambda f      => sat_lambda t f fs ps
  | Phi.or f₁ f₂      => (sat_phi t f₁ fs ps) ∧ (sat_phi t f₂ fs ps)
  | Phi.and f₁ f₂     => (sat_phi t f₁ fs ps) ∨ (sat_phi t f₂ fs ps)
  | Phi.snext f       => ∃ (h_not_last: t.trace.length > 1),
                          let next_t : Trace σ := {
                            trace := t.trace.shift 1 h_not_last
                            finite := by simp
                          }
                          sat_phi next_t f fs ps
  | Phi.wnext f       => ∀ (h_not_last: t.trace.length > 1),
                          let next_t : Trace σ := {
                            trace := t.trace.shift 1 h_not_last
                            finite := by simp
                          }
                          sat_phi next_t f fs ps
  | Phi.until f₁ f₂ =>
    ∃ j ≥ 0, ∃ (h_j: (j: ℕ) < t.trace.length),
      let t_j : Trace σ := {
        trace := (t.trace.shift j h_j)
        finite := by simp
      }
      (∀ k < j, ∀ (h_k: (k: ℕ) < t.trace.length),
      let t_k : Trace σ := {
        trace := (t.trace.shift k h_k)
        finite := by simp
      }
      (sat_phi t_k f₁ fs ps))
      ∧ (sat_phi t_j f₂ fs ps)
  | Phi.release f₁ f₂ =>
    (∀ j, ∃ (h_j: (j: ℕ) < t.trace.length),
      let t_j : Trace σ := {
        trace := (t.trace.shift j h_j)
        finite := by simp
      }
      (sat_phi t_j f₂ fs ps))
    ∨ ∃ k ≥ 0, ∃ (h_k: (k: ℕ) < t.trace.length),
      let t_k : Trace σ := {
        trace := (t.trace.shift k h_k)
        finite := by simp
      }
      (∀ j ≤ k, ∀ (h_j: (j: ℕ) < t.trace.length),
      let t_j : Trace σ := {
        trace := (t.trace.shift j h_j)
        finite := by simp
      }
      (sat_phi t_j f₁ fs ps))

def toLeanLTL_SigmaTerm (s: SigmaTerm σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) : (LeanLTL.TraceFun σ α) :=
  match s with
  | SigmaTerm.var v                 => sorry
  | SigmaTerm.qvar c                => sorry
  | SigmaTerm.const c               => sorry
  | SigmaTerm.apply (n:=n) fc args  => sorry
  | SigmaTerm.snext s               => sorry
  | SigmaTerm.wnext s               => sorry

def toLeanLTL_Lambda (l: Lambda σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)) : (LeanLTL.TraceSet σ) :=
  match l with
  | Lambda.alpha (an:=an) pc args   => sorry
  | Lambda.not f                    => sorry
  | Lambda.or f₁ f₂                 => sorry
  | Lambda.and f₁ f₂                => sorry
  | Lambda.exists p                 => sorry
  | Lambda.forall p                 => sorry

def toLeanLTL_Phi (p: Phi σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)) : (LeanLTL.TraceSet σ) :=
  match p with
  | Phi.top           => sorry
  | Phi.lambda f      => sorry
  | Phi.or f₁ f₂      => sorry
  | Phi.and f₁ f₂     => sorry
  | Phi.snext f       => sorry
  | Phi.wnext f       => sorry
  | Phi.until f₁ f₂   => sorry
  | Phi.release f₁ f₂ => sorry

theorem equisat (t: LTLfMT.Trace σ) (p: Phi σ α)
  (fs: (n: ℕ) → FuncConst n → (FuncVal n α)) (ps: (n: ℕ) → PredConst n → (PredVal n α)) :
  (LTLfMT.sat_phi t p fs ps) ↔ (t.trace ⊨ (toLeanLTL_Phi p fs ps)) := by
  sorry
