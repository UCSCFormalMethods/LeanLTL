import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

noncomputable section
namespace Teaser
axiom σ : Type*
axiom p : σ → ℤ
abbrev n : TraceFun σ ℤ := TraceFun.of p

example : ⊨ⁱ LLTL[((← n) = 5 ∧ G ((X (← n)) = (← n) ^ 2)) → G (5 ≤ (← n))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl, hinf]
  intros; nlinarith
