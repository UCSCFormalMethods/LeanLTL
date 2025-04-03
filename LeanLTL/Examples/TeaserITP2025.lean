import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

noncomputable section
namespace Teaser
axiom σ : Type*
axiom n : σ → ℤ

example : ⊨ⁱ LLTL[((← n) = 5 ∧ 𝐆 ((𝐗 (← n)) = (← n) ^ 2)) → 𝐆 (5 ≤ (← n))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl, hinf]
  intros; nlinarith
