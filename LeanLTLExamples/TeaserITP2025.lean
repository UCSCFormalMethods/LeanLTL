import LeanLTL

namespace LeanLTL.Examples

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

example : ⊨ LLTL[((← n) = 5 ∧ 𝐆 ((𝐗 (← n)) = (← n) ^ 2)) → 𝐆 (5 ≤ (← n))] := by
  rintro t ⟨h1, h2⟩
  have := t.inhabited
  apply TraceSet.globally_induction <;> simp_all [push_ltl]
  intros; nlinarith
