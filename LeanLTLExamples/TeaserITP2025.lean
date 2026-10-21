import LeanLTL

namespace LeanLTL.Examples

open LeanLTL
open scoped LeanLTL.Notation

noncomputable section
namespace Teaser
axiom σ : Type*
axiom n : σ → ℤ

example : ⊨ⁱ LLTL[((←ˢ n) = 5 ∧ 𝐆 ((𝐗 (←ˢ n)) = (←ˢ n) ^ 2)) → 𝐆 (5 ≤ (←ˢ n))] := by
  rw [TraceSet.sem_entail_inf_iff]
  rintro t hinf ⟨h1, h2⟩
  apply TraceSet.globally_induction <;> simp_all [push_ltl]
  intros; nlinarith

example : ⊨ LLTL[((←ˢ n) = 5 ∧ 𝐆 ((𝐗 (←ˢ n)) = (←ˢ n) ^ 2)) → 𝐆 (5 ≤ (←ˢ n))] := by
  rintro t ⟨h1, h2⟩
  have := t.inhabited
  apply TraceSet.globally_induction <;> simp_all [push_ltl]
  intros; nlinarith
