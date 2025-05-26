import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

axiom σ : Type*
axiom b₁ : σ → Prop
axiom b₂ : σ → Prop

example : ⊨ LLTL[(b₁ ∧ (𝐆 (b₁ → (𝐗ʷ b₁)))) → 𝐆 b₁] := by
  sorry

example : ⊨ LLTL[((𝐆 (b₁ ∨ b₂)) ∧ (𝐅 ¬b₁)) → (𝐅 b₂)] := by
  sorry

example : ⊨ᶠ (LLTL[𝐅 (𝐗ʷ ⊥)] : TraceSet σ) := by
  sorry

example : ⊨ⁱ (LLTL[𝐆 (𝐗ˢ ⊤)] : TraceSet σ) := by
  sorry
