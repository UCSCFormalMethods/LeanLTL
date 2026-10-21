import LeanLTL

namespace LeanLTL.Examples

open LeanLTL
open scoped LeanLTL.Notation

example {σ : Type} (n : σ → ℕ) :
    ⊨ⁱ LLTL[𝐆 ((←ˢ n) < (←ˢ 𝐗 n)) → ∀ m, 𝐅 (m < (←ˢ n))] := by
  simp +contextual [push_ltl]
  intros t ht hn x
  induction x with
  | zero =>
    use 1
    specialize hn 0
    simp at hn
    omega
  | succ x ih =>
    obtain ⟨m, ih⟩ := ih
    specialize hn m
    use 1 + m
    omega

example {σ : Type} (n : σ → ℕ) :
    ⊨ LLTL[𝐆 ((←ˢ n) < (←ˢ 𝐗 n)) → ∀ m, 𝐅 (m < (←ʷ n))] := by
  simp +contextual [push_ltl]
  intro t ht n
  induction n with
  | zero =>
    use 1
    simp
    obtain ⟨h, hn⟩ := ht 0 (by simp)
    simp at h hn
    exists h
    omega
  | succ x ih =>
    obtain ⟨m, hm, ih⟩ := ih
    obtain ⟨hm', ht⟩ := ht m hm
    use 1 + m
    constructor
    · omega
    · have : m < t.length := by
        generalize_proofs at ih
        assumption
      clear ht
      revert hm'
      cases t.length <;> simp
      norm_cast
      omega
