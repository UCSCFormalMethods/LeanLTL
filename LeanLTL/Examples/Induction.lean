import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

example {σ : Type} (n : σ → ℕ) :
    ⊨ⁱ LLTL[G ((←ˢ n) < (←ˢ X n)) → ∀ m, F (m < (←ˢ n))] := by
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
    ⊨ LLTL[G ((← n) < (← X n)) → ∀ m, F (m < (←ʷ n))] := by
  simp +contextual [push_ltl]
  intro t ht n
  induction n with
  | zero =>
    use 1
    simp
    obtain ⟨m, ht⟩ := ht 0 (by simp)
    simp at ht
    simp [TraceFun.shift] at ht
    obtain ⟨⟨h, rfl⟩, h'⟩ := ht
    exists h
    omega
  | succ x ih =>
    obtain ⟨m, hm, ih⟩ := ih
    obtain ⟨k, ht, ht'⟩ := ht m hm
    simp [TraceFun.shift] at ht
    obtain ⟨hm', rfl⟩ := ht
    use 1 + m
    constructor
    · omega
    · have : m < t.length := by
        generalize_proofs at ih
        assumption
      clear ht'
      revert hm'
      cases t.length <;> simp
      norm_cast
      omega
