import LeanLTL

open LeanLTL
open scoped LeanLTL.Notation

example {σ : Type} (p : σ → ℕ) :
    let n := TraceFun.of p
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
