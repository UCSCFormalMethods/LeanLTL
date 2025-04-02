import LeanLTL.Trace.Basic
import LeanLTL.TraceSet.Defs
import LeanLTL.Util.SimpAttrs
import Mathlib

/-!
# Basic theory about traces
-/

namespace LeanLTL

namespace TraceSet
variable {σ σ' σ'' α α' β β': Type*}
variable {t : Trace σ} {f f₁ f₂ f₃ : TraceSet σ}

@[ext]
protected def ext {f g : TraceSet σ} (h : ∀ t, (t ⊨ f) ↔ (t ⊨ g)) : f = g := by
  cases f
  cases g
  rw [mk.injEq]
  funext t
  apply propext
  apply h

/-!
### Boolean algebra instance
-/

instance : PartialOrder (TraceSet σ) where
  le := TraceSet.sem_imp
  le_refl _ _ h := h
  le_trans _ _ _ h1 h2 t ht := h2 t (h1 t ht)
  le_antisymm _ _ h1 h2 := TraceSet.ext fun t => ⟨h1 t, h2 t⟩

instance : Lattice (TraceSet σ) where
  sup := TraceSet.or
  inf := TraceSet.and
  le_sup_left _ _ _ := Or.inl
  le_sup_right _ _ _ := Or.inr
  sup_le _ _ _ h1 h2 t h := Or.elim h (h1 t) (h2 t)
  inf_le_left _ _ _ := And.left
  inf_le_right _ _ _ := And.right
  le_inf _ _ _ h1 h2 t h := And.intro (h1 t h) (h2 t h)

instance : CompleteLattice (TraceSet σ) where
  sSup := TraceSet.some
  sInf := TraceSet.all
  top := TraceSet.true
  bot := TraceSet.false
  le_sSup s p hp t ht := ⟨p, hp, ht⟩
  sSup_le s p hp t ht := by obtain ⟨q, hq, ht⟩ := ht; exact hp q hq t ht
  sInf_le s p hp t ht := ht p hp
  le_sInf s p hp t ht q hq := hp q hq t ht
  le_top _ _ _ := trivial
  bot_le _ _ h := False.elim h

instance : GeneralizedHeytingAlgebra (TraceSet σ) where
  himp := TraceSet.imp
  le_himp_iff _ _ _ := by
    constructor
    · intro h t ht
      exact h t ht.1 ht.2
    · intro h t ht1 ht2
      exact h t ⟨ht1, ht2⟩

instance : HeytingAlgebra (TraceSet σ) where
  compl := TraceSet.not
  himp_bot _ := rfl

instance : BooleanAlgebra (TraceSet σ) where
  inf_compl_le_bot _ _ := and_not_self
  top_le_sup_compl _ _ _ := Classical.em _
  le_top _ _ _ := trivial
  bot_le _ _ h := False.elim h
  himp_eq _ _ := TraceSet.ext fun _ => imp_iff_or_not

/-!
### Definition lemmas
-/

lemma release_eq : f₁.release f₂ = ((f₁ᶜ).until f₂ᶜ)ᶜ := rfl

lemma finally_eq : f.finally = TraceSet.until ⊤ f := rfl

lemma globally_eq : f.globally = (TraceSet.finally fᶜ)ᶜ := rfl

/-!
### Semantics lemmas (lemmas about `⊨`)
-/

open scoped symmDiff

@[push_ltl] lemma sat_const_iff (p : Prop) : (t ⊨ TraceSet.const p) ↔ p := Iff.rfl
@[push_ltl] lemma sat_true_iff : (t ⊨ ⊤) ↔ True := Iff.rfl
@[push_ltl] lemma sat_false_iff : (t ⊨ ⊥) ↔ False := Iff.rfl

@[push_ltl] lemma sat_not_iff : (t ⊨ fᶜ) ↔ ¬(t ⊨ f) := Iff.rfl
@[push_ltl] lemma sat_and_iff : (t ⊨ f₁ ⊓ f₂) ↔ (t ⊨ f₁) ∧ (t ⊨ f₂) := Iff.rfl
@[push_ltl] lemma sat_or_iff : (t ⊨ f₁ ⊔ f₂) ↔ (t ⊨ f₁) ∨ (t ⊨ f₂) := Iff.rfl
@[push_ltl] lemma sat_imp_iff : (t ⊨ f₁ ⇨ f₂) ↔ ((t ⊨ f₁) → (t ⊨ f₂)) := Iff.rfl
@[push_ltl] lemma sat_iff_iff : (t ⊨ f₁ ⇔ f₂) ↔ ((t ⊨ f₁) ↔ (t ⊨ f₂)) := and_comm.trans iff_iff_implies_and_implies.symm

@[push_ltl] theorem sat_forall_iff (p : α → TraceSet σ) :
    (t ⊨ (TraceSet.forall p)) ↔ (∀ x, t ⊨ p x) := Iff.rfl
@[push_ltl] theorem sat_exists_iff (p : α → TraceSet σ) :
    (t ⊨ (TraceSet.exists p)) ↔ (∃ x, t ⊨ p x) := Iff.rfl

@[push_ltl] theorem sat_iInf_iff (p : α → TraceSet σ) :
    (t ⊨ ⨅ x, p x) ↔ (∀ x, t ⊨ p x) := by
  constructor
  · intro h _
    apply h
    apply Set.mem_range_self
  · intro h q
    rw [Set.mem_range]
    rintro ⟨_, rfl⟩
    apply h
@[push_ltl] theorem sat_iSup_iff (p : α → TraceSet σ) :
    (t ⊨ ⨆ x, p x) ↔ (∃ x, t ⊨ p x) := by
  constructor
  · rintro ⟨_, ⟨_, rfl⟩, h⟩
    exact ⟨_, h⟩
  · rintro ⟨x, h⟩
    use! p x, x


@[push_ltl] lemma sat_wshift_iff (c : ℕ) :
    (t ⊨ f.wshift c) ↔ ∀ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_ltl] lemma sat_sshift_iff (c : ℕ) :
    (t ⊨ f.sshift c) ↔ ∃ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_ltl] lemma sat_until_iff :
    (t ⊨ f₁.until f₂) ↔ ∃ n, (∀ i < n, t ⊨ f₁.wshift i) ∧ (t ⊨ f₂.sshift n) := Iff.rfl

@[push_ltl] lemma sat_release_iff :
    (t ⊨ f₁.release f₂) ↔ ∀ (n : ℕ), (∀ i < n, ¬ t ⊨ f₁.sshift i) → (t ⊨ f₂.wshift n) := by
  simp only [release_eq, push_ltl]
  simp

/-- Alternative formulation of `sat_release_iff`, without negations. -/
lemma sat_release_iff' :
    (t ⊨ f₁.release f₂) ↔ ∀ (n : ℕ), (∃ i < n, t ⊨ f₁.sshift i) ∨ (t ⊨ f₂.wshift n) := by
  simp only [sat_release_iff, imp_iff_not_or]
  push_neg
  rfl

@[push_ltl] theorem sat_finally_iff : (t ⊨ f.finally) ↔ ∃ n, t ⊨ f.sshift n := by
  simp [finally_eq, push_ltl]

@[push_ltl] theorem sat_globally_iff : (t ⊨ f.globally) ↔ ∀ n, t ⊨ f.wshift n := by
  simp [globally_eq, push_ltl]

@[push_ltl] theorem sat_sget_iff (f : TraceFun σ α) (p : α → TraceSet σ) : (t ⊨ f.sget p) ↔ ∃ x, f t = some x ∧ (t ⊨ p x) := by
  simp only [TraceFun.sget, TraceFun.get]
  split <;> simp [*]

@[push_ltl] theorem sat_wget_iff (f : TraceFun σ α) (p : α → TraceSet σ) : (t ⊨ f.wget p) ↔ ∀ x, f t = some x → (t ⊨ p x) := by
  simp only [TraceFun.wget, TraceFun.get]
  split <;> simp [*]

theorem sem_entail_iff_top_le : (⊨ f) ↔ (⊤ ≤ f) := by
  constructor
  · intro h t _
    exact h t
  · intro h t
    exact h t trivial

@[push_ltl] theorem sem_entail_iff : (⊨ f) ↔ ∀ (t : Trace σ), t ⊨ f := Iff.rfl

@[push_ltl] theorem sem_entail_fin_iff : (⊨ᶠ f) ↔ ∀ (t : Trace σ), t.Finite → t ⊨ f := Iff.rfl

@[push_ltl] theorem sem_entail_inf_iff : (⊨ⁱ f) ↔ ∀ (t : Trace σ), t.Infinite → t ⊨ f := Iff.rfl

@[push_ltl] theorem sem_imp_iff : (f₁ ⇒ f₂) ↔ ∀ (t : Trace σ), t ⊨ f₁ ⇨ f₂ := Iff.rfl

theorem sem_imp_iff_sem_ential : (f₁ ⇒ f₂) ↔ ⊨ f₁ ⇨ f₂ := Iff.rfl

@[push_ltl] theorem sem_imp_fin_iff : (f₁ ⇒ᶠ f₂) ↔ ∀ (t : Trace σ) (_: t.Finite), t ⊨ f₁ ⇨ f₂ := by
  simp [TraceSet.sem_imp_fin, push_ltl]

@[push_ltl] theorem sem_imp_inf_iff : (f₁ ⇒ⁱ f₂) ↔ ∀ (t : Trace σ) (_: t.Infinite), t ⊨ f₁ ⇨ f₂ := by
  simp [TraceSet.sem_imp_inf, push_ltl]


lemma lt_of_sat_sshift {n : ℕ} (h : t ⊨ f.sshift n) : n < t.length := by
  rw [sat_sshift_iff] at h
  exact h.1

lemma not_sat_sshift_of_le {n : ℕ} (h : t.length ≤ n) : ¬(t ⊨ f.sshift n) := by
  simp [push_ltl]
  intro h'
  have := lt_of_lt_of_le h' h
  simp at this

lemma sat_wshift_of_le {n : ℕ} (h : t.length ≤ n) : (t ⊨ f.wshift n) := by
  simp [push_ltl]
  intro h'
  have := lt_of_lt_of_le h' h
  simp at this

lemma singleton_sat_wshift {s : σ} (c : ℕ) :
    (Trace.singleton s ⊨ f.wshift c) ↔ 0 < c ∨ (c = 0 ∧ Trace.singleton s ⊨ f) := by
  obtain h | h := Nat.eq_zero_or_pos c <;> simp [push_ltl, h]
  intro
  omega

-- TODO: Dual lemmas for unshift everywhere shift is

@[simp] lemma unshift_sat_snext_iff (s : σ) : (Trace.unshift s t ⊨ f.snext) ↔ (t ⊨ f) := by
  simp [push_ltl]

@[simp] lemma unshift_sat_wnext_iff (s : σ) : (Trace.unshift s t ⊨ f.wnext) ↔ (t ⊨ f) := by
  simp [push_ltl]

/-!
### Adjunctions
-/

lemma shift_sat_iff_sat_sshift {n : ℕ} (h : n < t.length) : (t.shift n h ⊨ f) ↔ (t ⊨ f.sshift n) := by
  constructor <;> simp [push_ltl, h]

lemma shift_sat_iff_sat_wshift {n : ℕ} (h : n < t.length) : (t.shift n h ⊨ f) ↔ (t ⊨ f.wshift n) := by
  constructor <;> simp [push_ltl, h]

/-!
### Negation pushing
-/

@[push_not_ltl, neg_norm_ltl] lemma not_not : fᶜᶜ = f := compl_compl f

@[push_not_ltl, neg_norm_ltl]
lemma not_sshift (n : ℕ) : (f.sshift n)ᶜ = fᶜ.wshift n := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_wshift (n : ℕ) : (f.wshift n)ᶜ = fᶜ.sshift n := by ext t; simp [push_ltl]

@[push_not_ltl] lemma not_finally : f.finallyᶜ = fᶜ.globally := by ext t; simp [push_ltl]

@[push_not_ltl] lemma not_globally : f.globallyᶜ = fᶜ.finally := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_and : (f₁ ⊓ f₂)ᶜ = f₁ᶜ ⊔ f₂ᶜ := by ext t; simp [push_ltl, imp_iff_not_or]

@[push_not_ltl, neg_norm_ltl]
lemma not_or : (f₁ ⊔ f₂)ᶜ = f₁ᶜ ⊓ f₂ᶜ := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_until : (f₁.until f₂)ᶜ = f₁ᶜ.release f₂ᶜ := by simp [release_eq]

@[push_not_ltl, neg_norm_ltl]
lemma not_release : (f₁.release f₂)ᶜ = f₁ᶜ.until f₂ᶜ := by simp [release_eq]

@[neg_norm_ltl]
lemma not_inj_iff : f₁ᶜ = f₂ᶜ ↔ f₁ = f₂ := compl_inj_iff

/-!
### General lemmas
-/

@[neg_norm_ltl]
lemma imp_eq_not_or : f₁ ⇨ f₂ = f₁ᶜ ⊔ f₂ := by ext t; simp [push_ltl, imp_iff_not_or]

@[simp] lemma sshift_zero : f.sshift 0 = f := by ext t; simp [push_ltl]

@[simp] lemma wshift_zero : f.wshift 0 = f := by ext t; simp [push_ltl]

lemma sat_wshift_of_sat_sshift (c : ℕ) (h : t ⊨ f.sshift c) : t ⊨ f.wshift c := by
  rw [sat_wshift_iff]
  intro
  rw [sat_sshift_iff] at h
  obtain ⟨_, hs⟩ := h
  exact hs

@[simp] lemma sshift_sshift (n₁ n₂ : ℕ) : (f.sshift n₁).sshift n₂ = f.sshift (n₁ + n₂) := by
  ext t
  simp only [push_ltl]
  simp only [Trace.shift_shift, Trace.shift_length, Nat.cast_add, lt_tsub_iff_left]
  constructor
  · rintro ⟨h₂, h₁, h⟩
    use (by rwa [add_comm])
  · rintro ⟨h, ht⟩
    refine ⟨?_, (by rwa [add_comm]), ht⟩
    clear ht
    revert h
    cases t.length
    · simp
    · norm_cast; omega

@[simp] lemma wshift_wshift (n₁ n₂ : ℕ) : (f.wshift n₁).wshift n₂ = f.wshift (n₂ + n₁) := by
  ext t
  simp only [push_ltl]
  simp only [Trace.shift_length, Trace.shift_shift, Nat.cast_add, add_comm, lt_tsub_iff_right]
  constructor
  · intro h hl
    refine h ?_ hl
    revert hl
    cases t.length
    · simp
    · norm_cast; omega
  · intro h _ hl
    exact h hl

-- TODO: are there sshift_wshift or wshift_sshift lemmas?

@[push_not_ltl, neg_norm_ltl]
lemma not_true : (⊤ᶜ : TraceSet σ) = ⊥ := compl_top

@[push_not_ltl, neg_norm_ltl]
lemma not_false : (⊥ᶜ : TraceSet σ) = ⊤ := compl_bot

@[simp]
lemma wshift_true (n : ℕ) : (⊤ : TraceSet σ).wshift n = ⊤ := by
  ext t; simp [push_ltl]

@[simp]
lemma sshift_false (n : ℕ) : (⊥ : TraceSet σ).sshift n = ⊥ := by
  ext t; simp [push_ltl]

lemma release_eq_not_until_not : f₁.release f₂ = (f₁ᶜ.until f₂ᶜ)ᶜ := rfl

lemma until_eq_not_release_not : f₁.until f₂ = (f₁ᶜ.release f₂ᶜ)ᶜ := by
  simp [release_eq_not_until_not]

lemma finally_eq_not_globally_not : f.finally = fᶜ.globallyᶜ := by
  simp [not_globally]

lemma globally_eq_not_finally_not : f.globally = fᶜ.finallyᶜ := by
  simp [not_finally]

lemma true_until : (⊤ : TraceSet σ).until f = f.finally := rfl

@[simp]
lemma false_until : (⊥ : TraceSet σ).until f = f := by
  ext t
  simp only [push_ltl]
  simp only [imp_false, not_lt]
  constructor
  · rintro ⟨n, h1, h2, h4⟩
    cases n
    · simpa using h4
    · specialize h1 0 (by simp)
      have := lt_of_lt_of_le t.nempty h1
      simp at this
  · intro h
    use 0
    simp [h]

@[simp, neg_norm_ltl]
lemma until_true : f.until ⊤  = ⊤  := by
  ext t
  simp only [push_ltl, iff_true]
  use 0
  simp

@[simp, neg_norm_ltl]
lemma until_false : f.until ⊥ = ⊥ := by
  ext t; simp [push_ltl, iff_false]

lemma false_release : (⊥ : TraceSet σ).release f = f.globally := by
  rw [globally_eq_not_finally_not, ← true_until]
  simp [push_not_ltl]

@[simp]
lemma true_release : (⊤ : TraceSet σ).release f = f := by
  rw [release_eq_not_until_not, not_true, false_until, not_not]

@[simp, neg_norm_ltl]
lemma release_true : f.release ⊤  = ⊤  := by
  rw [release_eq_not_until_not]
  simp

@[simp, neg_norm_ltl]
lemma release_false : f.release ⊥ = ⊥ := by
  rw [release_eq_not_until_not]
  simp

@[neg_norm_ltl]
lemma finally_eq_true_until : f.finally = (⊤ : TraceSet σ).until f := rfl

@[neg_norm_ltl]
lemma globally_eq_false_release : f.globally = (⊥ : TraceSet σ).release f := by
  rw [globally_eq_not_finally_not, finally_eq_true_until]
  simp [push_not_ltl]

@[simp]
lemma globally_true : (⊤ : TraceSet σ).globally = ⊤ := by
  simp [globally_eq_false_release]

@[simp]
lemma globally_false : (⊥ : TraceSet σ).globally = ⊥ := by
  simp [globally_eq_false_release]

@[simp]
lemma finally_true : (⊤ : TraceSet σ).finally = ⊤ := by
  simp [finally_eq_true_until]

@[simp]
lemma finally_false : (⊥ : TraceSet σ).finally = ⊥ := by
  simp [finally_eq_true_until]

theorem sat_finally_of (h : t ⊨ f) : t ⊨ f.finally := by
  rw [sat_finally_iff]
  use 0
  simpa

lemma sshift_until (n : ℕ) : (f₁.until f₂).sshift n = (f₁.sshift n).until (f₂.sshift n) := by
  ext t
  simp [push_ltl]
  constructor
  · rintro ⟨h1, k, h2, h3, h4⟩
    use k
    constructor
    · intro i h5 h6
      have h7 : n < t.length - i := by
        clear h4 h2
        revert h3 h5 h6 h1
        cases t.length
        · simp
        · norm_cast; omega
      use h7
      simp_rw [add_comm n]
      apply h2 _ h5
      exact lt_tsub_comm.mp h7
    · generalize_proofs h5 at h4
      rw [Nat.cast_add, add_comm] at h5
      use h5
      simpa [add_comm] using h4
  · rintro ⟨m, h1, h2, h3⟩
    have h4 : n < t.length := by
      clear h3
      revert h2
      cases t.length
      · simp
      · norm_cast; omega
    use h4, m
    constructor
    · intro i h5 h6
      simp only [add_comm i]
      have : i < t.length := by
        apply lt_of_lt_of_le h6
        simp
      obtain ⟨h7, h8⟩ := h1 i h5 this
      exact h8
    · use (by exact lt_tsub_iff_left.mpr h2)
      simpa only [add_comm] using h3

-- TODO: Does this hold too?
-- lemma wshift_until (n : ℕ) : (f₁.until f₂).wshift n = (f₁.wshift n).until (f₂.wshift n) := by
--   sorry

@[simp] theorem until_until : f₁.until (f₁.until f₂) = (f₁.until f₂) := by
  ext t
  constructor
  · rw [sat_until_iff]
    rintro ⟨n, h1, h2⟩
    have := lt_of_sat_sshift h2
    rw [← shift_sat_iff_sat_sshift this] at h2
    rw [sat_until_iff] at h2
    obtain ⟨n', h3, h2⟩ := h2
    rw [shift_sat_iff_sat_sshift, sshift_sshift] at h2
    rw [sat_until_iff]
    use (n + n')
    constructor
    · intro i hi
      simp [shift_sat_iff_sat_wshift] at h3
      specialize h3 (i - n)
      by_cases h : i < n
      · exact h1 _ h
      · simp at h
        simp [h] at h3
        apply h3
        omega
    · rwa [add_comm]
  · simp only [sat_until_iff, sat_wshift_iff, sat_sshift_iff, Trace.shift_length,
      Trace.shift_shift, forall_exists_index, and_imp]
    intro n h1 h2 h3
    use 0
    simp
    use n, h1, h2

lemma wshift_release (n : ℕ) : (f₁.release f₂).wshift n = (f₁.wshift n).release (f₂.wshift n) := by
  rw [release_eq_not_until_not, ← not_sshift, sshift_until, release_eq_not_until_not, not_wshift, not_wshift]

@[simp] theorem release_release : f₁.release (f₁.release f₂) = (f₁.release f₂) := by
  simp [release_eq_not_until_not]

@[simp] theorem finally_finally : f.finally.finally = f.finally := by
  ext t; simp [finally_eq]

@[simp] theorem globally_globally : f.globally.globally = f.globally := by
  simp [globally_eq]

/-!
### Distributivity
-/

lemma wshift_and_distrib (n : ℕ) : (f₁ ⊓ f₂).wshift n = (f₁.wshift n) ⊓ (f₂.wshift n) := by
  ext t; simp [push_ltl, forall_and]

lemma wshift_or_distrib (n : ℕ) : (f₁ ⊔ f₂).wshift n = (f₁.wshift n) ⊔ (f₂.wshift n) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_and_distrib (n : ℕ) : (f₁ ⊓ f₂).sshift n = (f₁.sshift n) ⊓ (f₂.sshift n) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_or_distrib (n : ℕ) : (f₁ ⊔ f₂).sshift n = (f₁.sshift n) ⊔ (f₂.sshift n) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma until_or_distrib : f₁.until (f₂ ⊔ f₃) = (f₁.until f₂) ⊔ (f₁.until f₃) := by
  ext t; simp only [push_ltl, exists_or, ← exists_or, ← and_or_left]

lemma and_until_distrib : (f₁ ⊓ f₂).until f₃ = (f₁.until f₃) ⊓ (f₂.until f₃) := by
  ext t
  simp only [push_ltl]
  constructor
  . aesop
  . rintro ⟨⟨n, ⟨h₁, ⟨h_t_n, h₂⟩⟩⟩, ⟨j,⟨h₃,⟨h_t_j,h₄⟩⟩⟩⟩
    by_cases h₅: n < j
    . use n
      simp_all only [_root_.true_and, exists_const, _root_.and_true]
      intro i h₅ h_t_i
      have : i < j := by linarith
      simp_all
    . use j
      simp_all only [not_lt, _root_.and_true, exists_const]
      intro i h₅ h_t_i
      have : i < n := by linarith
      simp_all

lemma release_and_distrib : f₁.release (f₂ ⊓ f₃) = (f₁.release f₂) ⊓ (f₁.release f₃) := by
  simp [release_eq, not_or, not_and, until_or_distrib]

lemma or_release_distrib : (f₁ ⊔ f₂).release f₃ = (f₁.release f₃) ⊔ (f₂.release f₃) := by
  simp [release_eq, not_or, not_and, and_until_distrib]

lemma finally_or_distrib : (f₁ ⊔ f₂).finally = f₁.finally ⊔ f₂.finally := by
  ext t; simp [push_ltl, exists_or]

lemma globally_and_distrib : (f₁ ⊓ f₂).globally = f₁.globally ⊓ f₂.globally := by
  ext t; simp [push_ltl, forall_and]

/-!
### Conditional lemmas
-/

theorem not_anti (h : f₁ ⇒ f₂) : f₂ᶜ ⇒ f₁ᶜ := by
  intro t
  exact mt (h t)

theorem snext_mono (h : f₁ ⇒ f₂) : f₁.snext ⇒ f₂.snext := by
  simp +contextual only [sem_imp_iff, sat_imp_iff, sat_sshift_iff, Nat.cast_one,
    forall_exists_index, exists_true_left]
  intro _ _ h'
  exact h _ h'

theorem wnext_mono (h : f₁ ⇒ f₂) : f₁.wnext ⇒ f₂.wnext := by
  simp only [sem_imp_iff, sat_imp_iff, sat_wshift_iff, Nat.cast_one]
  intro _ h' h''
  exact h _ (h' h'')

theorem globally_mono (h : f₁ ⇒ f₂) : f₁.globally ⇒ f₂.globally := by
  simp only [sem_imp_iff, sat_imp_iff, sat_globally_iff, sat_wshift_iff]
  intro _ h'
  peel h'
  exact h _ this

theorem finally_mono (h : f₁ ⇒ f₂) : f₁.finally ⇒ f₂.finally := by
  rw [finally_eq_not_globally_not, finally_eq_not_globally_not]
  apply not_anti
  apply globally_mono
  apply not_anti h

theorem sat_globally_imp_of (h : t ⊨ (f₁ ⇨ f₂).globally) : t ⊨ f₁.globally ⇨ f₂.globally := by
  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at h ⊢
  intro h1 _ _
  apply h
  apply h1

theorem sat_finally_imp_finally_of (h : t ⊨ (f₁ ⇨ f₂).globally) : t ⊨ f₁.finally ⇨ f₂.finally := by
  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff, sat_finally_iff, sat_sshift_iff,
    forall_exists_index] at h ⊢
  intro n hn h2
  refine ⟨_, _, h n hn h2⟩

theorem sat_finally_imp_of (h : t ⊨ f₁.finally ⇨ f₂.finally) : t ⊨ (f₁ ⇨ f₂).finally := by
  simp only [sat_imp_iff, sat_finally_iff, sat_sshift_iff, forall_exists_index] at h ⊢
  by_cases h' : t ⊨ f₂.finally
  · simp only [sat_finally_iff, sat_sshift_iff] at h'
    obtain ⟨n, hn, h'⟩ := h'
    use n, hn
    simp [h']
  · simp only [sat_finally_iff, sat_sshift_iff, not_exists] at h'
    specialize h 0
    simp only [CharP.cast_eq_zero, Trace.nempty, Trace.shift_zero, h', exists_false, exists_const,
      imp_false, forall_const] at h
    use 0
    simp [h]

theorem sat_finally_imp_of_finally_imp (h : t ⊨ f₁.finally ⇨ f₂.globally) : t ⊨ (f₁ ⇨ f₂).globally := by
  simp only [sat_imp_iff, sat_finally_iff, sat_sshift_iff, sat_globally_iff, sat_wshift_iff,
    forall_exists_index] at h ⊢
  intro n _ h'
  exact h n _ h' _ _

/-!
### Temporal unfolding
-/

theorem until_eq_or_and :
    f₁.until f₂ = f₂ ⊔ (f₁ ⊓ (f₁.until f₂).snext) := by
  ext t
  cases t using Trace.unshift_cases with
  | singleton =>
    simp [push_ltl]
    constructor
    · rintro ⟨_, _, rfl, h⟩
      exact h
    · intro h
      use 0
      simp [h]
  | unshift s t =>
    simp [push_ltl]
    constructor
    · rintro ⟨n, h1, h2, h3⟩
      cases n with
      | zero => simp at h3; simp [h3]
      | succ n =>
        right
        simp [Trace.shift_unshift_succ] at h3
        have h1' := h1 0 (by simp) (by simp)
        rw [Trace.shift_zero] at h1'
        refine ⟨h1', n, ?_, (by simpa using h2), h3⟩
        intro i hi ht
        have := h1 (i + 1) (by omega) (by simp [ht])
        simpa using this
    · rintro (h | ⟨h1, n, h3, h4, h5⟩)
      · use 0
        simp [h]
      · use (n + 1)
        simp [h5, h4]
        intro i h6 h7
        cases i with
        | zero => simp [h1]
        | succ n => simp; apply h3; omega

theorem release_eq_and_or :
    f₁.release f₂ = f₂ ⊓ (f₁ ⊔ (f₁.release f₂).wnext) := by
  conv_lhs =>
    rw [release_eq_not_until_not, until_eq_or_and]
    simp only [push_not_ltl]

theorem finally_eq_or_finally : f.finally = f ⊔ f.finally.snext := by
  conv_lhs =>
    rw [finally_eq, until_eq_or_and, ← finally_eq, top_inf_eq]

theorem globally_eq_and_globally : f.globally = f ⊓ f.globally.wnext := by
  conv_lhs =>
    rw [globally_eq, finally_eq_or_finally]
    simp [push_not_ltl]

/-!
### More semantics lemmas
-/

lemma unshift_sat_globally_iff (s : σ) :
    (Trace.unshift s t ⊨ TraceSet.globally f) ↔ (Trace.unshift s t ⊨ f) ∧ (t ⊨ TraceSet.globally f) := by
  rw (occs := [1]) [globally_eq_and_globally]
  simp [push_ltl]

/--
Induction principle for proving `t ⊨ .globally p`.
-/
theorem globally_induction {p : TraceSet σ} (t : Trace σ)
    (base : t ⊨ p) (step : t ⊨ .globally (p ⇨ p.wnext)) :
    t ⊨ .globally p := by
  simp [push_ltl]
  intro n h_n
  induction n
  . simp; exact base
  . rename_i n ih
    simp [push_ltl] at step
    have h2 : n < t.length := by
      rw [ENat.coe_add] at h_n
      simp at h_n
      refine (ENat.add_one_le_iff ?_).mp ?_
      exact ENat.coe_ne_top n
      exact le_of_lt h_n
    specialize ih h2
    specialize step n h2 ih (lt_tsub_iff_left.mpr h_n)
    simpa only [add_comm] using step
