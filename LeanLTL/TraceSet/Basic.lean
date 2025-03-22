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
### Semantics lemmas (lemmas about `⊨`)
-/

@[push_ltl] lemma sat_const_iff (p : Prop) : (t ⊨ TraceSet.const p) ↔ p := Iff.rfl
@[push_ltl] lemma sat_true_iff : (t ⊨ TraceSet.true) ↔ True := Iff.rfl
@[push_ltl] lemma sat_false_iff : (t ⊨ TraceSet.false) ↔ False := Iff.rfl

@[push_ltl] lemma sat_not_iff : (t ⊨ f.not) ↔ ¬(t ⊨ f) := Iff.rfl
@[push_ltl] lemma sat_and_iff : (t ⊨ f₁.and f₂) ↔ (t ⊨ f₁) ∧ (t ⊨ f₂) := Iff.rfl
@[push_ltl] lemma sat_or_iff : (t ⊨ f₁.or f₂) ↔ (t ⊨ f₁) ∨ (t ⊨ f₂) := Iff.rfl
@[push_ltl] lemma sat_imp_iff : (t ⊨ f₁.imp f₂) ↔ ((t ⊨ f₁) → (t ⊨ f₂)) := Iff.rfl
@[push_ltl] lemma sat_iff_iff : (t ⊨ f₁.iff f₂) ↔ ((t ⊨ f₁) ↔ (t ⊨ f₂)) := Iff.rfl

@[push_ltl] theorem sat_forall_iff (p : α → TraceSet σ) :
  (t ⊨ (TraceSet.forall p)) ↔ (∀ x, t ⊨ p x) := Iff.rfl
@[push_ltl] theorem sat_exists_iff (p : α → TraceSet σ) :
  (t ⊨ (TraceSet.exists p)) ↔ (∃ x, t ⊨ p x) := Iff.rfl

@[push_ltl] lemma sat_wshift_iff (c : ℕ) :
    (t ⊨ f.wshift c) ↔ ∀ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_ltl] lemma sat_sshift_iff (c : ℕ) :
    (t ⊨ f.sshift c) ↔ ∃ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_ltl] lemma sat_until_iff :
    (t ⊨ f₁.until f₂) ↔ ∃ n, (∀ i < n, t ⊨ f₁.wshift i) ∧ (t ⊨ f₂.sshift n) := Iff.rfl

@[push_ltl] lemma sat_release_iff :
    (t ⊨ f₁.release f₂) ↔ ∀ (n : ℕ), (∀ i < n, ¬ t ⊨ f₁.sshift i) → (t ⊨ f₂.wshift n) := by
  simp only [TraceSet.release, push_ltl]
  simp

/-- Alternative formulation of `sat_release_iff`, without negations. -/
lemma sat_release_iff' :
    (t ⊨ f₁.release f₂) ↔ ∀ (n : ℕ), (∃ i < n, t ⊨ f₁.sshift i) ∨ (t ⊨ f₂.wshift n) := by
  simp only [sat_release_iff, imp_iff_not_or]
  push_neg
  rfl

@[push_ltl] theorem sat_finally_iff : (t ⊨ f.finally) ↔ ∃ n, t ⊨ f.sshift n := by
  simp [TraceSet.finally, push_ltl]

@[push_ltl] theorem sat_globally_iff : (t ⊨ f.globally) ↔ ∀ n, t ⊨ f.wshift n := by
  simp [TraceSet.globally, push_ltl]

@[push_ltl] theorem sat_sget_iff (f : TraceFun σ α) (p : α → TraceSet σ) : (t ⊨ f.sget p) ↔ ∃ x, f t = some x ∧ (t ⊨ p x) := by
  simp only [TraceFun.sget, TraceFun.get]
  split <;> simp [*]

@[push_ltl] theorem sat_wget_iff (f : TraceFun σ α) (p : α → TraceSet σ) : (t ⊨ f.wget p) ↔ ∀ x, f t = some x → (t ⊨ p x) := by
  simp only [TraceFun.wget, TraceFun.get]
  split <;> simp [*]

@[push_ltl] theorem sem_entail_iff : (⊨ f) ↔ ∀ (t : Trace σ), t ⊨ f := Iff.rfl

@[push_ltl] theorem sem_entail_fin_iff : (⊨ᶠ f) ↔ ∀ (t : Trace σ), t.Finite → t ⊨ f := Iff.rfl

@[push_ltl] theorem sem_entail_inf_iff : (⊨ⁱ f) ↔ ∀ (t : Trace σ), t.Infinite → t ⊨ f := Iff.rfl

@[push_ltl] theorem sem_imp_iff : (f₁ ⇒ f₂) ↔ ∀ (t : Trace σ), t ⊨ f₁.imp f₂ := Iff.rfl

theorem sem_imp_iff_sem_ential : (f₁ ⇒ f₂) ↔ ⊨ f₁.imp f₂ := Iff.rfl

@[push_ltl] theorem sem_imp_fin_iff : (f₁ ⇒ᶠ f₂) ↔ ∀ (t : Trace σ) (_: t.Finite), t ⊨ f₁.imp f₂ := by
  simp [TraceSet.sem_imp_fin, push_ltl]

@[push_ltl] theorem sem_imp_inf_iff : (f₁ ⇒ⁱ f₂) ↔ ∀ (t : Trace σ) (_: t.Infinite), t ⊨ f₁.imp f₂ := by
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

@[simp, push_not_ltl, neg_norm_ltl] lemma not_not : f.not.not = f := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_sshift (n : ℕ) : (f.sshift n).not = f.not.wshift n := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_wshift (n : ℕ) : (f.wshift n).not = f.not.sshift n := by ext t; simp [push_ltl]

@[push_not_ltl] lemma not_finally : f.finally.not = f.not.globally := by ext t; simp [push_ltl]

@[push_not_ltl] lemma not_globally : f.globally.not = f.not.finally := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_and : (f₁.and f₂).not = f₁.not.or f₂.not := by ext t; simp [push_ltl, imp_iff_not_or]

@[push_not_ltl, neg_norm_ltl]
lemma not_or : (f₁.or f₂).not = f₁.not.and f₂.not := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_until : (f₁.until f₂).not = f₁.not.release f₂.not := by simp [TraceSet.release]

@[push_not_ltl, neg_norm_ltl]
lemma not_release : (f₁.release f₂).not = f₁.not.until f₂.not := by simp [TraceSet.release]

@[simp, neg_norm_ltl]
lemma not_inj_iff : f₁.not = f₂.not ↔ f₁ = f₂ := by
  constructor
  · intro h
    ext t
    simpa [push_ltl, not_iff_not] using congr(t ⊨ $h)
  · simp +contextual

/-!
### General lemmas
-/

@[neg_norm_ltl]
lemma imp_eq_not_or : f₁.imp f₂ = f₁.not.or f₂ := by ext t; simp [push_ltl, imp_iff_not_or]

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

@[simp, push_not_ltl, neg_norm_ltl]
lemma not_true : TraceSet.true.not = (TraceSet.false : TraceSet σ) := by
  ext t; simp [push_ltl]

@[simp, push_not_ltl, neg_norm_ltl]
lemma not_false : TraceSet.false.not = (TraceSet.true : TraceSet σ) := by
  ext t; simp [push_ltl]

@[simp] lemma true_and : TraceSet.true.and f = f := by ext t; simp [push_ltl]

@[simp] lemma and_true : f.and TraceSet.true = f := by ext t; simp [push_ltl]

@[simp] lemma false_and : TraceSet.false.and f = TraceSet.false := by ext t; simp [push_ltl]

@[simp] lemma and_false : f.and TraceSet.false = TraceSet.false := by ext t; simp [push_ltl]

@[simp] lemma false_or : TraceSet.false.or f = f := by ext t; simp [push_ltl]

@[simp] lemma or_false : f.or TraceSet.false = f := by ext t; simp [push_ltl]

@[simp] lemma true_or : TraceSet.true.or f = TraceSet.true := by ext t; simp [push_ltl]

@[simp] lemma or_true : f.or TraceSet.true = TraceSet.true := by ext t; simp [push_ltl]

@[simp]
lemma wshift_true (n : ℕ) : TraceSet.true.wshift n = (TraceSet.true : TraceSet σ) := by
  ext t; simp [push_ltl]

@[simp]
lemma sshift_false (n : ℕ) : TraceSet.false.sshift n = (TraceSet.false : TraceSet σ) := by
  ext t; simp [push_ltl]

lemma release_eq_not_until_not : f₁.release f₂ = (f₁.not.until f₂.not).not := rfl

lemma until_eq_not_release_not : f₁.until f₂ = (f₁.not.release f₂.not).not := by
  simp [release_eq_not_until_not]

lemma finally_eq_not_globally_not : f.finally = f.not.globally.not := by
  simp [not_globally]

lemma globally_eq_not_finally_not : f.globally = f.not.finally.not := by
  simp [not_finally]

lemma true_until : TraceSet.true.until f = f.finally := rfl

@[simp]
lemma false_until : TraceSet.false.until f = f := by
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
lemma until_true : f.until TraceSet.true = TraceSet.true := by
  ext t
  simp only [push_ltl, iff_true]
  use 0
  simp

@[simp, neg_norm_ltl]
lemma until_false : f.until TraceSet.false = TraceSet.false := by
  ext t; simp [push_ltl, iff_false]

lemma false_release : TraceSet.false.release f = f.globally := by
  rw [globally_eq_not_finally_not, ← true_until]
  simp [push_not_ltl]

@[simp]
lemma true_release : TraceSet.true.release f = f := by
  rw [release_eq_not_until_not, not_true, false_until, not_not]

@[simp, neg_norm_ltl]
lemma release_true : f.release TraceSet.true = TraceSet.true := by
  rw [release_eq_not_until_not]
  simp

@[simp, neg_norm_ltl]
lemma release_false : f.release TraceSet.false = TraceSet.false := by
  rw [release_eq_not_until_not]
  simp

@[neg_norm_ltl]
lemma finally_eq_true_until : f.finally = TraceSet.true.until f := rfl

@[neg_norm_ltl]
lemma globally_eq_false_release : f.globally = TraceSet.false.release f := by
  rw [globally_eq_not_finally_not, finally_eq_true_until]
  simp [push_not_ltl]

@[simp]
lemma globally_true : TraceSet.true.globally = (TraceSet.true : TraceSet σ) := by
  simp [globally_eq_false_release]

@[simp]
lemma globally_false : TraceSet.false.globally = (TraceSet.false : TraceSet σ) := by
  simp [globally_eq_false_release]

@[simp]
lemma finally_true : TraceSet.true.finally = (TraceSet.true : TraceSet σ) := by
  simp [finally_eq_true_until]

@[simp]
lemma finally_false : TraceSet.false.finally = (TraceSet.false : TraceSet σ) := by
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
  ext t; simp [TraceSet.finally]

@[simp] theorem globally_globally : f.globally.globally = f.globally := by
  simp [TraceSet.globally]

/-!
### Distributivity
-/

lemma wshift_and_distrib (n : ℕ) : (f₁.and f₂).wshift n = (f₁.wshift n).and (f₂.wshift n) := by
  ext t; simp [push_ltl, forall_and]

lemma wshift_or_distrib (n : ℕ) : (f₁.or f₂).wshift n = (f₁.wshift n).or (f₂.wshift n) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_and_distrib (n : ℕ) : (f₁.and f₂).sshift n = (f₁.sshift n).and (f₂.sshift n) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_or_distrib (n : ℕ) : (f₁.or f₂).sshift n = (f₁.sshift n).or (f₂.sshift n) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma until_or_distrib : f₁.until (f₂.or f₃) = (f₁.until f₂).or (f₁.until f₃) := by
  ext t; simp only [push_ltl, exists_or, ← exists_or, ← and_or_left]

lemma and_until_distrib : (f₁.and f₂).until f₃ = (f₁.until f₃).and (f₂.until f₃) := by
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

lemma release_and_distrib : f₁.release (f₂.and f₃) = (f₁.release f₂).and (f₁.release f₃) := by
  simp [TraceSet.release, not_or, not_and, until_or_distrib]

lemma or_release_distrib : (f₁.or f₂).release f₃ = (f₁.release f₃).or (f₂.release f₃) := by
  simp [TraceSet.release, not_or, not_and, and_until_distrib]

lemma finally_or_distrib : (f₁.or f₂).finally = f₁.finally.or f₂.finally := by
  ext t; simp [push_ltl, exists_or]

lemma globally_and_distrib : (f₁.and f₂).globally = f₁.globally.and f₂.globally := by
  ext t; simp [push_ltl, forall_and]

/-!
### Conditional lemmas
-/

theorem not_anti (h : f₁ ⇒ f₂) : f₂.not ⇒ f₁.not := by
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

theorem sat_globally_imp_of (h : t ⊨ (f₁.imp f₂).globally) : t ⊨ f₁.globally.imp f₂.globally := by
  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at h ⊢
  intro h1 _ _
  apply h
  apply h1

theorem sat_finally_imp_finally_of (h : t ⊨ (f₁.imp f₂).globally) : t ⊨ f₁.finally.imp f₂.finally := by
  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff, sat_finally_iff, sat_sshift_iff,
    forall_exists_index] at h ⊢
  intro n hn h2
  refine ⟨_, _, h n hn h2⟩

theorem sat_finally_imp_of (h : t ⊨ f₁.finally.imp f₂.finally) : t ⊨ (f₁.imp f₂).finally := by
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

theorem sat_finally_imp_of_finally_imp (h : t ⊨ f₁.finally.imp f₂.globally) : t ⊨ (f₁.imp f₂).globally := by
  simp only [sat_imp_iff, sat_finally_iff, sat_sshift_iff, sat_globally_iff, sat_wshift_iff,
    forall_exists_index] at h ⊢
  intro n _ h'
  exact h n _ h' _ _

/-!
### Temporal unfolding
-/

theorem until_eq_or_and :
    f₁.until f₂ = f₂.or (f₁.and (f₁.until f₂).snext) := by
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
    f₁.release f₂ = f₂.and (f₁.or (f₁.release f₂).wnext) := by
  conv_lhs =>
    rw [release_eq_not_until_not, until_eq_or_and]
    simp only [push_not_ltl]

theorem finally_eq_or_finally : f.finally = f.or f.finally.snext := by
  conv_lhs =>
    rw [TraceSet.finally, until_eq_or_and, ← TraceSet.finally, TraceSet.true_and]

theorem globally_eq_and_globally : f.globally = f.and f.globally.wnext := by
  conv_lhs =>
    rw [TraceSet.globally, finally_eq_or_finally]
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
    (base : t ⊨ p) (step : t ⊨ .globally (p.imp p.wnext)) :
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
