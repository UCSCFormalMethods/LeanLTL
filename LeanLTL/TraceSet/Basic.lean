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
variable {t : Trace σ} {f f₁ f₂ f₃ f₄ : TraceSet σ}

open scoped symmDiff

@[ext]
protected theorem ext {f g : TraceSet σ} (h : ∀ t, (t ⊨ f) ↔ (t ⊨ g)) : f = g := by
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
  isLUB_sSup s :=
    ⟨fun p hp t ht ↦ ⟨p, hp, ht⟩,
      fun p hp t ht ↦ by obtain ⟨q, hq, ht⟩ := ht; exact hp hq t ht⟩
  isGLB_sInf s :=
    ⟨fun p hp t ht ↦ ht p hp,
      fun p hp t ht q hq ↦ hp hq t ht⟩
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

lemma release_eq : f₁ 𝐑 f₂ = (f₁ᶜ 𝐔 f₂ᶜ)ᶜ := rfl

lemma finally_eq : 𝐅 f = ⊤ 𝐔 f := rfl

lemma globally_eq : 𝐆 f = (𝐅 fᶜ)ᶜ := rfl

/-!
### Notation normalization lemmas
-/

@[simp] lemma and_eq_inf : f₁.and f₂ = f₁ ⊓ f₂ := rfl
@[simp] lemma or_eq_sup : f₁.or f₂ = f₁ ⊔ f₂ := rfl
@[simp] lemma not_eq_compl : f.not = fᶜ := rfl
@[simp] lemma until_eq_until : f₁.until f₂ = f₁ 𝐔 f₂ := rfl
@[simp] lemma release_eq_release : f₁.release f₂ = f₁ 𝐑 f₂ := rfl
@[simp] lemma finally_eq_finally : f.finally = 𝐅 f := rfl
@[simp] lemma globally_eq_globally : f.globally = 𝐆 f := rfl
@[simp] lemma sshift_eq_sshift {i : ℕ} : f.sshift i = 𝐗ˢ(i) f := rfl
@[simp] lemma wshift_eq_wshift {i : ℕ} : f.wshift i = 𝐗ʷ(i) f := rfl

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
    (t ⊨ 𝐗ʷ(c) f) ↔ ∀ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_ltl] lemma sat_sshift_iff (c : ℕ) :
    (t ⊨ 𝐗ˢ(c) f) ↔ ∃ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_ltl] lemma sat_until_iff :
    (t ⊨ f₁ 𝐔 f₂) ↔ ∃ n, (∀ i < n, t ⊨ 𝐗ʷ(i) f₁) ∧ (t ⊨ 𝐗ˢ(n) f₂) := Iff.rfl

@[push_ltl] lemma sat_release_iff :
    (t ⊨ f₁ 𝐑 f₂) ↔ ∀ (n : ℕ), (∀ i < n, ¬ t ⊨ 𝐗ˢ(i) f₁) → (t ⊨ 𝐗ʷ(n) f₂) := by
  simp only [release_eq, push_ltl]
  simp

/-- Alternative formulation of `sat_release_iff`, without negations. -/
lemma sat_release_iff' :
    (t ⊨ f₁ 𝐑 f₂) ↔ ∀ (n : ℕ), (∃ i < n, t ⊨ 𝐗ˢ(i) f₁) ∨ (t ⊨ 𝐗ʷ(n) f₂) := by
  simp only [sat_release_iff, imp_iff_not_or]
  push Not
  rfl

@[push_ltl] theorem sat_finally_iff : (t ⊨ 𝐅 f) ↔ ∃ n, t ⊨ 𝐗ˢ(n) f := by
  simp [finally_eq, push_ltl]

@[push_ltl] theorem sat_globally_iff : (t ⊨ 𝐆 f) ↔ ∀ n, t ⊨ 𝐗ʷ(n) f := by
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

theorem sem_entail_iff_iff : (⊨ f₁ ⇔ f₂) ↔ ∀ (t : Trace σ), (t ⊨ f₁) ↔ (t ⊨ f₂) := by
  simp [sem_entail_iff, sat_iff_iff]

@[push_ltl] theorem sem_entail_fin_iff : (⊨ᶠ f) ↔ ∀ (t : Trace σ), t.Finite → t ⊨ f := Iff.rfl

theorem sem_entail_fin_iff_iff : (⊨ᶠ f₁ ⇔ f₂) ↔ ∀ (t : Trace σ), t.Finite → ((t ⊨ f₁) ↔ (t ⊨ f₂)) := by
  simp [sem_entail_fin_iff, sat_iff_iff]

@[push_ltl] theorem sem_entail_inf_iff : (⊨ⁱ f) ↔ ∀ (t : Trace σ), t.Infinite → t ⊨ f := Iff.rfl

theorem sem_entail_inf_iff_iff : (⊨ⁱ f₁ ⇔ f₂) ↔ ∀ (t : Trace σ), t.Infinite → ((t ⊨ f₁) ↔ (t ⊨ f₂)) := by
  simp [sem_entail_inf_iff, sat_iff_iff]

@[push_ltl] theorem sem_imp_iff : (f₁ ⇒ f₂) ↔ ∀ (t : Trace σ), t ⊨ f₁ ⇨ f₂ := Iff.rfl

theorem sem_imp_iff_sem_ential : (f₁ ⇒ f₂) ↔ ⊨ f₁ ⇨ f₂ := Iff.rfl

@[push_ltl] theorem sem_imp_fin_iff : (f₁ ⇒ᶠ f₂) ↔ ∀ (t : Trace σ) (_: t.Finite), t ⊨ f₁ ⇨ f₂ := by
  simp [TraceSet.sem_imp_fin, push_ltl]

@[push_ltl] theorem sem_imp_inf_iff : (f₁ ⇒ⁱ f₂) ↔ ∀ (t : Trace σ) (_: t.Infinite), t ⊨ f₁ ⇨ f₂ := by
  simp [TraceSet.sem_imp_inf, push_ltl]

@[simp] theorem sem_entail_true : ⊨ (⊤ : TraceSet σ) := by
  simp [sem_entail_iff, sat_true_iff]

@[simp] theorem sem_entail_false [Nonempty (Trace σ)] : ¬ ⊨ (⊥ : TraceSet σ) := by
  simp [sem_entail_iff, sat_false_iff]

lemma lt_of_sat_sshift {n : ℕ} (h : t ⊨ 𝐗ˢ(n) f) : n < t.length := by
  rw [sat_sshift_iff] at h
  exact h.1

lemma not_sat_sshift_of_le {n : ℕ} (h : t.length ≤ n) : ¬(t ⊨ 𝐗ˢ(n) f) := by
  contrapose! h
  exact lt_of_sat_sshift h

lemma sat_wshift_of_le {n : ℕ} (h : t.length ≤ n) : (t ⊨ 𝐗ʷ(n) f) := by
  simp [push_ltl]
  intro h'
  have := lt_of_lt_of_le h' h
  simp at this

lemma singleton_sat_wshift {s : σ} (c : ℕ) :
    (Trace.singleton s ⊨ 𝐗ʷ(c) f) ↔ 0 < c ∨ (c = 0 ∧ Trace.singleton s ⊨ f) := by
  obtain h | h := Nat.eq_zero_or_pos c <;> simp [push_ltl, h]
  intro
  omega

-- TODO: Dual lemmas for unshift everywhere shift is

@[simp] lemma unshift_sat_snext_iff (s : σ) : (Trace.unshift s t ⊨ 𝐗ˢ f) ↔ (t ⊨ f) := by
  simp [push_ltl]

@[simp] lemma unshift_sat_wnext_iff (s : σ) : (Trace.unshift s t ⊨ 𝐗ʷ f) ↔ (t ⊨ f) := by
  simp [push_ltl]

/-!
### Adjunctions
-/

lemma shift_sat_iff_sat_sshift {n : ℕ} (h : n < t.length) : (t.shift n h ⊨ f) ↔ (t ⊨ 𝐗ˢ(n) f) := by
  constructor <;> simp [push_ltl, h]

lemma shift_sat_iff_sat_wshift {n : ℕ} (h : n < t.length) : (t.shift n h ⊨ f) ↔ (t ⊨ 𝐗ʷ(n) f) := by
  constructor <;> simp [push_ltl, h]

/-!
### Negation pushing
-/

@[push_not_ltl, neg_norm_ltl] lemma not_not : fᶜᶜ = f := compl_compl f

@[push_not_ltl, neg_norm_ltl]
lemma not_sshift (n : ℕ) : (𝐗ˢ(n) f)ᶜ = 𝐗ʷ(n) fᶜ := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_wshift (n : ℕ) : (𝐗ʷ(n) f)ᶜ = 𝐗ˢ(n) fᶜ := by ext t; simp [push_ltl]

@[push_not_ltl] lemma not_finally : (𝐅 f)ᶜ = 𝐆 fᶜ := by ext t; simp [push_ltl]

@[push_not_ltl] lemma not_globally : (𝐆 f)ᶜ = 𝐅 fᶜ := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_and : (f₁ ⊓ f₂)ᶜ = f₁ᶜ ⊔ f₂ᶜ := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_or : (f₁ ⊔ f₂)ᶜ = f₁ᶜ ⊓ f₂ᶜ := by ext t; simp [push_ltl]

@[push_not_ltl, neg_norm_ltl]
lemma not_until : (f₁ 𝐔 f₂)ᶜ = f₁ᶜ 𝐑 f₂ᶜ := by simp [release_eq]

@[push_not_ltl, neg_norm_ltl]
lemma not_release : (f₁ 𝐑 f₂)ᶜ = f₁ᶜ 𝐔 f₂ᶜ := by simp [release_eq]

@[neg_norm_ltl]
lemma not_inj_iff : f₁ᶜ = f₂ᶜ ↔ f₁ = f₂ := compl_inj_iff

/-!
### General lemmas
-/

@[neg_norm_ltl]
lemma imp_eq_not_or : f₁ ⇨ f₂ = f₁ᶜ ⊔ f₂ := by ext t; simp [push_ltl, imp_iff_not_or]

@[simp] lemma sshift_zero : 𝐗ˢ(0) f = f := by ext t; simp [push_ltl]

@[simp] lemma wshift_zero : 𝐗ʷ(0) f = f := by ext t; simp [push_ltl]

lemma sat_wshift_of_sat_sshift (c : ℕ) (h : t ⊨ 𝐗ˢ(c) f) : t ⊨ 𝐗ʷ(c) f := by
  rw [sat_wshift_iff]
  intro
  rw [sat_sshift_iff] at h
  obtain ⟨_, hs⟩ := h
  exact hs

@[simp] lemma sshift_sshift (n₁ n₂ : ℕ) : 𝐗ˢ(n₂) (𝐗ˢ(n₁) f) = 𝐗ˢ(n₁ + n₂) f := by
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

@[simp] lemma wshift_wshift (n₁ n₂ : ℕ) : 𝐗ʷ(n₂) (𝐗ʷ(n₁) f) = 𝐗ʷ(n₂ + n₁) f := by
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

-- `compl_top` is already a simp lemma
@[push_not_ltl, neg_norm_ltl]
lemma not_true : (⊤ᶜ : TraceSet σ) = ⊥ := compl_top

-- `compl_bot` is already a simp lemma
@[push_not_ltl, neg_norm_ltl]
lemma not_false : (⊥ᶜ : TraceSet σ) = ⊤ := compl_bot

@[simp]
lemma wshift_true (n : ℕ) : 𝐗ʷ(n) (⊤ : TraceSet σ) = ⊤ := by
  ext t; simp [push_ltl]

@[simp]
lemma sshift_false (n : ℕ) : 𝐗ˢ(n) (⊥ : TraceSet σ) = ⊥ := by
  ext t; simp [push_ltl]

lemma release_eq_not_until_not : f₁ 𝐑 f₂ = (f₁ᶜ 𝐔 f₂ᶜ)ᶜ := rfl

lemma until_eq_not_release_not : f₁ 𝐔 f₂ = (f₁ᶜ 𝐑 f₂ᶜ)ᶜ := by
  simp [release_eq_not_until_not]

lemma finally_eq_not_globally_not : 𝐅 f = (𝐆 fᶜ)ᶜ := by
  simp [not_globally]

lemma globally_eq_not_finally_not : 𝐆 f = (𝐅 fᶜ)ᶜ := by
  simp [not_finally]

lemma true_until : ⊤ 𝐔 f = 𝐅 f := rfl

@[simp]
lemma false_until : ⊥ 𝐔 f = f := by
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
lemma until_true : f 𝐔 ⊤  = ⊤  := by
  ext t
  simp only [push_ltl, iff_true]
  use 0
  simp

@[simp, neg_norm_ltl]
lemma until_false : f 𝐔 ⊥ = ⊥ := by
  ext t; simp [push_ltl]

lemma false_release : ⊥ 𝐑 f = 𝐆 f := by
  rw [globally_eq_not_finally_not, ← true_until]
  simp [push_not_ltl]

@[simp]
lemma true_release : ⊤ 𝐑 f = f := by
  rw [release_eq_not_until_not, not_true, false_until, not_not]

@[simp, neg_norm_ltl]
lemma release_true : f 𝐑 ⊤  = ⊤  := by
  rw [release_eq_not_until_not]
  simp

@[simp, neg_norm_ltl]
lemma release_false : f 𝐑 ⊥ = ⊥ := by
  rw [release_eq_not_until_not]
  simp

@[neg_norm_ltl]
lemma finally_eq_true_until : 𝐅 f = ⊤ 𝐔 f := rfl

@[neg_norm_ltl]
lemma globally_eq_false_release : 𝐆 f = ⊥ 𝐑 f := by
  rw [globally_eq_not_finally_not, finally_eq_true_until]
  simp [push_not_ltl]

@[simp]
lemma globally_true : 𝐆 (⊤ : TraceSet σ) = ⊤ := by
  simp [globally_eq_false_release]

@[simp]
lemma globally_false : 𝐆 (⊥ : TraceSet σ) = ⊥ := by
  simp [globally_eq_false_release]

@[simp]
lemma finally_true : 𝐅 (⊤ : TraceSet σ) = ⊤ := by
  simp [finally_eq_true_until]

@[simp]
lemma finally_false : 𝐅 (⊥ : TraceSet σ) = ⊥ := by
  simp [finally_eq_true_until]

theorem sat_finally_of (h : t ⊨ f) : t ⊨ 𝐅 f := by
  rw [sat_finally_iff]
  use 0
  simpa

lemma sshift_until (n : ℕ) : 𝐗ˢ(n) (f₁ 𝐔 f₂) = (𝐗ˢ(n) f₁) 𝐔 (𝐗ˢ(n) f₂) := by
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

@[simp] theorem until_until : f₁ 𝐔 (f₁ 𝐔 f₂) = f₁ 𝐔 f₂ := by
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

lemma wshift_release (n : ℕ) : 𝐗ʷ(n) (f₁ 𝐑 f₂) = (𝐗ʷ(n) f₁) 𝐑 (𝐗ʷ(n) f₂) := by
  rw [release_eq_not_until_not, ← not_sshift, sshift_until, release_eq_not_until_not, not_wshift, not_wshift]

@[simp] theorem release_release : f₁ 𝐑 (f₁ 𝐑 f₂) = f₁ 𝐑 f₂ := by
  simp [release_eq_not_until_not]

@[simp] theorem finally_finally : 𝐅 𝐅 f = 𝐅 f := by
  ext t; simp [finally_eq]

@[simp] theorem globally_globally : 𝐆 𝐆 f = 𝐆 f := by
  simp [globally_eq]

/-!
### Distributivity
-/

lemma wshift_and_distrib (n : ℕ) : 𝐗ʷ(n) (f₁ ⊓ f₂) = (𝐗ʷ(n) f₁) ⊓ (𝐗ʷ(n) f₂) := by
  ext t; simp [push_ltl, forall_and]

lemma wshift_or_distrib (n : ℕ) : 𝐗ʷ(n) (f₁ ⊔ f₂) = (𝐗ʷ(n) f₁) ⊔ (𝐗ʷ(n) f₂) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_and_distrib (n : ℕ) : 𝐗ˢ(n) (f₁ ⊓ f₂) = (𝐗ˢ(n) f₁) ⊓ (𝐗ˢ(n) f₂) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_or_distrib (n : ℕ) : 𝐗ˢ(n) (f₁ ⊔ f₂) = (𝐗ˢ(n) f₁) ⊔ (𝐗ˢ(n) f₂) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma wshift_and_wshift (n : ℕ) : (𝐗ʷ(n) f₁) ⊓ (𝐗ʷ(n) f₂) = 𝐗ʷ(n) (f₁ ⊓ f₂) :=
  (wshift_and_distrib n).symm

lemma sshift_and_sshift (n : ℕ) : (𝐗ˢ(n) f₁) ⊓ (𝐗ˢ(n) f₂) = 𝐗ˢ(n) (f₁ ⊓ f₂) :=
  (sshift_and_distrib n).symm

lemma wshift_and_sshift (n : ℕ) : (𝐗ʷ(n) f₁) ⊓ (𝐗ˢ(n) f₂) = 𝐗ˢ(n) (f₁ ⊓ f₂) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_and_wshift (n : ℕ) : (𝐗ˢ(n) f₁) ⊓ (𝐗ʷ(n) f₂) = 𝐗ˢ(n) (f₁ ⊓ f₂) := by
  rw [inf_comm, wshift_and_sshift, inf_comm]

lemma wshift_or_sshift (n : ℕ) : (𝐗ʷ(n) f₁) ⊔ (𝐗ˢ(n) f₂) = 𝐗ʷ(n) (f₁ ⊔ f₂) := by
  ext t; by_cases n < t.length <;> simp [push_ltl, *]

lemma sshift_or_wshift (n : ℕ) : (𝐗ˢ(n) f₁) ⊔ (𝐗ʷ(n) f₂) = 𝐗ʷ(n) (f₁ ⊔ f₂) := by
  rw [sup_comm, wshift_or_sshift, sup_comm]

lemma until_or_distrib : f₁ 𝐔 (f₂ ⊔ f₃) = (f₁ 𝐔 f₂) ⊔ (f₁ 𝐔 f₃) := by
  ext t; simp only [push_ltl, ← exists_or, ← and_or_left]

lemma and_until_distrib : (f₁ ⊓ f₂) 𝐔 f₃ = (f₁ 𝐔 f₃) ⊓ (f₂ 𝐔 f₃) := by
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

lemma release_and_distrib : f₁ 𝐑 (f₂ ⊓ f₃) = (f₁ 𝐑 f₂) ⊓ (f₁ 𝐑 f₃) := by
  simp [release_eq, until_or_distrib]

lemma or_release_distrib : (f₁ ⊔ f₂) 𝐑 f₃ = (f₁ 𝐑 f₃) ⊔ (f₂ 𝐑 f₃) := by
  simp [release_eq, and_until_distrib]

lemma finally_or_distrib : 𝐅 (f₁ ⊔ f₂) = 𝐅 f₁ ⊔ 𝐅 f₂ := by
  ext t; simp [push_ltl, exists_or]

lemma globally_and_distrib : 𝐆 (f₁ ⊓ f₂) = 𝐆 f₁ ⊓ 𝐆 f₂ := by
  ext t; simp [push_ltl, forall_and]

/-!
### Finite trace congruence lemmas
-/

theorem entail_fin_not_congr (h : ⊨ᶠ f₁ ⇔ f₂) : ⊨ᶠ f₁ᶜ ⇔ f₂ᶜ := by
  rw [sem_entail_fin_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_fin_sshift_congr (h : ⊨ᶠ f₁ ⇔ f₂) {n} : ⊨ᶠ 𝐗ˢ(n) f₁ ⇔ 𝐗ˢ(n) f₂ := by
  rw [sem_entail_fin_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_fin_wshift_congr (h : ⊨ᶠ f₁ ⇔ f₂) {n} : ⊨ᶠ 𝐗ʷ(n) f₁ ⇔ 𝐗ʷ(n) f₂ := by
  rw [sem_entail_fin_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_fin_finally_congr (h : ⊨ᶠ f₁ ⇔ f₂) : ⊨ᶠ 𝐅 f₁ ⇔ 𝐅 f₂ := by
  rw [sem_entail_fin_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_fin_globally_congr (h : ⊨ᶠ f₁ ⇔ f₂) : ⊨ᶠ 𝐆 f₁ ⇔ 𝐆 f₂ := by
  rw [sem_entail_fin_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_fin_and_congr (h : ⊨ᶠ f₁ ⇔ f₃) (h' : ⊨ᶠ f₂ ⇔ f₄) : ⊨ᶠ (f₁ ⊓ f₂) ⇔ (f₃ ⊓ f₄) := by
  rw [sem_entail_fin_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_fin_or_congr (h : ⊨ᶠ f₁ ⇔ f₃) (h' : ⊨ᶠ f₂ ⇔ f₄) : ⊨ᶠ (f₁ ⊔ f₂) ⇔ (f₃ ⊔ f₄) := by
  rw [sem_entail_fin_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_fin_imp_congr (h : ⊨ᶠ f₁ ⇔ f₃) (h' : ⊨ᶠ f₂ ⇔ f₄) : ⊨ᶠ (f₁ ⇨ f₂) ⇔ (f₃ ⇨ f₄) := by
  rw [sem_entail_fin_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_fin_iff_congr (h : ⊨ᶠ f₁ ⇔ f₃) (h' : ⊨ᶠ f₂ ⇔ f₄) : ⊨ᶠ (f₁ ⇔ f₂) ⇔ (f₃ ⇔ f₄) := by
  rw [sem_entail_fin_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_fin_until_congr (h : ⊨ᶠ f₁ ⇔ f₃) (h' : ⊨ᶠ f₂ ⇔ f₄) : ⊨ᶠ (f₁ 𝐔 f₂) ⇔ (f₃ 𝐔 f₄) := by
  rw [sem_entail_fin_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_fin_release_congr (h : ⊨ᶠ f₁ ⇔ f₃) (h' : ⊨ᶠ f₂ ⇔ f₄) : ⊨ᶠ (f₁ 𝐑 f₂) ⇔ (f₃ 𝐑 f₄) := by
  rw [sem_entail_fin_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

/-!
### Infinite trace congruence lemmas
-/

theorem entail_inf_not_congr (h : ⊨ⁱ f₁ ⇔ f₂) : ⊨ⁱ f₁ᶜ ⇔ f₂ᶜ := by
  rw [sem_entail_inf_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_inf_sshift_congr (h : ⊨ⁱ f₁ ⇔ f₂) {n} : ⊨ⁱ 𝐗ˢ(n) f₁ ⇔ 𝐗ˢ(n) f₂ := by
  rw [sem_entail_inf_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_inf_wshift_congr (h : ⊨ⁱ f₁ ⇔ f₂) {n} : ⊨ⁱ 𝐗ʷ(n) f₁ ⇔ 𝐗ʷ(n) f₂ := by
  rw [sem_entail_inf_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_infally_congr (h : ⊨ⁱ f₁ ⇔ f₂) : ⊨ⁱ 𝐅 f₁ ⇔ 𝐅 f₂ := by
  rw [sem_entail_inf_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_inf_globally_congr (h : ⊨ⁱ f₁ ⇔ f₂) : ⊨ⁱ 𝐆 f₁ ⇔ 𝐆 f₂ := by
  rw [sem_entail_inf_iff_iff] at h
  simp +contextual [push_ltl, h]

theorem entail_inf_and_congr (h : ⊨ⁱ f₁ ⇔ f₃) (h' : ⊨ⁱ f₂ ⇔ f₄) : ⊨ⁱ (f₁ ⊓ f₂) ⇔ (f₃ ⊓ f₄) := by
  rw [sem_entail_inf_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_inf_or_congr (h : ⊨ⁱ f₁ ⇔ f₃) (h' : ⊨ⁱ f₂ ⇔ f₄) : ⊨ⁱ (f₁ ⊔ f₂) ⇔ (f₃ ⊔ f₄) := by
  rw [sem_entail_inf_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_inf_imp_congr (h : ⊨ⁱ f₁ ⇔ f₃) (h' : ⊨ⁱ f₂ ⇔ f₄) : ⊨ⁱ (f₁ ⇨ f₂) ⇔ (f₃ ⇨ f₄) := by
  rw [sem_entail_inf_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_inf_iff_congr (h : ⊨ⁱ f₁ ⇔ f₃) (h' : ⊨ⁱ f₂ ⇔ f₄) : ⊨ⁱ (f₁ ⇔ f₂) ⇔ (f₃ ⇔ f₄) := by
  rw [sem_entail_inf_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_inf_until_congr (h : ⊨ⁱ f₁ ⇔ f₃) (h' : ⊨ⁱ f₂ ⇔ f₄) : ⊨ⁱ (f₁ 𝐔 f₂) ⇔ (f₃ 𝐔 f₄) := by
  rw [sem_entail_inf_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

theorem entail_inf_release_congr (h : ⊨ⁱ f₁ ⇔ f₃) (h' : ⊨ⁱ f₂ ⇔ f₄) : ⊨ⁱ (f₁ 𝐑 f₂) ⇔ (f₃ 𝐑 f₄) := by
  rw [sem_entail_inf_iff_iff] at h h'
  simp +contextual [push_ltl, h, h']

/-!
### Conditional lemmas
-/

theorem not_anti (h : f₁ ⇒ f₂) : f₂ᶜ ⇒ f₁ᶜ := by
  intro t
  exact mt (h t)

theorem snext_mono (h : f₁ ⇒ f₂) : 𝐗ˢ f₁ ⇒ 𝐗ˢ f₂ := by
  simp +contextual only [sem_imp_iff, sat_imp_iff, sat_sshift_iff, Nat.cast_one,
    forall_exists_index, exists_true_left]
  intro _ _ h'
  exact h _ h'

theorem wnext_mono (h : f₁ ⇒ f₂) : 𝐗ʷ f₁ ⇒ 𝐗ʷ f₂ := by
  simp only [sem_imp_iff, sat_imp_iff, sat_wshift_iff, Nat.cast_one]
  intro _ h' h''
  exact h _ (h' h'')

theorem globally_mono (h : f₁ ⇒ f₂) : 𝐆 f₁ ⇒ 𝐆 f₂ := by
  simp only [sem_imp_iff, sat_imp_iff, sat_globally_iff, sat_wshift_iff]
  intro _ h'
  peel h'
  exact h _ this

theorem finally_mono (h : f₁ ⇒ f₂) : 𝐅 f₁ ⇒ 𝐅 f₂ := by
  rw [finally_eq_not_globally_not, finally_eq_not_globally_not]
  apply not_anti
  apply globally_mono
  apply not_anti h

theorem sat_globally_imp_of (h : t ⊨ 𝐆 (f₁ ⇨ f₂)) : t ⊨ 𝐆 f₁ ⇨ 𝐆 f₂ := by
  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff] at h ⊢
  intro h1 _ _
  apply h
  apply h1

theorem sat_finally_imp_finally_of (h : t ⊨ 𝐆 (f₁ ⇨ f₂)) : t ⊨ 𝐅 f₁ ⇨ 𝐅 f₂ := by
  simp only [sat_globally_iff, sat_wshift_iff, sat_imp_iff, sat_finally_iff, sat_sshift_iff,
    forall_exists_index] at h ⊢
  intro n hn h2
  refine ⟨_, _, h n hn h2⟩

theorem sat_finally_imp_of (h : t ⊨ 𝐅 f₁ ⇨ 𝐅 f₂) : t ⊨ 𝐅 (f₁ ⇨ f₂) := by
  simp only [sat_imp_iff, sat_finally_iff, sat_sshift_iff, forall_exists_index] at h ⊢
  by_cases h' : t ⊨ 𝐅 f₂
  · simp only [sat_finally_iff, sat_sshift_iff] at h'
    obtain ⟨n, hn, h'⟩ := h'
    use n, hn
    simp [h']
  · simp only [sat_finally_iff, sat_sshift_iff, not_exists] at h'
    specialize h 0
    simp only [CharP.cast_eq_zero, Trace.nempty, Trace.shift_zero, h', exists_false,
      imp_false, forall_const] at h
    use 0
    simp [h]

theorem sat_finally_imp_of_finally_imp (h : t ⊨ 𝐅 f₁ ⇨ 𝐆 f₂) : t ⊨ 𝐆 (f₁ ⇨ f₂) := by
  simp only [sat_imp_iff, sat_finally_iff, sat_sshift_iff, sat_globally_iff, sat_wshift_iff,
    forall_exists_index] at h ⊢
  intro n _ h'
  exact h n _ h' _ _

theorem sat_release_iff_globally_of_globally_not (h : t ⊨ 𝐆 f₁ᶜ) :
    (t ⊨ f₁ 𝐑 f₂) ↔ t ⊨ 𝐆 f₂ := by
  simp [push_ltl] at h ⊢
  constructor
  · intro h1 n hn
    simp +contextual [h] at h1
    apply h1
  · intro h2 n hn
    exact h2 n

-- TODO add "strong release"
theorem sat_release_iff_of_finally (h : t ⊨ 𝐅 f₁) :
    (t ⊨ f₁ 𝐑 f₂) ↔ ∃ n, (∀ i ≤ n, t ⊨ 𝐗ʷ(i) f₂) ∧ t ⊨ 𝐗ˢ(n) f₁ := by
  rw [sat_finally_iff] at h
  classical
  let n := Nat.find h
  have hn := Nat.find_spec h
  have hn' := fun m => Nat.find_min (H := h) (m := m)
  rw [sat_release_iff]
  constructor
  · intro hr
    refine ⟨n, ?_, hn⟩
    intro i hi
    apply hr
    intro i' hi'
    apply hn'
    exact lt_of_lt_of_le hi' hi
  · rintro ⟨n, h1, h2⟩
    intro i hi
    apply h1
    by_contra! h
    specialize hi n h
    exact absurd h2 hi

/--
`f₁ 𝐑 f₂` means that `f₂` has to be true until and including the point where `f₁` first becomes true;
if `f₁` never becomes true, `f₂` must remain true forever (description from Wikipedia).
-/
theorem sat_release_iff'' :
    (t ⊨ f₁ 𝐑 f₂) ↔ (t ⊨ 𝐆 f₂) ∨ ∃ n, (∀ i ≤ n, t ⊨ 𝐗ʷ(i) f₂) ∧ t ⊨ 𝐗ˢ(n) f₁ := by
  by_cases h : t ⊨ 𝐆 f₁ᶜ
  · rw [sat_release_iff_globally_of_globally_not h, iff_self_or]
    rintro ⟨n, h1, h2⟩
    simp only [push_ltl] at h
    specialize h n (lt_of_sat_sshift h2)
    rw [shift_sat_iff_sat_sshift] at h
    contradiction
  · rw [← sat_not_iff] at h
    simp only [push_not_ltl] at h
    rw [sat_release_iff_of_finally h, iff_or_self]
    revert h
    simp +contextual only [sat_globally_iff, sat_finally_iff, forall_true_iff, true_and]

/-!
### Temporal unfolding
-/

theorem until_eq_or_and :
    f₁ 𝐔 f₂ = f₂ ⊔ (f₁ ⊓ 𝐗ˢ (f₁ 𝐔 f₂)) := by
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
        rw [Trace.shift_unshift_succ] at h3
        have h1' := h1 0 (by simp) (by simp)
        rw [Trace.shift_zero] at h1'
        refine ⟨h1', n, ?_, (by simpa using h2), h3⟩
        intro i hi ht
        have := h1 (i + 1) (by omega) (by simp [ht])
        rw [Trace.shift_unshift_succ] at this
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
    f₁ 𝐑 f₂ = f₂ ⊓ (f₁ ⊔ 𝐗ʷ (f₁ 𝐑 f₂)) := by
  conv_lhs =>
    rw [release_eq_not_until_not, until_eq_or_and]
    simp only [push_not_ltl]

theorem release_eq_or_and :
    f₁ 𝐑 f₂ = (f₁ ⊓ f₂) ⊔ (f₂ ⊓ 𝐗ʷ (f₁ 𝐑 f₂)) := by
  conv_lhs => rw [release_eq_and_or]
  rw [inf_sup_left, inf_comm]

theorem finally_eq_or_finally : 𝐅 f = f ⊔ 𝐗ˢ (𝐅 f) := by
  conv_lhs =>
    rw [finally_eq, until_eq_or_and, ← finally_eq, top_inf_eq]

theorem globally_eq_and_globally : 𝐆 f = f ⊓ 𝐗ʷ (𝐆 f) := by
  conv_lhs =>
    rw [globally_eq, finally_eq_or_finally]
    simp [push_not_ltl]

theorem entail_globally_imp : ⊨ 𝐆 f ⇨ f := by
  rw [globally_eq_and_globally, inf_comm, ← himp_himp, himp_self, himp_top]
  exact sem_entail_true

theorem entail_of_globally (h : ⊨ 𝐆 f) : ⊨ f := by
  intro t
  exact entail_globally_imp t (h t)

private lemma eq_of_lt_sub_pred {n m k : ℕ} (hn : 0 < n) (hm : m < n - (n - 1))
    (hk : (k : ℕ∞) < (n : ℕ∞) - (n - 1 : ℕ)) : m = k := by
  rw [← ENat.natCast_sub] at hk
  norm_cast at hk
  omega

private lemma sub_one_add_eq_of_lt {n m k : ℕ} (hm : m < n) (hk : k < n) :
    n - k - 1 + k = n - m - 1 + m := by
  omega

private lemma sub_one_lt_sub_of_lt {n k : ℕ} (hk : k < n) : n - k - 1 < n - k := by
  omega

theorem globally_finally_iff_of_finite (h : t.Finite) : (t ⊨ 𝐆 𝐅 f) ↔ (t ⊨ 𝐅 𝐆 f) := by
  simp [push_ltl]
  obtain ⟨n, h1, h2⟩ := h.exists
  simp_rw [← h2]
  norm_cast
  constructor
  · intro h
    use n - 1, (by omega)
    intro m hm
    obtain ⟨k, hk, hf⟩ := h (n - 1) (by omega)
    convert hf
    exact eq_of_lt_sub_pred h1 hm hk
  · rintro ⟨m, hm, h2⟩ k hk
    use n - k - 1, (by
      rw [← ENat.natCast_sub]
      exact_mod_cast sub_one_lt_sub_of_lt hk)
    specialize h2 (n - m - 1) (sub_one_lt_sub_of_lt hm)
    convert h2 using 2
    exact sub_one_add_eq_of_lt hm hk

theorem entail_fin_globally_finally_comm : ⊨ᶠ 𝐆 𝐅 f ⇔ 𝐅 𝐆 f := by
  intro t
  rw [sat_iff_iff]
  exact globally_finally_iff_of_finite

theorem entail_fin_finally_globally_finally_iff : ⊨ᶠ 𝐅 𝐆 𝐅 f ⇔ 𝐆 𝐅 f := by
  intro t h
  rw [sat_iff_iff]
  rw [← globally_finally_iff_of_finite h, finally_finally, globally_finally_iff_of_finite h]

theorem entail_fin_globally_finally_idem : ⊨ᶠ 𝐆 𝐅 𝐆 𝐅 f ⇔ 𝐆 𝐅 f := by
  intro t h
  rw [sat_iff_iff]
  rw [globally_finally_iff_of_finite h, globally_globally,
    ← globally_finally_iff_of_finite h, finally_finally]

theorem entail_inf_snext_globally_finally_iff : ⊨ⁱ 𝐗ˢ 𝐆 𝐅 f ⇔ 𝐆 𝐅 f := by
  simp +contextual [push_ltl]
  intro t h
  constructor
  · intro h1 n
    obtain ⟨m, hm⟩ := h1 n
    use m + 1
    convert hm using 2
    omega
  · intro h2 n
    obtain ⟨m, hm⟩ := h2 (n + 1)
    use m

theorem entail_inf_wnext_finally_globally_iff : ⊨ⁱ 𝐗ʷ 𝐅 𝐆 f ⇔ 𝐅 𝐆 f := by
  simpa only [← not_globally, ← not_finally, ← not_wshift, compl_bihimp_compl]
    using entail_inf_snext_globally_finally_iff (f := fᶜ)

theorem finally_globally_finally_eq : 𝐅 𝐆 𝐅 f = 𝐆 𝐅 f := by
  ext t
  by_cases h : t.Finite
  · rw [← sat_iff_iff]
    exact entail_fin_finally_globally_finally_iff _ h
  · rw [Trace.not_finite] at h
    simp +contextual [push_ltl, h]
    constructor
    · rintro ⟨n, hn⟩ m
      obtain ⟨k, hk⟩ := hn m
      use n + k
      convert hk using 2
      omega
    · intro h2
      use 0
      simpa using h2

theorem globally_finally_idem : 𝐆 𝐅 𝐆 𝐅 f = 𝐆 𝐅 f := by
  rw [finally_globally_finally_eq, globally_globally]

theorem globally_finally_globally_eq : 𝐆 𝐅 𝐆 f = 𝐅 𝐆 f := by
  simpa only [← not_globally, ← not_finally, compl_inj_iff]
    using finally_globally_finally_eq (f := fᶜ)

theorem finally_globally_idem : 𝐅 𝐆 𝐅 𝐆 f = 𝐅 𝐆 f := by
  rw [globally_finally_globally_eq, finally_finally]

/-!
### More semantics lemmas
-/

lemma unshift_sat_globally_iff (s : σ) :
    (Trace.unshift s t ⊨ 𝐆 f) ↔ (Trace.unshift s t ⊨ f) ∧ (t ⊨ 𝐆 f) := by
  rw (occs := [1]) [globally_eq_and_globally]
  simp [push_ltl]

/--
Induction principle for proving `t ⊨ 𝐆 p`.
-/
theorem globally_induction {p : TraceSet σ} (t : Trace σ)
    (base : t ⊨ p) (step : t ⊨ 𝐆 (p ⇨ 𝐗ʷ p)) :
    t ⊨ 𝐆 p := by
  simp [push_ltl]
  intro n h_n
  induction n
  . simp; exact base
  . rename_i n ih
    simp [push_ltl] at step
    have h2 : n < t.length := by
      rw [ENat.natCast_add] at h_n
      simp at h_n
      refine (ENat.add_one_le_iff ?_).mp ?_
      exact ENat.natCast_ne_top n
      exact le_of_lt h_n
    specialize ih h2
    specialize step n h2 ih (lt_tsub_iff_left.mpr h_n)
    simpa only [add_comm] using step
