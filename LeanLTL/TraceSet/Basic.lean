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

@[push_fltl] lemma sat_true_iff : (t ⊨ TraceSet.true) ↔ True := by rfl
@[push_fltl] lemma sat_false_iff : (t ⊨ TraceSet.false) ↔ False := by rfl

@[push_fltl] lemma sat_not_iff : (t ⊨ f.not) ↔ ¬(t ⊨ f) := Iff.rfl
@[push_fltl] lemma sat_and_iff : (t ⊨ f₁.and f₂) ↔ (t ⊨ f₁) ∧ (t ⊨ f₂) := Iff.rfl
@[push_fltl] lemma sat_or_iff : (t ⊨ f₁.or f₂) ↔ (t ⊨ f₁) ∨ (t ⊨ f₂) := Iff.rfl
@[push_fltl] lemma sat_imp_iff : (t ⊨ f₁.imp f₂) ↔ ((t ⊨ f₁) → (t ⊨ f₂)) := Iff.rfl

@[push_fltl] lemma sat_wshift_iff (c : ℕ) :
    (t ⊨ f.wshift c) ↔ ∀ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_fltl] lemma sat_sshift_iff (c : ℕ) :
    (t ⊨ f.sshift c) ↔ ∃ h : c < t.length, t.shift c h ⊨ f := Iff.rfl

@[push_fltl] lemma sat_until_iff :
    (t ⊨ f₁.until f₂) ↔ ∃ n, (∀ i < n, t ⊨ f₁.wshift i) ∧ (t ⊨ f₂.sshift n) := Iff.rfl

@[push_fltl] theorem sat_finally_iff : (t ⊨ f.finally) ↔ ∃ n, t ⊨ f.sshift n := by
  simp [TraceSet.finally, push_fltl]

@[push_fltl] theorem sat_globally_iff : (t ⊨ f.globally) ↔ ∀ n, t ⊨ (f.wshift n) := by
  simp [TraceSet.globally, push_fltl]

@[push_fltl] theorem sem_imp_iff : (f₁ ⇒ f₂) ↔ ∀ (t : Trace σ), t ⊨ f₁.imp f₂ := by
  simp [TraceSet.sem_imp, push_fltl]

lemma lt_of_sat_sshift {n : ℕ} (h : t ⊨ f.sshift n) : n < t.length := by
  rw [sat_sshift_iff] at h
  exact h.1

lemma not_sat_sshift_of_le {n : ℕ} (h : t.length ≤ n) : ¬(t ⊨ f.sshift n) := by
  simp [push_fltl]
  intro h'
  have := lt_of_lt_of_le h' h
  simp at this

lemma sat_wshift_of_le {n : ℕ} (h : t.length ≤ n) : (t ⊨ f.wshift n) := by
  simp [push_fltl]
  intro h'
  have := lt_of_lt_of_le h' h
  simp at this

lemma singleton_sat_wshift {s : σ} (c : ℕ) :
    (Trace.singleton s ⊨ f.wshift c) ↔ 0 < c ∨ (c = 0 ∧ Trace.singleton s ⊨ f) := by
  obtain h | h := Nat.eq_zero_or_pos c <;> simp [push_fltl, h]
  intro
  omega

-- TODO: Dual lemmas for unshift everywhere shift is

@[simp] lemma unshift_sat_snext_iff (s : σ) : (Trace.unshift s t ⊨ f.snext) ↔ (t ⊨ f) := by
  simp [push_fltl]

@[simp] lemma unshift_sat_wnext_iff (s : σ) : (Trace.unshift s t ⊨ f.wnext) ↔ (t ⊨ f) := by
  simp [push_fltl]

/-!
### Adjunctions
-/

lemma shift_sat_iff_sat_sshift {n : ℕ} (h : n < t.length) : (t.shift n h ⊨ f) ↔ (t ⊨ f.sshift n) := by
  constructor <;> simp [push_fltl, h]

lemma shift_sat_iff_sat_wshift {n : ℕ} (h : n < t.length) : (t.shift n h ⊨ f) ↔ (t ⊨ f.wshift n) := by
  constructor <;> simp [push_fltl, h]

/-!
### Negation pushing
-/

@[simp] lemma not_not : f.not.not = f := by ext t; simp [push_fltl]

lemma not_sshift (n : ℕ) : (f.sshift n).not = f.not.wshift n := by ext t; simp [push_fltl]

lemma not_wshift (n : ℕ) : (f.wshift n).not = f.not.sshift n := by ext t; simp [push_fltl]

lemma not_finally : f.finally.not = f.not.globally := by ext t; simp [push_fltl]

lemma not_globally : f.globally.not = f.not.finally := by ext t; simp [push_fltl]

lemma not_and : (f₁.and f₂).not = f₁.not.or f₂.not := by ext t; simp [push_fltl, imp_iff_not_or]

lemma not_or : (f₁.or f₂).not = f₁.not.and f₂.not := by ext t; simp [push_fltl]

lemma not_inj_iff : f₁.not = f₂.not ↔ f₁ = f₂ := by
  constructor
  · intro h
    ext t
    simpa [push_fltl, not_iff_not] using congr(t ⊨ $h)
  · simp +contextual

/-!
### General lemmas
-/

@[simp] lemma sshift_zero : f.sshift 0 = f := by ext t; simp [push_fltl]

@[simp] lemma wshift_zero : f.wshift 0 = f := by ext t; simp [push_fltl]

lemma sat_wshift_of_sat_sshift (c : ℕ) (h : t ⊨ f.sshift c) : t ⊨ f.wshift c := by
  rw [sat_wshift_iff]
  intro
  rw [sat_sshift_iff] at h
  obtain ⟨_, hs⟩ := h
  exact hs

@[simp] lemma sshift_sshift (n₁ n₂ : ℕ) : (f.sshift n₁).sshift n₂ = f.sshift (n₁ + n₂) := by
  ext t
  simp only [push_fltl]
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
  simp only [push_fltl]
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

@[simp] lemma true_and : TraceSet.true.and f = f := by ext t; simp [push_fltl]

@[simp] lemma and_true : f.and TraceSet.true = f := by ext t; simp [push_fltl]

lemma sshift_until (n : ℕ) : (f₁.until f₂).sshift n = (f₁.sshift n).until (f₂.sshift n) := by
  ext t
  simp [push_fltl]
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

@[simp] theorem finally_finally : f.finally.finally = f.finally := by
  ext t; simp [TraceSet.finally]

@[simp] theorem globally_globally : f.globally.globally = f.globally := by
  simp [TraceSet.globally]


/-!
### Distributivity
-/

lemma wshift_and_distrib (n : ℕ) :
    (f₁.and f₂).wshift n = (f₁.wshift n).and (f₂.wshift n) := by
  ext t; simp [push_fltl, forall_and]

lemma wshift_or_distrib (n : ℕ) :
    (f₁.or f₂).wshift n = (f₁.wshift n).or (f₂.wshift n) := by
  ext t; by_cases n < t.length <;> simp [push_fltl, *]

lemma sshift_and_distrib (n : ℕ) :
    (f₁.and f₂).sshift n = (f₁.sshift n).and (f₂.sshift n) := by
  ext t; by_cases n < t.length <;> simp [push_fltl, *]

lemma sshift_or_distrib (n : ℕ) :
    (f₁.or f₂).sshift n = (f₁.sshift n).or (f₂.sshift n) := by
  ext t; by_cases n < t.length <;> simp [push_fltl, *]

lemma until_or_distrib (f₁ f₂ f₃: TraceSet σ) :
    f₁.until (f₂.or f₃) = (f₁.until f₂).or (f₁.until f₃) := by
  ext t; simp only [push_fltl, exists_or, ← exists_or, ← and_or_left]

lemma and_until_distrib (f₁ f₂ f₃: TraceSet σ) :
    (f₁.and f₂).until f₃ = (f₁.until f₃).and (f₂.until f₃) := by
  ext t
  simp only [push_fltl]
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

lemma finally_or_distrib (f₁ f₂ : TraceSet σ) : (f₁.or f₂).finally = f₁.finally.or f₂.finally := by
  ext t; simp [push_fltl, exists_or]

lemma globally_and_distrib (f₁ f₂ : TraceSet σ) : (f₁.and f₂).globally = f₁.globally.and f₂.globally := by
  ext t; simp [push_fltl, forall_and]

/-!
### Temporal unfolding
-/

theorem until_eq_or_and :
    f₁.until f₂ = f₂.or (f₁.and (f₁.until f₂).snext) := by
  ext t
  cases t using Trace.unshift_cases with
  | singleton =>
    simp [push_fltl]
    constructor
    · rintro ⟨_, _, rfl, h⟩
      exact h
    · intro h
      use 0
      simp [h]
  | unshift s t =>
    simp [push_fltl]
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

theorem finally_eq_or_finally : f.finally = f.or f.finally.snext := by
  conv =>
    enter [1]
    rw [TraceSet.finally, until_eq_or_and, ← TraceSet.finally, TraceSet.true_and]

theorem globally_eq_and_globally : f.globally = f.and f.globally.wnext := by
  conv =>
    enter [1]
    rw [TraceSet.globally, finally_eq_or_finally]
    simp [TraceSet.not_or, TraceSet.not_sshift, TraceSet.not_finally]

/-!
### More semantics lemmas
-/

lemma unshift_sat_globally_iff (s : σ) :
    (Trace.unshift s t ⊨ TraceSet.globally f) ↔ (Trace.unshift s t ⊨ f) ∧ (t ⊨ TraceSet.globally f) := by
  rw (occs := [1]) [globally_eq_and_globally]
  simp [push_fltl]

/--
Induction principle for proving `t ⊨ .globally p`.
-/
theorem globally_induction {p : TraceSet σ} (t : Trace σ)
    (base : t ⊨ p) (step : t ⊨ .globally (p.imp p.wnext)) :
    t ⊨ .globally p := by
  simp [push_fltl]
  intro n h_n
  induction n
  . simp; exact base
  . rename_i n ih
    simp [push_fltl] at step
    have h2 : n < t.length := by
      rw [ENat.coe_add] at h_n
      simp at h_n
      refine (ENat.add_one_le_iff ?_).mp ?_
      exact ENat.coe_ne_top n
      exact le_of_lt h_n
    specialize ih h2
    specialize step n h2 ih (lt_tsub_iff_left.mpr h_n)
    simpa only [add_comm] using step

/-!
### Theorems about `TraceSet.toFun`
-/

@[simp] lemma toFun_defined (s : TraceSet σ) (t : Trace σ) : (s.toFun t).isSome := rfl

@[simp] lemma toTraceSet_toFun (f : TraceSet σ) (c : Prop) : f.toFun.toTraceSet c = f := rfl

-- TODO should `toFun` be pushed inward or pushed outward?
lemma map_toFun (f : TraceSet σ) (g : Prop → Prop) : f.toFun.map g = (f.map g).toFun := rfl

lemma map₂_toFun (f f' : TraceSet σ) (g : Prop → Prop → Prop) :
    TraceFun.map₂ g f.toFun f'.toFun = (TraceSet.map₂ g f f').toFun := rfl

-- lemma toTraceSet_shift_toFun (f : TraceSet σ) (i : ℕ) :
--     (f.toFun.shift i).toTraceSetTrue = f.wshift i := by
--   ext
--   simp
