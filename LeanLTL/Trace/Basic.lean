import LeanLTL.Trace.Defs
import Mathlib

/-!
# Basic theory about traces
-/

namespace LeanLTL

namespace Trace
variable {σ σ' σ'' α α' β β': Type*}

@[simp] lemma one_lt_succ_length (t : Trace α) : 1 < t.length + 1 := by
  nth_rewrite 1 [← zero_add 1]
  rw [enat_cancel']
  apply t.nempty

lemma toFun_eq {t : Trace σ} (i : ℕ) (h : i < t.length) :
    t.toFun i h = (t.toFun? i).get ((t.defined i).mp h) := rfl

/-- Put `toFun?` into simp normal form. -/
@[simp] lemma get_toFun?_eq {t : Trace σ} {i : ℕ} {h} :
    (t.toFun? i).get h = t.toFun i (by rwa [t.defined]) := rfl

/-- We can put `t.toFun? 0` into `toFun` form as well. -/
@[simp] lemma toFun?_zero_eq {t : Trace σ} : t.toFun? 0 = some (t.toFun 0) := by
  rw [Trace.toFun, Option.some_get]

theorem isSome_toFun_zero (t : Trace σ) : (t.toFun? 0).isSome := by simp

@[simp] lemma isSome_toFun?_iff (t : Trace σ) (i : Nat) : (t.toFun? i).isSome ↔ i < t.length :=
  (t.defined i).symm

@[ext] protected lemma ext {t t' : Trace σ}
    (hLen : t.length = t'.length)
    (hToFun : ∀ i h h', t.toFun i h = t'.toFun i h') :
    t = t' := by
  simp_rw [toFun_eq, Option.get_inj_iff] at hToFun
  obtain ⟨toFun?, len, _, defined⟩ := t
  obtain ⟨toFun?', _, _, defined'⟩ := t'
  cases hLen
  simp only [mk.injEq, and_true]
  ext1 i
  by_cases hi : i < len
  · exact hToFun _ hi hi
  · have := And.intro (defined i) (defined' i)
    simp [hi] at this
    simp [this]

@[simp] lemma singleton_length (s : σ) : (Trace.singleton s).length = 1 := rfl

@[simp] theorem shift_length (t : Trace σ) (n : ℕ) (h : n < t.length) :
    (t.shift n h).length = t.length - n := by rfl

@[simp] lemma unshift_length (s : σ) (t : Trace σ) : (Trace.unshift s t).length = t.length + 1 := rfl

lemma one_lt_unshift_length (s : σ) (t : Trace σ) : 1 < (Trace.unshift s t).length := by
  rw [unshift_length]
  have := t.nempty
  revert this
  cases t.length
  · intro; apply ENat.coe_lt_top
  · norm_cast; simp

lemma singleton_toFun_zero_eq (s : σ) : (Trace.singleton s).toFun 0 = s := rfl

@[simp] lemma singleton_toFun_eq {s : σ} {n} {h} : (Trace.singleton s).toFun n h = s := by
  simp only [singleton_length, Nat.cast_lt_one] at h
  cases h
  apply singleton_toFun_zero_eq

@[simp] lemma singleton_toFun?_succ_eq (s : σ) (i : ℕ) : (Trace.singleton s).toFun? (i + 1) = none := rfl

lemma length_eq_one_iff_eq_singleton (t : Trace σ) :
    t.length = 1 ↔ t = Trace.singleton (t.toFun 0) := by
  rw [Trace.ext_iff]
  simp +contextual

lemma exists_singleton (t : Trace σ) (h : t.length = 1) :
    ∃ (s : σ), t = Trace.singleton s := by
  rw [length_eq_one_iff_eq_singleton] at h
  exact ⟨_, h⟩

lemma exists_unshift (t : Trace σ) (h1 : 1 < t.length) :
    ∃ (s : σ) (t' : Trace σ), t = Trace.unshift s t' := by
  use t.toFun 0
  use t.shift 1 h1
  ext i
  · revert h1
    simp only [unshift_length, shift_length, Nat.cast_one]
    cases t.length
    · simp
    · norm_cast
      omega
  · cases i <;> rfl

@[simp] lemma shift_zero (t : Trace σ) : t.shift 0 t.nempty = t := by simp [Trace.shift]

@[simp] lemma shift_singleton_eq (s : σ) (i : ℕ) (h : i < (Trace.singleton s).length) :
    (Trace.singleton s).shift i h = Trace.singleton s := by
  simp only [singleton_length, Nat.cast_lt_one] at h
  cases h
  simp

@[simp] lemma shift_unshift_succ (s : σ) (t : Trace σ) {n : ℕ} (h : (n + 1 : ℕ) < (Trace.unshift s t).length) :
    (Trace.unshift s t).shift (n + 1) h = t.shift n (by simpa using h) := by
  ext
  · revert h
    simp
    cases t.length
    · simp; change ¬ (n + 1 : ℕ) = (⊤ : ℕ∞); apply ENat.coe_ne_top
    · norm_cast; omega
  · rfl

lemma shift_unshift_one (s : σ) (t : Trace σ) :
    (Trace.unshift s t).shift 1 (one_lt_unshift_length _ _) = t := by simp

@[simp] lemma not_finite {t : Trace σ} : ¬ t.Finite ↔ t.Infinite := by
  unfold Trace.Finite Trace.Infinite
  simp only [not_lt, top_le_iff]

@[simp] lemma not_infinite {t : Trace σ} : ¬ t.Infinite ↔ t.Finite := by
  rw [← not_finite, not_not]

@[simp] lemma singleton_finite (s : σ) : (Trace.singleton s).Finite :=
  ENat.coe_lt_top _

@[simp] lemma infinite_shift_iff (t : Trace σ) {i} {h} : (Trace.shift t i h).Infinite ↔ t.Infinite := by
  simp [Trace.Infinite]

@[simp] lemma infinite_unshift_iff (s : σ) (t : Trace σ) : (Trace.unshift s t).Infinite ↔ t.Infinite := by
  simp [Trace.Infinite]
  cases t.length
  · simp
  · norm_cast; simp only [ENat.coe_ne_top]

@[simp] lemma finite_shift_iff (t : Trace σ) {i} {h} : (Trace.shift t i h).Finite ↔ t.Finite := by
  rw [← not_infinite, infinite_shift_iff, not_infinite]

@[simp] lemma finite_unshift_iff (s : σ) (t : Trace σ) : (Trace.unshift s t).Finite ↔ t.Finite := by
  rw [← not_infinite, infinite_unshift_iff, not_infinite]

@[simp] lemma length_eq_of_infinite {t : Trace σ} (h : t.Infinite) : t.length = ⊤ := by
  rwa [Trace.Infinite] at h

lemma coe_lt_length_of_infinite {t : Trace σ} (h : t.Infinite) (n : Nat) : n < t.length := by
  simp [h]

@[elab_as_elim]
theorem unshift_induction {p : (t : Trace σ) → t.Finite → Prop}
    (h1 : ∀ s : σ, p (Trace.singleton s) (by simp))
    (hind : ∀ (s : σ) (t : Trace σ) (hfin : t.Finite),
      p t hfin → p (t.unshift s) ((finite_unshift_iff s t).mpr hfin))
    (t : Trace σ) (hfin : t.Finite) : p t hfin := by
  generalize h1: t.length = k
  induction k
  . simp only [Trace.Finite] at hfin
    rw [h1] at hfin
    simp at hfin
  . rename_i k
    have h2 : k ≥ 1 := by
      have := t.nempty
      simp_all only [Nat.cast_pos, ge_iff_le]
      linarith
    induction k, h2 using Nat.le_induction generalizing t
    . simp_all only [Nat.cast_one]
      have h2 := exists_singleton t h1
      obtain ⟨s, h2⟩ := h2
      simp_all
    . rename_i h2 i h3 ih
      simp_all only [Nat.cast_add, Nat.cast_one]
      norm_cast at *
      simp_all only [add_right_eq_self, one_ne_zero, IsEmpty.forall_iff, Nat.cast_add, Nat.cast_one]
      have h4 := exists_unshift t (by rw [h1]; norm_cast; linarith)
      obtain ⟨s, t', h4⟩ := h4
      subst t
      apply hind
      refine ih t' ((finite_unshift_iff s t').mp hfin) ?_
      . simp_all only [unshift_length]
        cases h5:  t'.length
        . simp_all [Trace.Finite]
        . simp_all only [Nat.cast_inj]
          norm_cast at *
          omega

@[elab_as_elim]
theorem unshift_cases {p : (t : Trace σ) → Prop}
    (singleton : ∀ s : σ, p (Trace.singleton s))
    (unshift : ∀ (s : σ) (t : Trace σ), p (t.unshift s))
    (t : Trace σ) : p t := by
  generalize hl : t.length = n
  cases n with
  | top =>
    obtain ⟨_, _, rfl⟩ := exists_unshift t (by simp [hl])
    apply unshift
  | coe n =>
    obtain _ | _ | n := n
    · have := t.nempty
      simp [hl] at this
    · simp only [zero_add, Nat.cast_one] at hl
      obtain ⟨_, rfl⟩ := exists_singleton t hl
      apply singleton
    · obtain ⟨_, _, rfl⟩ := exists_unshift t (by rw [hl]; norm_cast; omega)
      apply unshift

private lemma shift_shift_aux {t : Trace σ} {m n : ℕ}
    (h₁ : m < t.length) (h₂ : n < (t.shift m h₁).length) : ↑(n + m) < t.length := by
  rw [shift_length] at h₂
  generalize t.length = k at *
  induction k
  . simp only [ENat.coe_lt_top]
  . norm_cast at *
    omega

lemma toFun_shift (t : Trace σ) (i j : ℕ) (h) (h') :
    (t.shift i h).toFun j h' = t.toFun (j + i) (shift_shift_aux h h') := rfl -- (!)

@[simp]
theorem shift_shift (t : Trace σ) (m n : ℕ)
    (h₁ : m < t.length) (h₂ : n < (t.shift m h₁).length) :
    ((t.shift m h₁).shift n h₂) = t.shift (n + m) (shift_shift_aux h₁ h₂) := by
  ext i
  . simp
    cases t.length
    · norm_cast
    · norm_cast; omega
  . simp [toFun_shift]
    congr! 1
    ring

end Trace
