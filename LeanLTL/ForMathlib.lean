import Mathlib.Data.ENat.Basic

lemma enat_cancel (n m : ENat) (i : Nat) : n + i < m + i ↔ n < m := by
  refine ENat.add_lt_add_iff_right ?h
  exact ENat.coe_ne_top i

@[simp]
lemma enat_cancel' (n m : ENat) : n + 1 < m + 1 ↔ n < m := by
  refine ENat.add_lt_add_iff_right ?h
  exact ENat.coe_ne_top 1

lemma enat_leq_sub {n m : ENat} {a : ℕ} (h: n < m): (n - a: ENat) < m := by
  exact tsub_lt_of_lt h

lemma Option.get_inj_iff {α : Type*} {o o' : Option α} {h} {h'} :
    o.get h = o'.get h' ↔ o = o' := by
  cases o <;> cases o' <;> simp [Option.isSome] at h h' ⊢
