import Mathlib.Data.ENat.Basic

lemma enat_cancel (n m : ENat) (i : Nat) : n + i < m + i ↔ n < m := by
  refine ENat.add_lt_add_iff_right ?h
  exact ENat.coe_ne_top i

@[simp]
lemma enat_cancel' (n m : ENat) : n + 1 < m + 1 ↔ n < m := by
  refine ENat.add_lt_add_iff_right ?h
  exact ENat.coe_ne_top 1

@[simp] lemma ENat.one_lt_top : (1 : ℕ∞) < ⊤ := by
  rw [← Nat.cast_one]
  apply ENat.coe_lt_top

lemma enat_leq_sub {n m : ENat} {a : ℕ} (h: n < m): (n - a: ENat) < m := by
  exact tsub_lt_of_lt h

lemma Option.get_inj_iff {α : Type*} {o o' : Option α} {h} {h'} :
    o.get h = o'.get h' ↔ o = o' := by
  cases o <;> cases o' <;> simp [Option.isSome] at h h' ⊢

theorem Option.bind_some_eq_map {α β : Type*} (x? : Option α) (f : α → β) :
    (x?.bind fun x => some (f x)) = x?.map f := by
  cases x? <;> rfl

theorem Option.bind_map' {α β γ : Type*} {f : α → β} {g : β → Option γ} {x : Option α} :
    (x.map f).bind g = x.bind (fun v => g (f v)) := Option.bind_map

theorem Option.bind_map_assoc {α β γ : Type*} (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl
