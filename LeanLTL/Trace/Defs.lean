import LeanLTL.Init
import LeanLTL.ForMathlib
import Mathlib.Data.ENat.Lattice

/-!
# `Trace` and basic definitions
-/

namespace LeanLTL

/--
A trace over `σ` is a nonempty sequence (either finite or infinite)
of *states* from `σ`.
-/
structure Trace (σ : Type*) where
  toFun? : ℕ → Option σ
  length : ℕ∞
  nempty : 0 < length
  defined : ∀ i : ℕ, i < length ↔ (toFun? i).isSome

namespace Trace
variable {σ σ' σ'' α α' β β': Type*}

attribute [simp] Trace.nempty

/-- Get the `n`th state, with a proof that `n` is in bounds. -/
protected def toFun (t : Trace σ) (n : ℕ) (h : n < t.length := by simp [Trace.nempty]) : σ :=
  (t.toFun? n).get ((t.defined n).mp h)

/-- Get the `n`th state, assuming that `n` is in bounds. -/
protected def toFun! [Inhabited σ] (t : Trace σ) (n : ℕ) : σ :=
  (t.toFun? n).get!

protected def inhabited (t : Trace σ) : Inhabited σ := ⟨t.toFun 0⟩

/-- Transforms the states of a trace. -/
protected def map (f : σ → σ') (t : Trace σ) : Trace σ' where
  toFun? := fun n => (t.toFun? n).map f
  length := t.length
  nempty := t.nempty
  defined := by simpa only [Option.isSome_map'] using t.defined

/-- A one-state trace. -/
protected def singleton (s : σ) : Trace σ where
  toFun?
    | 0   => s
    | n+1 => none
  length := 1
  nempty := by simp
  defined := by rintro (_|i) <;> simp

/-- Drops the first `i` states from a trace. -/
protected def shift (t : Trace σ) (i : ℕ) (h : i < t.length) : Trace σ where
  toFun? := fun n => t.toFun? (n + i)
  length := t.length - i
  nempty := by simp_all
  defined := by
    intro n
    calc
      n < t.length - i ↔ n + i < t.length := by exact lt_tsub_iff_right
      _ ↔ (t.toFun? (n + i)).isSome       := t.defined (n + i)

/-- Inserts a state to the front of a trace. -/
protected def unshift (s : σ) (t : Trace σ) : Trace σ where
  toFun?
    | 0   => s
    | n+1 => t.toFun? n
  length := t.length + 1
  nempty := by simp
  defined := by rintro (_|i) <;> simp [t.defined]

/-- Predicate that the trace is finite in length. -/
protected def Finite (t : Trace α) : Prop := t.length < ⊤

/-- Predicate that the trace is infinite in length. -/
protected def Infinite (t : Trace α) : Prop := t.length = ⊤

instance [Nonempty σ] : Nonempty (Trace σ) :=
  ⟨Trace.singleton (Classical.arbitrary σ)⟩

end Trace
