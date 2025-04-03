import Mathlib.Tactic.Common
/-!
# Notation classes for LTL operations
-/

namespace LeanLTL

class HasFinally (α : Type*) where
  «finally» : α → α

class HasGlobally (α : Type*) where
  globally : α → α

class HasUntil (α : Type*) where
  «until» : α → α → α

class HasRelease (α : Type*) where
  release : α → α → α

class Shift (α : Type*) where
  shift : ℕ → α → α

class SShift (α : Type*) where
  sshift : ℕ → α → α

class WShift (α : Type*) where
  wshift : ℕ → α → α

/-- `𝐅 f` is *finally*.
True if some strong shift is true. -/
scoped prefix:max "𝐅 " => HasFinally.finally

/-- `𝐆 f` is *globally*.
True if every weak shift is true. -/
scoped prefix:max "𝐆 " => HasGlobally.globally

/--
`f 𝐔 g` is *until*.
True if there is a point at which a strong shift makes `g` true,
and all shifts of `f` until that point are true.
That is, "there is a point where `g` is strongly true, before which `f` is always weakly true".
-/
scoped infix:70 " 𝐔 " => HasUntil.until

/--
`f 𝐑 g` is *release*.
True if at every point, if every strong shift to before that point makes `f` false,
then the weak shift to the point makes `g` true.
That is, "`g` is weakly true at the first point `f` is strongly true".
-/
scoped infix:70 " 𝐑 " => HasRelease.release

/--
`𝐗ˢ(i) p` is the *strong shift* by `i` units of time.
Requires that the shifted trace is nonempty.
`𝐗ˢ p` is short for `𝐗ˢ(1) p`.
-/
scoped syntax:max "𝐗ˢ(" term ") " term:max : term
/-- `𝐗ˢ f` is *strong next*. Short for `𝐗ˢ(1) p`. -/
scoped syntax:max "𝐗ˢ " term:max : term
/--
`𝐗ʷ(i) p` is the *weak shift* by `i` units of time.
If the shifted trace is empty, evaluates to true.
`𝐗ʷ p` is short for `𝐗ʷ(1) p`.
-/
scoped syntax:max "𝐗ʷ(" term ") " term:max : term
/-- `𝐗ʷ f` is *weak next*. Short for `𝐗ʷ(1) p`. -/
scoped syntax:max "𝐗ʷ " term:max : term
/--
`𝐗(i) f` is the *shift* by `i` units of time.
Undefined if the shifted trace is empty.
`𝐗 f` is short for `𝐗(1) f`.
-/
scoped syntax:max "𝐗(" term ") " term:max : term
/-- `𝐗 f` is *next*. Short for `𝐗(1) f`. -/
scoped syntax:max "𝐗 " term:max : term

macro_rules | `(𝐗ˢ($i) $t) => `(SShift.sshift $i $t)
macro_rules | `(𝐗ʷ($i) $t) => `(WShift.wshift $i $t)
macro_rules | `(𝐗($i) $t) => `(Shift.shift $i $t)
macro_rules | `(𝐗ˢ $t) => `(SShift.sshift 1 $t)
macro_rules | `(𝐗ʷ $t) => `(WShift.wshift 1 $t)
macro_rules | `(𝐗 $t) => `(Shift.shift 1 $t)

@[scoped app_unexpander SShift.sshift]
def unexpand_sshift : Lean.PrettyPrinter.Unexpander
  | `($_ 1 $t) => `(𝐗ˢ $t)
  | `($_ $n $t) => `(𝐗ˢ($n) $t)
  | _ => throw ()
@[scoped app_unexpander WShift.wshift]
def unexpand_wshift : Lean.PrettyPrinter.Unexpander
  | `($_ 1 $t) => `(𝐗ʷ $t)
  | `($_ $n $t) => `(𝐗ʷ($n) $t)
  | _ => throw ()
@[scoped app_unexpander Shift.shift]
def unexpand_shift : Lean.PrettyPrinter.Unexpander
  | `($_ 1 $t) => `(𝐗 $t)
  | `($_ $n $t) => `(𝐗($n) $t)
  | _ => throw ()

end LeanLTL
