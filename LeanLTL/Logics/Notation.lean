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

end LeanLTL
