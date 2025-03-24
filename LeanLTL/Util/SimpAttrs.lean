import Lean.Meta.Tactic.Simp.Attr

/-!
# Simp attributes

- `push_ltl` is for converting LTL formulas into logic.
- `push_not_ltl` is for pushing negations into LTL formulae.
- `neg_norm_ltl` is for putting LTL into negation normal form.
-/

open Lean Meta

/--
Simp set for converting `t ⊨ f` LTL expressions into their semantic interpretation.
-/
initialize pushLTLExt : SimpExtension ←
  registerSimpAttr `push_ltl
    "lemmas for pushing out operators in LTL lemmas"

/--
Simp set for pushing `TraceSet.not` inwards in LTL expressions.
-/
initialize pushNotFLTLExt : SimpExtension ←
  registerSimpAttr `push_not_ltl
    "lemmas for pushing `not` inwards in LTL expressions"

/--
Simp set for putting LTL expressions into "negation normal form".
- Negations are pushed inward (like with `push_not_fltl`)
- Globally and finally are eliminated.
- The only remaining LTL operators are true, false, and, or, sshift, wshift, until, and release.

and declaring that `(TraceSet.false.sshift n).not` is in negation normal form.
-/
initialize negNormFLTLExt : SimpExtension ←
  registerSimpAttr `neg_norm_ltl
    "lemmas for putting LTL expressions into negation normal form"
