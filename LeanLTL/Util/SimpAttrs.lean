import Lean.Meta.Tactic.Simp.Attr

/-!
# Simp attributes

`push_ltl` and `push_fltl` are for converting LTL formulas into logic.
-/

open Lean Meta

initialize pushLTLExt : SimpExtension ←
  registerSimpAttr `push_ltl
    "lemmas for pushing out operators in LTL lemmas"

/--
Simp set for converting `t ⊨ f` LTL expressions into their semantic interpretation.
-/
initialize pushFLTLExt : SimpExtension ←
  registerSimpAttr `push_fltl
    "lemmas for pushing out operators in LTL lemmas"

/--
Simp set for pushing `TraceSet.not` inwards in LTL expressions.
-/
initialize pushNotFLTLExt : SimpExtension ←
  registerSimpAttr `push_not_fltl
    "lemmas for pushing `not` inwards in LTL expressions"

/--
Simp set for putting LTL expressions into "negation normal form".
- Negations are pushed inward (like with `push_not_fltl`)
- Globally and finally are eliminated.
- The only remaining LTL operators are true, false, and, or, sshift, wshift, until, and release.

TODO: in a tactic we could eliminate wshift as well, using
```
f.wshift n = (f.sshift n).or (TraceSet.false.sshift n).not
```
and declaring that `(TraceSet.false.sshift n).not` is in negation normal form.
-/
initialize negNormFLTLExt : SimpExtension ←
  registerSimpAttr `neg_norm_fltl
    "lemmas for putting LTL expressions into negation normal form"

-- open Lean.Parser
-- syntax (name := push_ltl) "push_ltl" (Tactic.simpPre <|> Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (ppSpace prio)? : attr
