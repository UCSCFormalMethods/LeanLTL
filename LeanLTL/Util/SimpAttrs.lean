import Lean.Meta.Tactic.Simp.Attr

/-!
# Simp attributes

`push_ltl` and `push_fltl` are for converting LTL formulas into logic.
-/

open Lean Meta

initialize pushLTLExt : SimpExtension ←
  registerSimpAttr `push_ltl
    "lemmas for pushing out operators in LTL lemmas"

initialize pushFLTLExt : SimpExtension ←
  registerSimpAttr `push_fltl
    "lemmas for pushing out operators in LTL lemmas"


-- open Lean.Parser
-- syntax (name := push_ltl) "push_ltl" (Tactic.simpPre <|> Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (ppSpace prio)? : attr
