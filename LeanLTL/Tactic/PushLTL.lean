import LeanLTL.Util.SimpAttrs

macro "push_ltl" : tactic =>
  `(tactic| simp +contextual only [push_ltl])
