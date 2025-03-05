import LeanLTL

-- TODO: Some sort of element, possible optional, that makes this more interesting and undecidable? Right now this could be solved
--       by LTL MT
-- TODO: Support naturals/integers instead of rationals
-- TODO: Rewrite this, maybe using quantifiers, to be more compact/support more lights?
-- TODO: Use quantifiers over max_arrives, max_departs, to make problem more interesting?
--         (e.g. prove we can avoid starvation if max_departs > max_arrives and there's always eventually a break in traffic)
--       Or is there a better way to represent constant values in state across formulas? We could do it by declaring a signal that never changes,
--       but maybe we can add a shorthand?

-- Traffic Light Example
structure ExState where
  TL1Red: Prop
  TL1Green: Prop
  TL2Red: Prop
  TL2Green: Prop
  TL1Arrives : ℚ
  TL1Departs : ℚ
  TL2Arrives : ℚ
  TL2Departs : ℚ
  TL1Queue : ℚ
  TL2Queue : ℚ

abbrev TL1Green := LeanLTL.TraceFun.of ExState.TL1Green
abbrev TL1Red := LeanLTL.TraceFun.of ExState.TL1Red
abbrev TL2Green := LeanLTL.TraceFun.of ExState.TL2Green
abbrev TL2Red := LeanLTL.TraceFun.of ExState.TL2Red
abbrev TL1Arrives := LeanLTL.TraceFun.of ExState.TL1Arrives
abbrev TL1Departs := LeanLTL.TraceFun.of ExState.TL1Departs
abbrev TL2Arrives := LeanLTL.TraceFun.of ExState.TL2Arrives
abbrev TL2Departs := LeanLTL.TraceFun.of ExState.TL2Departs
abbrev TL1Queue := LeanLTL.TraceFun.of ExState.TL1Queue
abbrev TL2Queue := LeanLTL.TraceFun.of ExState.TL2Queue

abbrev max_arrives : LeanLTL.TraceFun ExState ℚ := LLTL[1]
abbrev max_departs : LeanLTL.TraceFun ExState ℚ := LLTL[1]
-- abbrev TL_Queues : {q | q=TL1_Q ∨ q=TL2_Q}

-- Base Properties
abbrev TL1GreenRedIff  := LLTL[G (TL1Green ↔ (¬TL1Red))]
abbrev TL2GreenRedIff  := LLTL[G (TL2Green ↔ (¬TL2Red))]

abbrev TL1GreenNext     := LLTL[G ((TL1Green ∧ TL1Queue == 0) → (X (TL1Red ∧ TL2Green)))]
abbrev TL2GreenNext     := LLTL[G ((TL2Green ∧ TL2Queue == 0) → (X (TL2Red ∧ TL1Green)))]

abbrev TL1GreenDeparts  := LLTL[G (TL1Green → (TL1Departs == max_departs))]
abbrev TL1RedDeparts    := LLTL[G (TL1Red → (TL1Departs == 0))]
abbrev TL2GreenDeparts  := LLTL[G (TL2Green → (TL2Departs == max_departs))]
abbrev TL2RedDeparts    := LLTL[G (TL2Red → (TL2Departs == 0))]

abbrev TL1ArrivesBounds := LLTL[G (0 ≤ TL1Arrives ∧ TL1Arrives ≤ max_arrives)]
abbrev TL2ArrivesBounds := LLTL[G (0 ≤ TL2Arrives ∧ TL2Arrives ≤ max_arrives)]

abbrev TL1QueueNext     := LLTL[G ((X TL1Queue) == TL1Queue + TL1Arrives - TL1Departs)]
abbrev TL2QueueNext     := LLTL[G ((X TL2Queue) == TL2Queue + TL2Arrives - TL2Departs)]

abbrev TLBaseProperties :=  TL1GreenRedIff ∧ TL2GreenRedIff ∧ TL1GreenNext ∧ TL2GreenNext
                            ∧ TL1GreenDeparts ∧ TL1RedDeparts ∧ TL2GreenDeparts ∧ TL2RedDeparts
                            ∧ TL1ArrivesBounds ∧ TL2ArrivesBounds ∧ TL1QueueNext ∧ TL2QueueNext


-- Optional Properties
abbrev ArrivesLtDeparts   := LLTL[(max_arrives < max_departs)]
abbrev ArrivesLeDeparts   := LLTL[(max_arrives ≤  max_departs)]
abbrev TrafficLulls       := LLTL[(G (F (TL1Arrives == 0))) ∧ (G (F (TL2Arrives == 0)))]


-- Goal Properties
abbrev LightSafety        := LLTL[G ((TL1Green → ¬TL2Green) ∧ (TL2Green → ¬TL1Green))]
abbrev NeverStarvation    := LLTL[(G (F (TL1Queue == 0))) ∧ (G (F (TL2Queue == 0)))]


-- Example Proofs
theorem SatisfiesLightSafety : TLBaseProperties ⇒ LightSafety := sorry

theorem NeverStarvationCase1 : LLTL[ArrivesLtDeparts ∧ TLBaseProperties] ⇒ NeverStarvation := sorry

theorem NeverStarvationCase2 : LLTL[ArrivesLeDeparts ∧ TrafficLulls ∧ TLBaseProperties] ⇒ NeverStarvation := sorry
