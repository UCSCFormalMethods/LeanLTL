import LeanLTL
open scoped LeanLTL.Notation
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
  TL1Green: Prop
  TL2Green: Prop

  TL1Arrives : ℕ
  TL1Departs : ℕ
  TL2Arrives : ℕ
  TL2Departs : ℕ
  TL1Queue : ℕ
  TL2Queue : ℕ

abbrev TL1Green := LeanLTL.TraceSet.of ExState.TL1Green
abbrev TL2Green := LeanLTL.TraceSet.of ExState.TL2Green
abbrev TL1Arrives := LeanLTL.TraceFun.of ExState.TL1Arrives
abbrev TL1Departs := LeanLTL.TraceFun.of ExState.TL1Departs
abbrev TL2Arrives := LeanLTL.TraceFun.of ExState.TL2Arrives
abbrev TL2Departs := LeanLTL.TraceFun.of ExState.TL2Departs
abbrev TL1Queue := LeanLTL.TraceFun.of ExState.TL1Queue
abbrev TL2Queue := LeanLTL.TraceFun.of ExState.TL2Queue

abbrev max_arrives : ℕ := 2
abbrev max_departs : ℕ := 2

-- Base Properties
-- TODO: Get rid of red prop
abbrev TL1StartGreen    := LLTL[TL1Green]
abbrev TL2StartRed      := LLTL[¬TL2Green]

abbrev TL1ToTL2Green    := LLTL[G ((TL1Green ∧ ((← TL1Queue) == 0)) → (Xˢ (¬TL1Green ∧ TL2Green)))]
abbrev TL2ToTL1Green    := LLTL[G ((TL2Green ∧ ((← TL2Queue) == 0)) → (Xˢ (TL1Green ∧ ¬ TL2Green)))]
abbrev TL1StayGreen     := LLTL[G ((TL1Green ∧ ((← TL1Queue) != 0)) → (Xˢ (TL1Green ∧ ¬ TL2Green)))]
abbrev TL2StayGreen     := LLTL[G ((TL2Green ∧ ((← TL2Queue) != 0)) → (Xˢ (¬ TL1Green ∧ TL2Green)))]

abbrev TL1GreenDeparts  := LLTL[G (TL1Green → ((← TL1Departs) == max_departs))]
abbrev TL1RedDeparts    := LLTL[G (¬TL1Green → ((← TL1Departs) == 0))]
abbrev TL2GreenDeparts  := LLTL[G (TL2Green → ((← TL2Departs) == max_departs))]
abbrev TL2RedDeparts    := LLTL[G (¬TL2Green → ((← TL2Departs) == 0))]

abbrev TL1ArrivesBounds := LLTL[G (0 ≤ (← TL1Arrives) ∧ (← TL1Arrives) ≤ max_arrives)]
abbrev TL2ArrivesBounds := LLTL[G (0 ≤ (← TL2Arrives) ∧ (← TL2Arrives) ≤ max_arrives)]

abbrev TL1QueueNext     := LLTL[G ((X (← TL1Queue)) == (← TL1Queue) + (← TL1Arrives) - (← TL1Departs))]
abbrev TL2QueueNext     := LLTL[G ((X (← TL2Queue)) == (← TL2Queue) + (← TL2Arrives) - (← TL2Departs))]

abbrev TLBaseProperties := LLTL[TL1StartGreen ∧ TL2StartRed ∧ TL1ToTL2Green ∧ TL2ToTL1Green
                            ∧ TL1StayGreen ∧ TL2StayGreen ∧ TL1GreenDeparts ∧ TL1RedDeparts
                            ∧ TL2GreenDeparts ∧ TL2RedDeparts ∧ TL1ArrivesBounds ∧ TL2ArrivesBounds
                            ∧ TL1QueueNext ∧ TL2QueueNext]

-- Optional Properties
abbrev TrafficLulls       := LLTL[(G (F ((← TL1Arrives) == 0))) ∧ (G (F ((← TL2Arrives) == 0)))]

-- Goal Properties
abbrev LightSafety        := LLTL[G (¬(TL1Green ∧ TL2Green))]
abbrev NeverStarvation    := LLTL[(G (F ((← TL1Queue) == 0))) ∧ (G (F ((← TL2Queue) == 0)))]

-- Example Proofs
theorem SatisfiesLightSafety : TLBaseProperties ⇒ⁱ LightSafety := by
  simp [TLBaseProperties, LeanLTL.TraceSet.sem_imp_inf_iff, LeanLTL.TraceSet.sat_imp_iff]
  intro t h_t_inf h
  simp [LeanLTL.TraceSet.sat_and_iff] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have h_ind : t ⊨ LLTL[G ((¬(TL1Green ∧ TL2Green)) ∧ (TL1Green ∨ TL2Green))] := by
    apply LeanLTL.TraceSet.globally_induction
    . simp [push_fltl] at h1 h2 ⊢
      tauto
    . simp [push_fltl] at h3 h4 h5 h6 ⊢
      intro n h_n ih h_1_n h15
      specialize h3 n h_n
      specialize h4 n h_n
      specialize h5 n h_n
      specialize h6 n h_n
      simp [*] at h3 h4 h5 h6
      by_cases t.shift n h_n ⊨ TL1Green <;> by_cases t.shift n h_n ⊨ LLTL[((← TL1Queue) != 0)] <;> (simp_all; try tauto)
  simp [push_fltl] at h_ind ⊢
  simp_all

theorem TrafficLullsImpliesNeverStarvation : LLTL[TrafficLulls ∧ TLBaseProperties] ⇒ⁱ NeverStarvation := by
  simp [TLBaseProperties, LeanLTL.TraceSet.sem_imp_inf_iff, LeanLTL.TraceSet.sat_imp_iff]
  intro t h_t_inf h
  simp [LeanLTL.TraceSet.sat_and_iff] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

  sorry
