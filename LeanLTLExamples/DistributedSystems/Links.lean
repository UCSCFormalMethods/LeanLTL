import LeanLTL
import LeanLTLExamples.DistributedSystems.Defs

open Classical

open LeanLTL.Notation
open LeanLTLExamples.DistributedSystems

namespace LeanLTL.Examples.DistributedSystems

instance {α : Type} : Membership α (Option $ Set α) where
  mem
  | .some s, a => a ∈ s
  | _, _ => False

namespace FairLossLink
  axiom MaxDeliverTime : ℕ

  variable {𝓂 : Type}

  inductive Request | Send (dest : Process) (msg : 𝓂)
  -- In distributed system terminology, "deliver" sorta means "receives".
  -- That's because we are reasoning about the fair-loss link component
  -- who will be delivering messages to the process on which it is hosted.
  inductive Indication | Deliver (src : Process) (msg : 𝓂)

  -- Events for a given process.
  structure ε where
    requests : Set $ @Request 𝓂
    indications : Set $ @Indication 𝓂

  -- Events at a point in time for some process.
  -- If σ p is Option.none for some p, then some p is crashed at that state.
  def σ := Process → Option (@ε 𝓂)
  instance : Inhabited $ @σ 𝓂 where
    default _ := .none

  def Trace' := Trace $ @σ 𝓂
  def TraceSet' := TraceSet $ @σ 𝓂

  -- Handmade Trace Functions
  def crashedAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).isNone
  def requestsAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).map ε.requests
  def indicationsAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).map ε.indications

  -- LLTL Trace Functions for use in LLTL macro
  def crashed (s : @σ 𝓂) (p : Process) := (s p).isNone
  def requests (s : @σ 𝓂) (p : Process) := (s p).map ε.requests
  def indications (s : @σ 𝓂) (p : Process) := (s p).map ε.indications

  -- If process p₁ sends a message m infinitely often to process p₂,
  -- then process p₂ will deliver m infinitely often from p₁.
  def fairLoss : @TraceSet' 𝓂 where
    sat t := ∀ (p₁ p₂ : Process) (msg : 𝓂),
      (∀ n, ∃ sendTime, n ≤ sendTime ∧ (.Send p₂ msg) ∈ (requestsAt t sendTime p₁))
      → (∀ n, ∃ deliverTime > n,
          (crashedAt t deliverTime p₂) ∨ (.Deliver p₁ msg) ∈ (indicationsAt t deliverTime p₂))

  -- If process p₁ does *not* send a message m infinitely often to process p₂,
  -- then process p₂ should *not* deliver m infinitely often.
  def finiteDuplication : @TraceSet' 𝓂 where
    sat t := ∀ (p₁ p₂ : Process) (msg : 𝓂),
      (∃ noMoreSending, (.Send p₂ msg) ∉ (requestsAt t noMoreSending p₁))
        → (∃ noMoreDelivering, (.Deliver p₁ msg) ∉ (indicationsAt t noMoreDelivering p₂))

  -- A message does not come out of thin air;
  -- If process p₂ delivers a message from process p₁,
  def noCreation : @TraceSet' 𝓂 where
    sat t := ∀ (p₁ p₂ : Process) (msg : 𝓂) deliverTime,
      ((.Deliver p₁ msg) ∈ (indicationsAt t deliverTime p₂))
      → ∃ sendTime < deliverTime, deliverTime ≤ sendTime + MaxDeliverTime
          ∧ (.Send p₂ msg) ∈ (requestsAt t sendTime p₁)

end FairLossLink
open FairLossLink in
def FairLossLink {𝓂 : Type} : @TraceSet' 𝓂 := LLTL[fairLoss ∧ finiteDuplication ∧ noCreation]

namespace StubbornLink
  variable {𝓂 : Type}

  inductive Request | Send (dest : Process) (msg : 𝓂)
  inductive Indication | Deliver (src : Process) (msg : 𝓂)

  structure ε where
    requests : Set $ @Request 𝓂
    indications : Set $ @Indication 𝓂

  def σ := Process → Option (@ε 𝓂)
  instance : Inhabited $ @σ 𝓂 where
    default _ := .none

  def Trace' := Trace $ @σ 𝓂
  def TraceSet' := TraceSet $ @σ 𝓂

  def crashedAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).isNone
  def requestsAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).map ε.requests
  def indicationsAt (t : @Trace' 𝓂) n (p : Process) := (t.toFun! n p).map ε.indications

  def crashed (s : @σ 𝓂) (p : Process) := (s p).isNone
  def requests (s : @σ 𝓂) (p : Process) := (s p).map ε.requests
  def indications (s : @σ 𝓂) (p : Process) := (s p).map ε.indications
end StubbornLink
-- Unlike the FairLossLink, whose properties are assumed, we write the code for the stubborn link,
-- and show that it can be made using a fair-loss link.
--
-- Afterwards we will reason about its properties.
open StubbornLink in
def StubbornLink {𝓂 : Type} : @TraceSet' 𝓂 where
  sat t :=
    -- There is a fair loss link that runs in lockstep with the stubborn link.
    ∃ fll_t : @FairLossLink.Trace' 𝓂, (fll_t ⊨ FairLossLink)
    -- And it runs for as long as the stubborn link
    ∧ fll_t.length = t.length
    -- And a process crashes on both at the same time
    ∧ (∀ n p, crashedAt t n p ↔ FairLossLink.crashedAt fll_t n p)
    -- Here are the only requests made to it.
    ∧ (∀ n p₁ p₂ msg,
      (.Send p₂ msg) ∈ (FairLossLink.requestsAt fll_t n p₁)
        ↔ ∃ sendTime ≤ n, (.Send p₂ msg) ∈ requestsAt t sendTime p₁)
    -- ∧ (∀ sendTime p₁ p₂ msg, ((.Send p₂ msg) ∈ requestsAt t sendTime p₁)
    --     ↔ ∀ forwardTime, sendTime ≤ forwardTime
    --     → ((.Send p₂ msg) ∈ FairLossLink.requestsAt fll_t forwardTime p₁))
    -- Now that we have our fair loss link, and it's up and running, we need to filter our stubborn
    -- link indications.
    -- The stubborn link delivers whenever the fair loss link delivers.
    ∧ (∀ deliverTime p₁ p₂ msg,
        (.Deliver p₁ msg) ∈ FairLossLink.indicationsAt fll_t deliverTime p₂
        ↔ ((.Deliver p₁ msg) ∈ indicationsAt t deliverTime p₂))

namespace StubbornLink
  variable {𝓂 : Type}
  -- If p1 sends to p2, then p2 will deliver infinitely often, or it will have crashed.
  theorem stubbornDelivery (p₁ p₂ : Process) (msg : 𝓂) :
    ⊨ⁱ LLTL[StubbornLink →
      𝐆 (((.Send p₂ msg) ∈ ((← requests) p₁))
      → 𝐆 𝐅 (((← crashed) p₂) = true ∨ (.Deliver p₁ msg) ∈ ((← indications) p₂)))
    ] := by
      simp +contextual [push_ltl]
      rintro t t_inf ⟨fll_t, fairloss, fll_t_len, crashes, subreq, delivery⟩ x req z
      unfold FairLossLink at fairloss
      simp +contextual [push_ltl] at fairloss
      replace fairloss := fairloss.1
      unfold FairLossLink.fairLoss at fairloss
      simp at fairloss
      specialize fairloss p₁ p₂ msg
      -- Suffering
      have infiniteSend : ∀ (n : ℕ), ∃ sendTime ≥ n, .Send p₂ msg ∈ FairLossLink.requestsAt fll_t sendTime p₁ := by
        intro now
        specialize subreq (now + x) p₁ p₂ msg
        replace subreq := subreq.mpr
        specialize subreq ⟨x, by simp, req⟩
        exists (now + x)
        exact ⟨by omega, subreq⟩
      specialize fairloss infiniteSend (z + x)
      obtain ⟨deliverTime, ⟨deliverTimeLowerBound, crashedOrDelivered⟩⟩ := fairloss
      exists (deliverTime - (z + x))
      rw [@Nat.sub_add_cancel deliverTime (z + x) deliverTimeLowerBound.le]
      match crashedOrDelivered with
      | .inl crashed =>
        left
        replace crashes := (crashes deliverTime p₂).mpr
        exact crashes crashed
      | .inr delivered =>
        right
        replace delivery := delivery deliverTime p₁ p₂ msg
        unfold indicationsAt at delivery
        unfold indications
        exact delivery.mp delivered

  -- If a message m was stubborn received at time n, it must have been stubborn sent.
  -- Proof by contradiction:
  -- 1. Assume m was stubborn received [but was not stubborn sent!]
  --    Show that this results in a contradiction.
  --
  -- 2. m must have been fair-loss received because that's how the stubborn link code works.
  --
  -- 3. By the no-creation property on the fair-loss link, m was fair-loss sent at some time n' before n.
  --
  -- 4. But we assumed that message m was not stubborn sent before time n!
  --    Because it was not stubborn sent before time n, then it couldn't have been fair-loss sent before n.
  --
  -- Contradiction ∎
  theorem noCreation (t : Trace') (p₁ p₂ : Process) (msg : 𝓂) deliverTime:
    (t ⊨ StubbornLink) → ((.Deliver p₁ msg) ∈ (indicationsAt t deliverTime p₂))
    → ∃ sendTime < deliverTime, (.Send p₂ msg) ∈ (requestsAt t sendTime p₁)
    := by
      -- 1.
      rintro ⟨fll_t, fairloss, sameLength, crashes, sendCode, deliverCode⟩ stubbornDelivery
      apply byContradiction
      intro noStubbornSend
      simp at noStubbornSend
      -- 2.
      have fllDelivery := (deliverCode deliverTime p₁ p₂ msg).mpr stubbornDelivery
      obtain ⟨_, _, noCreation⟩ := fairloss
      -- 3.
      replace noCreation := noCreation p₁ p₂ msg deliverTime fllDelivery
      obtain ⟨n', n'min, n'max, fairlossSend⟩ := noCreation
      -- 4.
      obtain ⟨m, mMin, stubbornSend⟩ := (sendCode n' p₁ p₂ msg).mp fairlossSend
      specialize noStubbornSend m (by omega)
      contradiction
