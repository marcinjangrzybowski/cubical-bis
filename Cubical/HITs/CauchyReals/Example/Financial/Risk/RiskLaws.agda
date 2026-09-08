{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws where

open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall public
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Laws for attained CVaR values. Existence is supplied by a certificate,
-- rather than assumed for every vector of arbitrary constructive reals.
-- Every elimination of a hidden optimizer has a proposition as its target.
module CVaRLaws {n : ℕ} (P : Distribution n) (level : TailLevel) where
  open TailRisk P level

  CVaR-monotone : ∀ X Y r s →
    (∀ i → X i ≤ᵣ Y i) → IsCVaR X r → IsCVaR Y s → r ≤ᵣ s
  CVaR-monotone X Y r s bound (lowerX , attainX) (lowerY , attainY) =
    PT.rec (isProp≤ᵣ r s)
      (λ (t , p) → isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _ (lowerX t) (objective-monotone X Y t bound)) p)
      attainY

  -- Transport the whole minimum predicate, including truncated attainment.
  IsCVaR-cash : ∀ X r c → IsCVaR X r →
    IsCVaR (λ i → c +ᵣ X i) (c +ᵣ r)
  IsCVaR-cash X r c (lower , attained) = lower' , PT.map
    (λ (t , p) → (c +ᵣ t) ,
      (objective-cash X t c ∙ cong (c +ᵣ_) p)) attained
    where
    cancel : ∀ t → c +ᵣ (t -ᵣ c) ≡ t
    cancel t = ℝ!

    lower' : ∀ t → c +ᵣ r ≤ᵣ objective (λ i → c +ᵣ X i) t
    lower' t = isTrans≤≡ᵣ _ _ _ (≤ᵣ-o+ _ _ c (lower (t -ᵣ c)))
      (sym (objective-cash X (t -ᵣ c) c)
        ∙ cong (objective (λ i → c +ᵣ X i)) (cancel t))

  CVaR-cash : ∀ X r c s → IsCVaR X r →
    IsCVaR (λ i → c +ᵣ X i) s → s ≡ c +ᵣ r
  CVaR-cash X r c s value translated =
    CVaR-unique _ _ _ translated (IsCVaR-cash X r c value)

  CVaR-subadditive : ∀ X Y r s u →
    IsCVaR X r → IsCVaR Y s →
    IsCVaR (λ i → X i +ᵣ Y i) u → u ≤ᵣ r +ᵣ s
  CVaR-subadditive X Y r s u (lowerX , attainX) (lowerY , attainY)
    (lowerSum , attainSum) = PT.rec2 (isProp≤ᵣ _ _)
      (λ (a , pa) (b , pb) → isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _ (lowerSum (a +ᵣ b))
          (objective-subadditive X Y a b))
        (cong₂ _+ᵣ_ pa pb)) attainX attainY

  -- Nonnegative conic aggregation; convex mixtures are the a + b = 1 case.
  CVaR-weighted : ∀ X Y a b r s u → 0 ≤ᵣ a → 0 ≤ᵣ b →
    IsCVaR X r → IsCVaR Y s →
    IsCVaR (λ i → a ·ᵣ X i +ᵣ b ·ᵣ Y i) u →
    u ≤ᵣ a ·ᵣ r +ᵣ b ·ᵣ s
  CVaR-weighted X Y a b r s u a₊ b₊ (lowerX , attainX) (lowerY , attainY)
    (lowerSum , attainSum) = PT.rec2 (isProp≤ᵣ _ _)
      (λ (x , px) (y , py) → isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _ (lowerSum (a ·ᵣ x +ᵣ b ·ᵣ y))
          (objective-weighted X Y a b x y a₊ b₊))
        (cong₂ _+ᵣ_ (cong (a ·ᵣ_) px) (cong (b ·ᵣ_) py)))
      attainX attainY

  CVaR-perturbation : ∀ X Y r s ε →
    (∀ i → X i ≤ᵣ ε +ᵣ Y i) → IsCVaR X r → IsCVaR Y s →
    r ≤ᵣ ε +ᵣ s
  CVaR-perturbation X Y r s ε bound valueX valueY =
    CVaR-monotone X (λ i → ε +ᵣ Y i) r (ε +ᵣ s) bound valueX
      (IsCVaR-cash Y s ε valueY)

  -- Comparing a certified value to capital is exactly the earlier policy
  -- predicate. No optimizer needs to be exposed to the policy consumer.
  CVaR-accepted→bound : ∀ X r budget → IsCVaR X r →
    Accepted X budget → r ≤ᵣ budget
  CVaR-accepted→bound X r budget (lower , attained) =
    PT.rec (isProp≤ᵣ _ _) (λ (t , p) → isTrans≤ᵣ _ _ _ (lower t) p)

  CVaR-bound→accepted : ∀ X r budget → IsCVaR X r →
    r ≤ᵣ budget → Accepted X budget
  CVaR-bound→accepted X r budget (lower , attained) bound =
    PT.map (λ (t , p) → t , isTrans≡≤ᵣ _ _ _ p bound) attained

  CVaR-accepted≃bound : ∀ X r budget → IsCVaR X r →
    Accepted X budget ≃ (r ≤ᵣ budget)
  CVaR-accepted≃bound X r budget value =
    propBiimpl→Equiv (accepted-isProp X budget) (isProp≤ᵣ _ _)
      (CVaR-accepted→bound X r budget value)
      (CVaR-bound→accepted X r budget value)

  CVaR-policy-path : ∀ X r budget → IsCVaR X r →
    Accepted X budget ≡ (r ≤ᵣ budget)
  CVaR-policy-path X r budget value = ua (CVaR-accepted≃bound X r budget value)

  CVaR-scenario-upper : ∀ X r budget → IsCVaR X r →
    (∀ i → X i ≤ᵣ budget) → r ≤ᵣ budget
  CVaR-scenario-upper X r budget (lower , attained) bound =
    isTrans≤≡ᵣ _ _ _ (lower budget) (objective-at-upper-bound X budget bound)

  CVaR-dual-lower : ∀ X r → IsCVaR X r →
    (Q : Distribution n) → Admissible Q → expectation Q X ≤ᵣ r
  CVaR-dual-lower X r (lower , attained) Q cap =
    PT.rec (isProp≤ᵣ _ _)
      (λ (t , p) → isTrans≤≡ᵣ _ _ _ (weak-duality X Q cap t) p) attained
