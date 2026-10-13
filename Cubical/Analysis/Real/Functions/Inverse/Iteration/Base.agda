module Cubical.Analysis.Real.Functions.Inverse.Iteration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Domain.Interval

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

-- For an increasing function with Lipschitz constant one, the residual
-- step stays below the target and inside its bracket. The derivative may
-- vanish at either endpoint; no positive lower slope is assumed.
module Iteration
  (f : ℝ → ℝ) (a b target : ℝ)
  (ordered : a ≤ℝ b)
  (lower-image : f a ≤ℝ target) (upper-image : target ≤ℝ f b)
  (monotone : ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → f x ≤ℝ f y)
  (upper-difference : ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b →
    f y - f x ≤ℝ y - x) where

  residual : ℝ → ℝ
  residual x = target - f x

  step : ℝ → ℝ
  step x = x + residual x

  Invariant : ℝ → Type₀
  Invariant x = (a ≤ℝ x) × (x ≤ℝ b) × (f x ≤ℝ target)

  opaque
    residual-nonnegative : ∀ x → Invariant x → 0ℝ ≤ℝ residual x
    residual-nonnegative x p = nonnegativeSub (f x) target (snd (snd p))

    step-increasing : ∀ x → Invariant x → x ≤ℝ step x
    step-increasing x p = subst (_≤ℝ step x) (addIdR x)
      (addPres≤L 0ℝ (residual x) x (residual-nonnegative x p))

    step-upper : ∀ x → Invariant x → step x ≤ℝ b
    step-upper x p = subst (step x ≤ℝ_)
      (addComm x (b - x) ∙ subAddCancel b x)
      (addPres≤L (residual x) (b - x) x
        (≤ℝ-trans (residual x) (f b - f x) (b - x)
          (addPres≤R target (f b) (- f x) upper-image)
          (upper-difference x b (fst p) (fst (snd p)) (≤ℝ-refl b))))

    step-difference : ∀ x → step x - x ≡ residual x
    step-difference x = cong (_- x) (addComm x (residual x))
      ∙ R.plusMinus (residual x) x

    step-image-upper : ∀ x → Invariant x → f (step x) ≤ℝ target
    step-image-upper x p = addReflects≤R (f (step x)) target (- f x)
      (subst (f (step x) - f x ≤ℝ_) (step-difference x)
        (upper-difference x (step x) (fst p) (step-increasing x p) (step-upper x p)))

    step-preserves : ∀ x → Invariant x → Invariant (step x)
    step-preserves x p =
      ≤ℝ-trans a x (step x) (fst p) (step-increasing x p)
      , step-upper x p , step-image-upper x p

    residual-decreases : ∀ x → Invariant x → residual (step x) ≤ℝ residual x
    residual-decreases x p = addPres≤L (- f (step x)) (- f x) target
      (negPres≤ (f x) (f (step x))
        (monotone x (step x) (fst p) (step-increasing x p) (step-upper x p)))

  -- Opaque recursive values avoid expanding completed sine/cosine values
  -- during uses of the induction hypotheses.
  opaque
    state : ℕ → Σ[ x ∈ ℝ ] Invariant x
    state zero = a , ≤ℝ-refl a , ordered , lower-image
    state (suc n) = step (fst (state n)) , step-preserves (fst (state n)) (snd (state n))

    points : ℕ → ℝ
    points n = fst (state n)

    points-zero : points zero ≡ a
    points-zero = refl

    points-step : ∀ n → points (suc n) ≡ step (points n)
    points-step n = refl

    points-invariant : ∀ n → Invariant (points n)
    points-invariant n = snd (state n)

  intervalPoints : ℕ → ClosedInterval a b
  intervalPoints n = points n , fst (points-invariant n) , fst (snd (points-invariant n))

  opaque
    residual-antitone-step : ∀ n → residual (points (suc n)) ≤ℝ residual (points n)
    residual-antitone-step n = subst (λ x → residual x ≤ℝ residual (points n))
      (sym (points-step n)) (residual-decreases (points n) (points-invariant n))

    weighted-residual : ∀ n → realNatural n · residual (points n) ≤ℝ points n - a
    weighted-residual zero = subst2 _≤ℝ_
      (sym (R.0LeftAnnihilates (residual (points zero))))
      (sym (cong (_- a) points-zero ∙ subSelf a)) (≤ℝ-refl 0ℝ)
    weighted-residual (suc n) = ≤ℝ-trans
      (realNatural (suc n) · residual (points (suc n)))
      (realNatural (suc n) · residual (points n)) (points (suc n) - a)
      (mulPres≤L (residual (points (suc n))) (residual (points n)) (realNatural (suc n))
        (0≤→isNonnegative (realNatural (suc n)) (realNatural-nonnegative (suc n)))
        (residual-antitone-step n))
      (subst2 _≤ℝ_ (sym coefficient-path) (sym distance-path)
        (addPres≤R (realNatural n · residual (points n)) (points n - a)
          (residual (points n)) (weighted-residual n)))
      where
      coefficient-path : realNatural (suc n) · residual (points n) ≡
        realNatural n · residual (points n) + residual (points n)
      coefficient-path = cong (_· residual (points n)) (realNatural-suc n)
        ∙ mulDistL (realNatural n) 1ℝ (residual (points n))
        ∙ cong (realNatural n · residual (points n) +_) (mulIdL (residual (points n)))
      distance-path : points (suc n) - a ≡ (points n - a) + residual (points n)
      distance-path = cong (_- a) (points-step n)
        ∙ sym (addAssoc (points n) (residual (points n)) (- a))
        ∙ cong (points n +_) (addComm (residual (points n)) (- a))
        ∙ addAssoc (points n) (- a) (residual (points n))

    weighted-residual-bound : ∀ n → realNatural n · residual (points n) ≤ℝ b - a
    weighted-residual-bound n = ≤ℝ-trans
      (realNatural n · residual (points n)) (points n - a) (b - a)
      (weighted-residual n)
      (addPres≤R (points n) b (- a) (fst (snd (points-invariant n))))
