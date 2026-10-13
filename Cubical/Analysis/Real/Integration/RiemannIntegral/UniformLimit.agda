module Cubical.Analysis.Real.Integration.RiemannIntegral.UniformLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ using (ℕ; max)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; ℚ₊≡)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Uniform
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Error

opaque
  -- If the approximating integrals already converge, radiuswise uniform
  -- convergence is enough to identify their limit with the new integral.
  uniformLimitPreservesIntegral : ∀ (functions : ℕ → ℝ → ℝ) f a b values value →
    (∀ n → HasRiemannIntegralOn (functions n) a b (values n)) →
    IsUniformLimit (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) →
    isLimitSequence values value → HasRiemannIntegralOn f a b value
  uniformLimitPreservesIntegral functions f a b values value hasValues uniform values→value ε =
    PT.rec squash₁ (λ { (k , length<bound) →
      PT.rec squash₁ (λ { (N , nearFunction) →
        PT.rec squash₁ (λ { (M , nearValue) →
          PT.map (λ { (δ , nearIntegral) → δ , λ tagged fine →
            closeness→absDifference< (riemannSum tagged f) value ε
              (subst (λ ρ → riemannSum tagged f ∼[ ρ ] value)
                (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst ε)))
                (triangle∼ (riemannSum tagged f) (values (max N M)) value (ε /2₊) (ε /2₊)
                  (subst (λ ρ → riemannSum tagged f ∼[ ρ ] values (max N M))
                    (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst (ε /2₊))))
                    (triangle∼ (riemannSum tagged f) (riemannSum tagged (functions (max N M)))
                      (values (max N M)) ((ε /2₊) /2₊) ((ε /2₊) /2₊)
                      (riemannSumsCloseFromUniformBound tagged f (functions (max N M))
                        (naturalBound k) ((ε /2₊) /2₊) length<bound
                        (λ point → sym∼ (functions (max N M) (fst point)) (f (fst point))
                          (((ε /2₊) /2₊) ₊／₊ naturalBound k)
                          (nearFunction (max N M) (ℕ.left-≤-max {m = N} {n = M}) point)))
                      (absDifference<→closeness (riemannSum tagged (functions (max N M)))
                        (values (max N M)) ((ε /2₊) /2₊) (nearIntegral tagged fine))))
                  (nearValue (max N M) (ℕ.right-≤-max {n = M} {m = N})))) })
            (hasValues (max N M) ((ε /2₊) /2₊)) }) (values→value (ε /2₊)) })
        (uniform (((ε /2₊) /2₊) ₊／₊ naturalBound k)) }) (∃naturalUpperBound (b - a))

  integralsConvergeUnderUniformLimit : ∀ (functions : ℕ → ℝ → ℝ) f a b → a ≤ℝ b →
    ∀ values value → (∀ n → HasRiemannIntegralOn (functions n) a b (values n)) →
    HasRiemannIntegralOn f a b value →
    IsUniformLimit (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) → isLimitSequence values value
  integralsConvergeUnderUniformLimit functions f a b a≤b values value hasValues hasValue uniform ε =
    PT.rec squash₁ (λ { (k , length<bound) →
      PT.map (λ { (N , close) → N , λ n large →
        riemannIntegralsCloseFromUniformBound a b a≤b (functions n) f (values n) value
          (naturalBound k) ε length<bound (hasValues n) hasValue (close n large) })
        (uniform (ε ₊／₊ naturalBound k)) }) (∃naturalUpperBound (b - a))

  uniformLimitWithIsRiemannIntegrableOn : ∀ (functions : ℕ → ℝ → ℝ) f a b → a ≤ℝ b →
    (integrable : ∀ n → IsRiemannIntegrableOn (functions n) a b) →
    (μ : ℚ₊ → ℕ) → IsUniformLimitWith (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) μ →
    IsRiemannIntegrableOn f a b
  uniformLimitWithIsRiemannIntegrableOn functions f a b a≤b integrable μ uniform =
    PT.rec (isPropIsRiemannIntegrableOn a b a≤b f)
      (λ { (k , length<bound) → fromBound (naturalBound k) length<bound })
      (∃naturalUpperBound (b - a))
    where
    values : ℕ → ℝ
    values n = fst (integrable n)
    fromBound : (bound : ℚ₊) → b - a <ℝ rat (fst bound) → IsRiemannIntegrableOn f a b
    fromBound bound length<bound = value
      , uniformLimitPreservesIntegral functions f a b values value (λ n → snd (integrable n))
        (λ ε → ∣ μ ε , uniform ε ∣₁) (limitOfSequenceIsLimit values witness)
      where
      witness : SeqWitness values
      witness = ∣ (λ ε → μ ((ε ₊／₊ bound) /2₊))
        , (λ ε m n largeM largeN →
          riemannIntegralsCloseFromUniformBound a b a≤b (functions m) (functions n)
            (values m) (values n) bound ε length<bound (snd (integrable m)) (snd (integrable n))
            (λ point → subst (λ ρ → functions m (fst point) ∼[ ρ ] functions n (fst point))
              (ℚ₊≡ (1/2∈ℚ./2+/2≡id (fst (ε ₊／₊ bound))))
              (triangle∼ (functions m (fst point)) (f (fst point)) (functions n (fst point))
                ((ε ₊／₊ bound) /2₊) ((ε ₊／₊ bound) /2₊)
                (uniform ((ε ₊／₊ bound) /2₊) m largeM point)
                (sym∼ (functions n (fst point)) (f (fst point)) ((ε ₊／₊ bound) /2₊)
                  (uniform ((ε ₊／₊ bound) /2₊) n largeN point))))) ∣₁
      value : ℝ
      value = limitOfSequence values witness

  uniformLimitIsRiemannIntegrableOn : ∀ (functions : ℕ → ℝ → ℝ) f a b → a ≤ℝ b →
    (∀ n → IsRiemannIntegrableOn (functions n) a b) →
    UniformLimitWitness (λ n (x : ClosedInterval a b) → functions n (fst x)) (f ∘ fst) → IsRiemannIntegrableOn f a b
  uniformLimitIsRiemannIntegrableOn functions f a b a≤b integrable =
    PT.rec (isPropIsRiemannIntegrableOn a b a≤b f)
      (λ { (μ , uniform) → uniformLimitWithIsRiemannIntegrableOn functions f a b a≤b integrable μ uniform })
