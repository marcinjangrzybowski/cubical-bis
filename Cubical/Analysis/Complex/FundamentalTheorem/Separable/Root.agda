module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Root where

-- Choice-free exact root existence under positive formal separability.
-- Choose two rational tolerances and one approximate root under a single
-- truncated conclusion; thereafter Newton iteration is deterministic.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Contraction using (ComplexBall)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.Polynomial.Newton using (localNewtonRoot)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic
  using (BezoutSeparability; ExactRootData; StronglySeparableRootExistence)
open import Cubical.Analysis.Complex.FundamentalTheorem.Approximate.Norm
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Smallness
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Parameters
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants using () renaming
  (descentHalf to half; descentHalf-positive to half-positive)

private module CertifiedRoot (n : ℕ) (p : MonicPolynomial (suc n)) (certificate : BezoutSeparability p) where
  open Parameters p certificate renaming
    (residualMultiplier to S; residualMultiplier-nonnegative to S-nonnegative;
     inverseBound to M; inverseBound-nonnegative to M-nonnegative;
     variationBound to H; variationBound-nonnegative to H-nonnegative)

  opaque
    fromApproximation : (ρ ε : ℚ₊) → rat (fst ρ) ≤ℝ 1ℝ →
      (M · H) · rat (fst ρ) ≤ℝ half → rat (fst ε) ≤ℝ half →
      S · rat (fst ε) ≤ℝ half → M · rat (fst ε) ≤ℝ half · rat (fst ρ) →
      (center : ℂ) → normℂ (evaluateMonic p center) <ℝ rat (fst ε) → ExactRootData p
    fromApproximation ρ ε radius-small contracts tolerance-small residual-small correction-small center approximate =
      fst result , fst (snd (snd result))
      where
      radius tolerance : ℝ
      radius = rat (fst ρ)
      tolerance = rat (fst ε)
      radius-positive : 0ℝ <ℝ radius
      radius-positive = <ℚ→<ℝ 0 (fst ρ) (snd ρ)
      radius-nonnegative : 0ℝ ≤ℝ radius
      radius-nonnegative = <ℝ-weaken 0ℝ radius radius-positive
      value-bounded : normℂ (evaluateMonic p center) ≤ℝ tolerance
      value-bounded = <ℝ-weaken (normℂ (evaluateMonic p center)) tolerance approximate
      modulus-bounded : modulusℂ (evaluateMonic p center) ≤ℝ tolerance
      modulus-bounded = ≤ℝ-trans (modulusℂ (evaluateMonic p center)) (normℂ (evaluateMonic p center)) tolerance
        (modulusℂ≤normℂ (evaluateMonic p center)) value-bounded
      center-bounded : normℂ center ≤ℝ centerBound
      center-bounded = smallResidual-centerBound center
        (≤<ℝ-trans (modulusℂ (evaluateMonic p center)) tolerance 1ℝ modulus-bounded
          (≤<ℝ-trans tolerance half 1ℝ tolerance-small half<one))
      residual-budget : S · modulusℂ (evaluateMonic p center) ≤ℝ half
      residual-budget = ≤ℝ-trans (S · modulusℂ (evaluateMonic p center)) (S · tolerance) half
        (mulPres≤L (modulusℂ (evaluateMonic p center)) tolerance S (0≤→isNonnegative S S-nonnegative) modulus-bounded)
        residual-small
      inverseData : Σ[ inverse ∈ ℂ ]
        ((inverse ·ℂ derivativeMonic p center ≡ 1ℂ) × (normℂ inverse ≤ℝ M))
      inverseData = derivativeInverse center center-bounded residual-budget
      inverse : ℂ
      inverse = fst inverseData
      inverse-bounded : normℂ inverse ≤ℝ M
      inverse-bounded = snd (snd inverseData)
      error-nonnegative : 0ℝ ≤ℝ H · radius
      error-nonnegative = product-nonnegative H radius H-nonnegative radius-nonnegative
      inverse-error : normℂ inverse · (H · radius) ≤ℝ half
      inverse-error = ≤ℝ-trans (normℂ inverse · (H · radius)) (M · (H · radius)) half
        (mulPres≤R-0≤ (normℂ inverse) M (H · radius) error-nonnegative inverse-bounded)
        (subst (_≤ℝ half) (sym (mulAssoc M H radius)) contracts)
      correction : normℂ (inverse ·ℂ evaluateMonic p center) ≤ℝ (1ℝ - half) · radius
      correction = subst (normℂ (inverse ·ℂ evaluateMonic p center) ≤ℝ_)
        (sym (cong (_· radius) one-minus-half))
        (≤ℝ-trans (normℂ (inverse ·ℂ evaluateMonic p center)) (M · tolerance) (half · radius)
          (normℂ-mulBound inverse (evaluateMonic p center) M tolerance inverse-bounded value-bounded) correction-small)
      result : Σ[ root ∈ ℂ ] (ComplexBall center radius root × (evaluateMonic p root ≡ 0ℂ) ×
        ((z : ℂ) → ComplexBall center radius z → evaluateMonic p z ≡ 0ℂ → z ≡ root))
      result = localNewtonRoot (suc n) p center inverse radius (H · radius) half
        (fst (snd inverseData)) radius-positive error-nonnegative (<ℝ-weaken 0ℝ half half-positive) half<one
        inverse-error correction (remainderBound center radius center-bounded radius-small)

  exactRoot : PT.∥ ExactRootData p ∥₁
  exactRoot = PT.rec PT.squash₁ atRadius
    (smallPositiveRationalForTwoProducts 1ℝ (M · H) half 0ℝ 1ℝ one-positive
      (product-nonnegative M H M-nonnegative H-nonnegative) half-positive (≤ℝ-refl 0ℝ) one-positive)
    where
    atRadius : (Σ[ ρ ∈ ℚ₊ ] (rat (fst ρ) ≤ℝ 1ℝ) × ((M · H) · rat (fst ρ) ≤ℝ half) ×
      (0ℝ · rat (fst ρ) ≤ℝ 1ℝ)) → PT.∥ ExactRootData p ∥₁
    atRadius (ρ , radius-small , contracts , unused) = PT.rec PT.squash₁ atTolerance
      (smallPositiveRationalForTwoProducts half S half M (half · rat (fst ρ)) half-positive
        S-nonnegative half-positive M-nonnegative
        (mulPositive half (rat (fst ρ)) half-positive (<ℚ→<ℝ 0 (fst ρ) (snd ρ))))
      where
      atTolerance : (Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ half) × (S · rat (fst ε) ≤ℝ half) ×
        (M · rat (fst ε) ≤ℝ half · rat (fst ρ))) → PT.∥ ExactRootData p ∥₁
      atTolerance (ε , tolerance-small , residual-small , correction-small) = PT.map
        (λ (center , approximate) → fromApproximation ρ ε radius-small contracts tolerance-small
          residual-small correction-small center approximate)
        (approximatePolynomialRoots-norm n p ε)

-- The certificate may itself be supplied only propositionally: its use
-- stays within the propositionally truncated root-existence conclusion.
stronglySeparableRootExistence : StronglySeparableRootExistence
stronglySeparableRootExistence n p = PT.rec PT.squash₁ (CertifiedRoot.exactRoot n p)
