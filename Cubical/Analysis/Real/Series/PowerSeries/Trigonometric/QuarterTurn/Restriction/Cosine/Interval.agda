module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue using (nonnegativeSub)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


CosineHalfInterval : ℝ → Type₀
CosineHalfInterval quarter = ClosedInterval 0ℝ (halfTurn quarter)


private
  reflectionAtHalfTurn : ∀ quarter → quarter - halfTurn quarter ≡ - quarter
  reflectionAtHalfTurn quarter =
    cong (quarter +_) (negAdd quarter quarter)
    ∙ addAssoc quarter (- quarter) (- quarter)
    ∙ cong (_+ (- quarter)) (addInvR quarter)
    ∙ addIdL (- quarter)


opaque
  quarterReflectionInvolutive : ∀ quarter x →
    quarter - (quarter - x) ≡ x
  quarterReflectionInvolutive quarter x =
    cong (quarter +_)
      (negAdd quarter (- x) ∙ cong ((- quarter) +_) (negInvol x))
    ∙ addAssoc quarter (- quarter) x
    ∙ cong (_+ x) (addInvR quarter)
    ∙ addIdL x

  cosineToSineInterval : ∀ quarter →
    CosineHalfInterval quarter → SineQuarterInterval quarter
  cosineToSineInterval quarter (x , zero≤x , x≤half) =
    (quarter - x)
    , subst (_≤ℝ quarter - x) (reflectionAtHalfTurn quarter)
        (addPres≤L (- halfTurn quarter) (- x) quarter
          (negPres≤ x (halfTurn quarter) x≤half))
    , subst (quarter - x ≤ℝ_) (subZero quarter)
        (addPres≤L (- x) (- 0ℝ) quarter (negPres≤ 0ℝ x zero≤x))

  cosineToSineInterval-value : ∀ quarter point →
    fst (cosineToSineInterval quarter point) ≡ quarter + (- fst point)
  cosineToSineInterval-value quarter point = refl

  sineToCosineInterval : ∀ quarter →
    SineQuarterInterval quarter → CosineHalfInterval quarter
  sineToCosineInterval quarter (x , negative≤x , x≤quarter) =
    (quarter - x)
    , nonnegativeSub x quarter x≤quarter
    , subst (quarter - x ≤ℝ_) (cong (quarter +_) (negInvol quarter))
        (addPres≤L (- x) (- (- quarter)) quarter
          (negPres≤ (- quarter) x negative≤x))

  sineToCosineInterval-value : ∀ quarter point →
    fst (sineToCosineInterval quarter point) ≡ quarter - fst point
  sineToCosineInterval-value quarter point = refl

  cosineToSine-sineToCosine : ∀ quarter point →
    cosineToSineInterval quarter (sineToCosineInterval quarter point) ≡ point
  cosineToSine-sineToCosine quarter point =
    Σ≡Prop (isPropClosedIntervalMembership (- quarter) quarter)
      (quarterReflectionInvolutive quarter (fst point))
  sineToCosine-cosineToSine : ∀ quarter point →
    sineToCosineInterval quarter (cosineToSineInterval quarter point) ≡ point
  sineToCosine-cosineToSine quarter point =
    Σ≡Prop (isPropClosedIntervalMembership 0ℝ (halfTurn quarter))
      (quarterReflectionInvolutive quarter (fst point))


cosineSineIntervalIso : ∀ quarter →
  Iso (CosineHalfInterval quarter) (SineQuarterInterval quarter)
cosineSineIntervalIso quarter .Iso.fun = cosineToSineInterval quarter
cosineSineIntervalIso quarter .Iso.inv = sineToCosineInterval quarter
cosineSineIntervalIso quarter .Iso.sec = cosineToSine-sineToCosine quarter
cosineSineIntervalIso quarter .Iso.ret = sineToCosine-cosineToSine quarter


cosineSineIntervalEquiv : ∀ quarter →
  CosineHalfInterval quarter ≃ SineQuarterInterval quarter
cosineSineIntervalEquiv quarter = isoToEquiv (cosineSineIntervalIso quarter)
