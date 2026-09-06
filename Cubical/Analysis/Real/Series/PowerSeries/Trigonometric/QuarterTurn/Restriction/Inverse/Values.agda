module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Values where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.OrderedCommRing

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Inverse


-- Negation preserves both closed symmetric domains.  These operations retain
-- the domain witnesses, so parity statements do not require callers to rebuild
-- interval membership proofs.
sineQuarterNegate : ∀ quarter →
  SineQuarterInterval quarter → SineQuarterInterval quarter
sineQuarterNegate quarter (x , lower , upper) =
  (- x)
  , negPres≤ x quarter upper
  , subst ((- x) ≤ℝ_) (negInvol quarter)
      (negPres≤ (- quarter) x lower)

sineUnitNegate : SineUnitInterval → SineUnitInterval
sineUnitNegate = sineQuarterNegate 1ℝ

sineQuarterZero : ∀ quarter → 0ℝ ≤ℝ quarter → SineQuarterInterval quarter
sineQuarterZero quarter nonnegative =
  0ℝ
  , subst ((- quarter) ≤ℝ_) negZero
      (negPres≤ 0ℝ quarter nonnegative)
  , nonnegative

sineUnitZero : SineUnitInterval
sineUnitZero =
  sineQuarterZero 1ℝ
    (<ℝ-weaken 0ℝ 1ℝ (isOrderedCommRingℝ .IsOrderedCommRing.0<1))


opaque
  restrictedArcSin-zero : ∀ quarter → 0ℝ ≤ℝ quarter → ∀ equivalent →
    fst (restrictedArcSin quarter equivalent sineUnitZero) ≡ 0ℝ
  restrictedArcSin-zero quarter nonnegative equivalent =
    cong {x = restrictedArcSin quarter equivalent sineUnitZero}
      {y = sineQuarterZero quarter nonnegative} fst
      (restrictedArcSin-unique quarter equivalent sineUnitZero
        (sineQuarterZero quarter nonnegative)
        (subst (λ x → sinℝ x ≡ 0ℝ) (sym coordinate) sinℝ-zero))
    ∙ coordinate
    where
    coordinate : fst (sineQuarterZero quarter nonnegative) ≡ 0ℝ
    coordinate = refl

  restrictedArcCos-zero : ∀ quarter → 0ℝ ≤ℝ quarter → ∀ equivalent →
    fst (restrictedArcCos quarter equivalent sineUnitZero) ≡ quarter
  restrictedArcCos-zero quarter nonnegative equivalent =
    restrictedArcCos-value quarter equivalent sineUnitZero
    ∙ cong (λ x → quarter - x)
        (restrictedArcSin-zero quarter nonnegative equivalent)
    ∙ subZero quarter

  restrictedArcSin-odd : ∀ quarter equivalent value →
    fst (restrictedArcSin quarter equivalent (sineUnitNegate value)) ≡
    - fst (restrictedArcSin quarter equivalent value)
  restrictedArcSin-odd quarter equivalent value =
    cong {x = restrictedArcSin quarter equivalent (sineUnitNegate value)}
      {y = sineQuarterNegate quarter (restrictedArcSin quarter equivalent value)} fst
      (restrictedArcSin-unique quarter equivalent (sineUnitNegate value)
        (sineQuarterNegate quarter (restrictedArcSin quarter equivalent value))
        (subst (λ x → sinℝ x ≡ - fst value) (sym coordinate)
          (sinℝ-neg (fst (restrictedArcSin quarter equivalent value))
          ∙ cong -_ (sinℝ-restrictedArcSin quarter equivalent value))))
    ∙ coordinate
    where
    coordinate :
      fst (sineQuarterNegate quarter (restrictedArcSin quarter equivalent value)) ≡
      - fst (restrictedArcSin quarter equivalent value)
    coordinate = refl


private
  opaque
    reflectedNegation : ∀ quarter x →
      quarter - (- x) ≡ halfTurn quarter - (quarter - x)
    reflectedNegation quarter x =
      cong (quarter +_) (negInvol x)
      ∙ sym
          (cong ((quarter + quarter) +_) (negAdd quarter (- x)
            ∙ cong ((- quarter) +_) (negInvol x))
          ∙ addAssoc (quarter + quarter) (- quarter) x
          ∙ cong (_+ x)
              (sym (addAssoc quarter quarter (- quarter))
              ∙ cong (quarter +_) (addInvR quarter)
              ∙ addIdR quarter))


opaque
  restrictedArcCos-negate : ∀ quarter equivalent value →
    fst (restrictedArcCos quarter equivalent (sineUnitNegate value)) ≡
    halfTurn quarter - fst (restrictedArcCos quarter equivalent value)
  restrictedArcCos-negate quarter equivalent value =
    restrictedArcCos-value quarter equivalent (sineUnitNegate value)
    ∙ cong (λ x → quarter - x)
        (restrictedArcSin-odd quarter equivalent value)
    ∙ reflectedNegation quarter
        (fst (restrictedArcSin quarter equivalent value))
    ∙ cong (λ x → halfTurn quarter - x)
        (sym (restrictedArcCos-value quarter equivalent value))
