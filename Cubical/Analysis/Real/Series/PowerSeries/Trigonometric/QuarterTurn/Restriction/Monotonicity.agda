module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Monotonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Functions.Embedding

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Domain.Interval
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity


SineQuarterStrictlyIncreasing : ℝ → Type₀
SineQuarterStrictlyIncreasing quarter =
  ∀ (left right : SineQuarterInterval quarter) →
    fst left <ℝ fst right →
    sinℝ (fst left) <ℝ sinℝ (fst right)


private
  opaque
    strictAndEqualImpossible : ∀ left right →
      left <ℝ right → left ≡ right → ⊥
    strictAndEqualImpossible left right =
      <ℝ→≢ left right


opaque
  restrictedSine-injectiveFromStrictIncrease : ∀ quarter →
    SineQuarterStrictlyIncreasing quarter →
    ∀ (left right : SineQuarterInterval quarter) →
    restrictedSine quarter left ≡ restrictedSine quarter right →
    left ≡ right
  restrictedSine-injectiveFromStrictIncrease
      quarter strictly-increasing left right image-path =
    Σ≡Prop
      (isPropClosedIntervalMembership (- quarter) quarter)
      (≤ℝ-antisym (fst left) (fst right) left≤right right≤left)
    where
    sine-values-equal : sinℝ (fst left) ≡ sinℝ (fst right)
    sine-values-equal =
      sym (restrictedSine-value quarter left)
      ∙ cong fst image-path
      ∙ restrictedSine-value quarter right

    left≤right : fst left ≤ℝ fst right
    left≤right =
      notGreater→≤ℝ (fst left) (fst right) λ right<left →
        strictAndEqualImpossible
          (sinℝ (fst right)) (sinℝ (fst left))
          (strictly-increasing right left right<left)
          (sym sine-values-equal)

    right≤left : fst right ≤ℝ fst left
    right≤left =
      notGreater→≤ℝ (fst right) (fst left) λ left<right →
        strictAndEqualImpossible
          (sinℝ (fst left)) (sinℝ (fst right))
          (strictly-increasing left right left<right)
          sine-values-equal


restrictedSine-isEmbeddingFromStrictIncrease : ∀ quarter →
  SineQuarterStrictlyIncreasing quarter →
  isEmbedding (restrictedSine quarter)
restrictedSine-isEmbeddingFromStrictIncrease quarter strictly-increasing =
  injEmbedding
    (isSetClosedInterval (- 1ℝ) 1ℝ)
    (λ {left} {right} →
      restrictedSine-injectiveFromStrictIncrease
        quarter strictly-increasing left right)


restrictedSine-strictlyIncreasing : ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  SineQuarterStrictlyIncreasing quarter
restrictedSine-strictlyIncreasing =
  sinℝ-strictMonotone-on-quarterInterval


restrictedSine-injective : ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  ∀ (left right : SineQuarterInterval quarter) →
  restrictedSine quarter left ≡ restrictedSine quarter right →
  left ≡ right
restrictedSine-injective
    quarter positive-quarter characterization =
  restrictedSine-injectiveFromStrictIncrease quarter
    (restrictedSine-strictlyIncreasing
      quarter positive-quarter characterization)


restrictedSine-isEmbedding : ∀ quarter →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  isEmbedding (restrictedSine quarter)
restrictedSine-isEmbedding
    quarter positive-quarter characterization =
  restrictedSine-isEmbeddingFromStrictIncrease quarter
    (restrictedSine-strictlyIncreasing
      quarter positive-quarter characterization)
