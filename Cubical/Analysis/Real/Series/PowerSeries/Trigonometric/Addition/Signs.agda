module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Signs where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients


private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- The addition law for the two four-periodic masks is independent of
-- factorial coefficients and convergence.  Proving it over the rationals
-- makes its later transport to the reals exact.

trigonometricRationalSign-addition : ∀ left right →
  ( sineRationalSign left ℚ.· cosineRationalSign right ℚ.+
      cosineRationalSign left ℚ.· sineRationalSign right
      ≡ sineRationalSign (left ℕ.+ right))
  ×
  ( cosineRationalSign left ℚ.· cosineRationalSign right ℚ.+
      ℚ.- (sineRationalSign left ℚ.· sineRationalSign right)
      ≡ cosineRationalSign (left ℕ.+ right))
trigonometricRationalSign-addition zero right =
  ( cong₂ ℚ._+_
      (ℚRing.0LeftAnnihilates (cosineRationalSign right))
      (ℚ.·IdL (sineRationalSign right))
    ∙ ℚ.+IdL (sineRationalSign right)
  , cong₂ ℚ._+_
      (ℚ.·IdL (cosineRationalSign right))
      (cong ℚ.-_ (ℚRing.0LeftAnnihilates (sineRationalSign right)))
    ∙ cong (cosineRationalSign right ℚ.+_) ℚRing.0Selfinverse
    ∙ ℚ.+IdR (cosineRationalSign right)
  )
trigonometricRationalSign-addition (suc left) right =
  ( cong
      (cosineRationalSign left ℚ.· cosineRationalSign right ℚ.+_)
      (ℚRing.-DistL·
        (sineRationalSign left) (sineRationalSign right))
    ∙ snd induction
  , cong
      (ℚ._+ ℚ.-
        (cosineRationalSign left ℚ.· sineRationalSign right))
      (ℚRing.-DistL·
        (sineRationalSign left) (cosineRationalSign right))
    ∙ ℚRing.-Dist
        (sineRationalSign left ℚ.· cosineRationalSign right)
        (cosineRationalSign left ℚ.· sineRationalSign right)
    ∙ cong ℚ.-_ (fst induction)
  )
  where
  induction = trigonometricRationalSign-addition left right


sineSign cosineSign : ℕ → ℝ
sineSign n = rat (sineRationalSign n)
cosineSign n = rat (cosineRationalSign n)


sineCoefficient-as-sign : ∀ n →
  sineCoefficients n ≡ sineSign n · exponentialCoefficients n
sineCoefficient-as-sign n =
  sym
    (mul-rat
      (sineRationalSign n)
      (exponentialRationalCoefficient n))


cosineCoefficient-as-sign : ∀ n →
  cosineCoefficients n ≡ cosineSign n · exponentialCoefficients n
cosineCoefficient-as-sign n =
  sym
    (mul-rat
      (cosineRationalSign n)
      (exponentialRationalCoefficient n))


trigonometricSign-addition : ∀ left right →
  ( sineSign left · cosineSign right +
      cosineSign left · sineSign right
      ≡ sineSign (left ℕ.+ right))
  ×
  ( cosineSign left · cosineSign right +
      - (sineSign left · sineSign right)
      ≡ cosineSign (left ℕ.+ right))
trigonometricSign-addition left right =
  ( cong₂ _+_
      (mul-rat
        (sineRationalSign left) (cosineRationalSign right))
      (mul-rat
        (cosineRationalSign left) (sineRationalSign right))
    ∙ rat+rat
        (sineRationalSign left ℚ.· cosineRationalSign right)
        (cosineRationalSign left ℚ.· sineRationalSign right)
    ∙ cong rat (fst rational-addition)
  , cong₂ _+_
      (mul-rat
        (cosineRationalSign left) (cosineRationalSign right))
      (cong -_
        (mul-rat
          (sineRationalSign left) (sineRationalSign right)))
    ∙ cong
        (rat
          (cosineRationalSign left ℚ.· cosineRationalSign right) +_)
        (neg-rat
          (sineRationalSign left ℚ.· sineRationalSign right))
    ∙ rat+rat
        (cosineRationalSign left ℚ.· cosineRationalSign right)
        (ℚ.- (sineRationalSign left ℚ.· sineRationalSign right))
    ∙ cong rat (snd rational-addition)
  )
  where
  rational-addition =
    trigonometricRationalSign-addition left right
