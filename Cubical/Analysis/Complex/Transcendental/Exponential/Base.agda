module Cubical.Analysis.Complex.Transcendental.Exponential.Base where

-- Define the complex exponential using the established native real functions.
-- No new series completion or choice of an argument is involved.
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.Cis.Properties
import Cubical.Analysis.Complex.Polar.Algebra as PolarAlgebra

private
  module C = CommRingTheory ℂCommRing
  module A = PolarAlgebra.PolarAlgebra ℝCommRing

  -- Keep the existing real series value opaque while checking coordinate
  -- algebra. These laws are aliases of the native exponential API.
  opaque
    realExp : ℝ → ℝ
    realExp = expℝ

    realExp-value : ∀ x → realExp x ≡ expℝ x
    realExp-value x = refl

    realExp-positive-value : ∀ x → realExp x ≡ fst (expPositive x)
    realExp-positive-value x = sym (expPositive-value x)

    realExp-zero : realExp 0ℝ ≡ 1ℝ
    realExp-zero = exponentialEntireValue-zero

    realExp-add : ∀ x y → realExp (x + y) ≡ realExp x · realExp y
    realExp-add = exponentialEntireValue-add

  conjugate-real : ∀ x → conjugate (fromℝ x) ≡ fromℝ x
  conjugate-real x = ℂ≡ refl negZero

  imaginary-real : ∀ θ → iℂ ·ℂ fromℝ θ ≡ (0ℝ , θ)
  imaginary-real θ = A.quarterRotate θ 0ℝ ∙ ℂ≡ negZero refl

opaque
  expℂ : ℂ → ℂ
  expℂ z = polarℂ (realExp (re z)) (im z)

  expℂ-polar : ∀ z → expℂ z ≡ polarℂ (expℝ (re z)) (im z)
  expℂ-polar z = cong (λ r → polarℂ r (im z)) (realExp-value (re z))

  -- A second value equation stays within the opaque positive-real API,
  -- useful when composing with the already constructed real logarithm.
  expℂ-positivePolar : ∀ x θ → expℂ (x , θ) ≡ polarℂ (fst (expPositive x)) θ
  expℂ-positivePolar x θ = cong (λ r → polarℂ r θ) (realExp-positive-value x)

  expℂ-zero : expℂ 0ℂ ≡ 1ℂ
  expℂ-zero = cong₂ _·ℂ_ (cong fromℝ realExp-zero) cisℝ-zero
    ∙ ·ℂIdR 1ℂ

  expℂ-add : ∀ z w → expℂ (z +ℂ w) ≡ expℂ z ·ℂ expℂ w
  expℂ-add z w = cong₂ _·ℂ_
    (cong fromℝ (realExp-add (re z) (re w))
      ∙ fromℝ-pres· (realExp (re z)) (realExp (re w)))
    (cisℝ-add (im z) (im w))
    ∙ C.·CommAssocSwap (fromℝ (realExp (re z))) (fromℝ (realExp (re w)))
      (cisℝ (im z)) (cisℝ (im w))

  expℂ-fromℝ : ∀ x → expℂ (fromℝ x) ≡ fromℝ (expℝ x)
  expℂ-fromℝ x = cong (fromℝ (realExp x) ·ℂ_) cisℝ-zero
    ∙ ·ℂIdR (fromℝ (realExp x)) ∙ cong fromℝ (realExp-value x)

  expℂ-imaginary : ∀ θ → expℂ (0ℝ , θ) ≡ cisℝ θ
  expℂ-imaginary θ = cong (λ r → fromℝ r ·ℂ cisℝ θ) realExp-zero
    ∙ CommRingStr.·IdL (snd ℂCommRing) (cisℝ θ)

  expℂ-conjugate : ∀ z → expℂ (conjugate z) ≡ conjugate (expℂ z)
  expℂ-conjugate z = cong (fromℝ (realExp (re z)) ·ℂ_) (cisℝ-neg (im z))
    ∙ cong (_·ℂ conjugate (cisℝ (im z))) (sym (conjugate-real (realExp (re z))))
    ∙ sym (conjugate-pres· (fromℝ (realExp (re z))) (cisℝ (im z)))

opaque
  expℂ-euler : ∀ θ → expℂ (iℂ ·ℂ fromℝ θ) ≡ cisℝ θ
  expℂ-euler θ = cong expℂ (imaginary-real θ)
    ∙ expℂ-imaginary θ

  expℂ-neg-inverse : ∀ z → expℂ z ·ℂ expℂ (-ℂ z) ≡ 1ℂ
  expℂ-neg-inverse z = sym (expℂ-add z (-ℂ z))
    ∙ cong expℂ (+ℂInvR z) ∙ expℂ-zero
