module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.HigherDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ)

open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol)
open import Cubical.Analysis.Real.Series.Base using (RealSequence)
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients


negativeCoefficients : RealSequence → RealSequence
negativeCoefficients coefficients n = - coefficients n


formalDerivative²-sineCoefficients :
  formalDerivative (formalDerivative sineCoefficients)
    ≡ negativeCoefficients sineCoefficients
formalDerivative²-sineCoefficients =
  cong formalDerivative formalDerivative-sineCoefficients
  ∙ formalDerivative-cosineCoefficients


formalDerivative²-cosineCoefficients :
  formalDerivative (formalDerivative cosineCoefficients)
    ≡ negativeCoefficients cosineCoefficients
formalDerivative²-cosineCoefficients =
  cong formalDerivative formalDerivative-cosineCoefficients
  ∙ formalDerivative-neg sineCoefficients
  ∙ cong negativeCoefficients formalDerivative-sineCoefficients


formalDerivative⁴-sineCoefficients :
  formalDerivative
    (formalDerivative
      (formalDerivative
        (formalDerivative sineCoefficients)))
    ≡ sineCoefficients
formalDerivative⁴-sineCoefficients =
  cong
    (λ (coefficients : RealSequence) →
      repeatedFormalDerivative 2 coefficients)
    formalDerivative²-sineCoefficients
  ∙ repeatedFormalDerivative-neg 2 sineCoefficients
  ∙ cong negativeCoefficients formalDerivative²-sineCoefficients
  ∙ funExt (λ n → negInvol (sineCoefficients n))


formalDerivative⁴-cosineCoefficients :
  formalDerivative
    (formalDerivative
      (formalDerivative
        (formalDerivative cosineCoefficients)))
    ≡ cosineCoefficients
formalDerivative⁴-cosineCoefficients =
  cong
    (λ (coefficients : RealSequence) →
      repeatedFormalDerivative 2 coefficients)
    formalDerivative²-cosineCoefficients
  ∙ repeatedFormalDerivative-neg 2 cosineCoefficients
  ∙ cong negativeCoefficients formalDerivative²-cosineCoefficients
  ∙ funExt (λ n → negInvol (cosineCoefficients n))


repeatedFormalDerivative-sine-two :
  repeatedFormalDerivative 2 sineCoefficients
    ≡ negativeCoefficients sineCoefficients
repeatedFormalDerivative-sine-two =
  formalDerivative²-sineCoefficients


repeatedFormalDerivative-cosine-two :
  repeatedFormalDerivative 2 cosineCoefficients
    ≡ negativeCoefficients cosineCoefficients
repeatedFormalDerivative-cosine-two =
  formalDerivative²-cosineCoefficients


repeatedFormalDerivative-sine-four :
  repeatedFormalDerivative 4 sineCoefficients ≡ sineCoefficients
repeatedFormalDerivative-sine-four =
  formalDerivative⁴-sineCoefficients


repeatedFormalDerivative-cosine-four :
  repeatedFormalDerivative 4 cosineCoefficients ≡ cosineCoefficients
repeatedFormalDerivative-cosine-four =
  formalDerivative⁴-cosineCoefficients


repeatedFormalDerivative-sine-addFour : ∀ order →
  repeatedFormalDerivative (4 ℕ.+ order) sineCoefficients ≡
  repeatedFormalDerivative order sineCoefficients
repeatedFormalDerivative-sine-addFour order =
  cong
    (λ total → repeatedFormalDerivative total sineCoefficients)
    (ℕ.+-comm 4 order)
  ∙ repeatedFormalDerivative-addIterations
      order 4 sineCoefficients
  ∙ cong
      (repeatedFormalDerivative order)
      repeatedFormalDerivative-sine-four


repeatedFormalDerivative-cosine-addFour : ∀ order →
  repeatedFormalDerivative (4 ℕ.+ order) cosineCoefficients ≡
  repeatedFormalDerivative order cosineCoefficients
repeatedFormalDerivative-cosine-addFour order =
  cong
    (λ total → repeatedFormalDerivative total cosineCoefficients)
    (ℕ.+-comm 4 order)
  ∙ repeatedFormalDerivative-addIterations
      order 4 cosineCoefficients
  ∙ cong
      (repeatedFormalDerivative order)
      repeatedFormalDerivative-cosine-four
