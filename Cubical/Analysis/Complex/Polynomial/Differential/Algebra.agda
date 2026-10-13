module Cubical.Analysis.Complex.Polynomial.Differential.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition

module Differential {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open PolynomialDefinition.Polynomials R
  private A = fst R

  -- Horner differentiation needs neither natural-number division nor a
  -- decision whether a coefficient is zero.
  differentiate : List A → List A
  differentiate [] = []
  differentiate (a ∷ p) = addCoefficients p (0r ∷ differentiate p)

  derivativeValue : List A → A → A
  derivativeValue [] z = 0r
  derivativeValue (a ∷ p) z = evaluate p z + z · derivativeValue p z

  evaluate-differentiate : ∀ p z →
    evaluate (differentiate p) z ≡ derivativeValue p z
  evaluate-differentiate [] z = refl
  evaluate-differentiate (a ∷ p) z =
    evaluate-add p (0r ∷ differentiate p) z
    ∙ cong (evaluate p z +_) (+IdL (z · evaluate (differentiate p) z))
    ∙ cong (λ d → evaluate p z + z · d) (evaluate-differentiate p z)

  dividedDifference-diagonal : ∀ p r →
    evaluate (quotientAt p r) r ≡ derivativeValue p r
  dividedDifference-diagonal [] r = refl
  dividedDifference-diagonal (a ∷ p) r =
    cong (λ d → evaluate p r + r · d) (dividedDifference-diagonal p r)

  quadraticRemainder : List A → A → List A
  quadraticRemainder p r = quotientAt (quotientAt p r) r

  -- An exact, division-free Taylor identity. The remainder is a polynomial,
  -- so its bounds and continuity can use the ordinary Horner interfaces.
  taylorIdentity : ∀ p r z → evaluate p z ≡
    evaluate p r + (z - r) ·
      (derivativeValue p r + (z - r) · evaluate (quadraticRemainder p r) z)
  taylorIdentity p r z = divisionIdentity p r z
    ∙ cong (λ d → evaluate p r + (z - r) · d)
      (divisionIdentity (quotientAt p r) r z
      ∙ cong (_+ (z - r) · evaluate (quadraticRemainder p r) z)
        (dividedDifference-diagonal p r))

  translate : List A → A → List A
  translate [] r = []
  translate (a ∷ p) r = addCoefficients (a ∷ [])
    (multiplyCoefficients (r ∷ 1r ∷ []) (translate p r))

  private
    constantValue : ∀ a z → evaluate (a ∷ []) z ≡ a
    constantValue a z = solve! R

    linearValue : ∀ r z → evaluate (r ∷ 1r ∷ []) z ≡ r + z
    linearValue r z = solve! R

  evaluate-translate : ∀ p r z → evaluate (translate p r) z ≡ evaluate p (r + z)
  evaluate-translate [] r z = refl
  evaluate-translate (a ∷ p) r z =
    evaluate-add (a ∷ []) (multiplyCoefficients (r ∷ 1r ∷ []) (translate p r)) z
    ∙ cong₂ _+_ (constantValue a z)
      (evaluate-multiply (r ∷ 1r ∷ []) (translate p r) z
      ∙ cong₂ _·_ (linearValue r z) (evaluate-translate p r z))

  centeredRemainder : List A → A → List A
  centeredRemainder p r = translate (quadraticRemainder p r) r

  private
    offset : ∀ r u → (r + u) - r ≡ u
    offset r u = solve! R

  centeredTaylorIdentity : ∀ p r u → evaluate p (r + u) ≡
    evaluate p r + u · (derivativeValue p r + u · evaluate (centeredRemainder p r) u)
  centeredTaylorIdentity p r u = taylorIdentity p r (r + u)
    ∙ cong₂ (λ d v → evaluate p r + d · (derivativeValue p r + d · v))
      (offset r u) (sym (evaluate-translate (quadraticRemainder p r) r u))
