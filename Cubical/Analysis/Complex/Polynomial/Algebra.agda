module Cubical.Analysis.Complex.Polynomial.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_; map)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

module Polynomials {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private A = fst R

  evaluate : List A → A → A
  evaluate [] z = 0r
  evaluate (a ∷ coefficients) z = a + z · evaluate coefficients z

  addCoefficients : List A → List A → List A
  addCoefficients [] q = q
  addCoefficients (a ∷ p) [] = a ∷ p
  addCoefficients (a ∷ p) (b ∷ q) = (a + b) ∷ addCoefficients p q

  scaleCoefficients : A → List A → List A
  scaleCoefficients a = map (a ·_)

  multiplyCoefficients : List A → List A → List A
  multiplyCoefficients [] q = []
  multiplyCoefficients (a ∷ p) q =
    addCoefficients (scaleCoefficients a q) (0r ∷ multiplyCoefficients p q)

  private
    addHorner : ∀ a b x p q → (a + b) + x · (p + q) ≡ (a + x · p) + (b + x · q)
    addHorner a b x p q = solve! R

    scaleHorner : ∀ a b x p → a · b + x · (a · p) ≡ a · (b + x · p)
    scaleHorner a b x p = solve! R

    multiplyHorner : ∀ a x p q → a · q + (0r + x · (p · q)) ≡ (a + x · p) · q
    multiplyHorner a x p q = solve! R

  evaluate-add : ∀ p q z → evaluate (addCoefficients p q) z ≡ evaluate p z + evaluate q z
  evaluate-add [] q z = sym (+IdL (evaluate q z))
  evaluate-add (a ∷ p) [] z = sym (+IdR (evaluate (a ∷ p) z))
  evaluate-add (a ∷ p) (b ∷ q) z =
    cong (λ t → (a + b) + z · t) (evaluate-add p q z)
    ∙ addHorner a b z (evaluate p z) (evaluate q z)

  evaluate-scale : ∀ a p z → evaluate (scaleCoefficients a p) z ≡ a · evaluate p z
  evaluate-scale a [] z = solve! R
  evaluate-scale a (b ∷ p) z =
    cong (λ t → a · b + z · t) (evaluate-scale a p z)
    ∙ scaleHorner a b z (evaluate p z)

  evaluate-multiply : ∀ p q z → evaluate (multiplyCoefficients p q) z ≡ evaluate p z · evaluate q z
  evaluate-multiply [] q z = solve! R
  evaluate-multiply (a ∷ p) q z =
    evaluate-add (scaleCoefficients a q) (0r ∷ multiplyCoefficients p q) z
    ∙ cong₂ _+_ (evaluate-scale a q z)
        (cong (λ t → 0r + z · t) (evaluate-multiply p q z))
    ∙ multiplyHorner a z (evaluate p z) (evaluate q z)

  -- Division by X-r is exact with an explicit remainder. A harmless final
  -- zero is retained, so no decidable equality on the coefficient ring is used.
  quotientAt : List A → A → List A
  quotientAt [] r = []
  quotientAt (a ∷ p) r = evaluate p r ∷ quotientAt p r

  private
    divisionStep : ∀ a x r b q →
      a + x · (b + (x - r) · q) ≡ (a + r · b) + (x - r) · (b + x · q)
    divisionStep a x r b q = solve! R

  divisionIdentity : ∀ p r z →
    evaluate p z ≡ evaluate p r + (z - r) · evaluate (quotientAt p r) z
  divisionIdentity [] r z = solve! R
  divisionIdentity (a ∷ p) r z =
    cong (λ t → a + z · t) (divisionIdentity p r z)
    ∙ divisionStep a z r (evaluate p r) (evaluate (quotientAt p r) z)

  factorAtRoot : ∀ p r → evaluate p r ≡ 0r → ∀ z →
    evaluate p z ≡ (z - r) · evaluate (quotientAt p r) z
  factorAtRoot p r root z = divisionIdentity p r z
    ∙ cong (_+ (z - r) · evaluate (quotientAt p r) z) root
    ∙ +IdL ((z - r) · evaluate (quotientAt p r) z)

  subtractVariable : List A → List A
  subtractVariable p = addCoefficients p (0r ∷ (- 1r) ∷ [])

  evaluate-subtractVariable : ∀ p z → evaluate (subtractVariable p) z ≡ evaluate p z - z
  evaluate-subtractVariable p z = evaluate-add p (0r ∷ (- 1r) ∷ []) z
    ∙ cong (evaluate p z +_) (solve! R)

  evaluate-quadratic : ∀ a b c z → evaluate (a ∷ b ∷ c ∷ []) z ≡ a + z · (b + z · c)
  evaluate-quadratic a b c z = solve! R
