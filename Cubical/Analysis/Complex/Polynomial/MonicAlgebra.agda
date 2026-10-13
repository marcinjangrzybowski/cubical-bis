module Cubical.Analysis.Complex.Polynomial.MonicAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.BigOps as BigOps
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition

module Monic {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private
    A = fst R
    module I = IdentitiesDefinition.Identities R

  -- The leading coefficient 1 is implicit; every stored coefficient is
  -- meaningful and the formal degree is available without zero tests.
  MonicPolynomial : ℕ → Type ℓ
  MonicPolynomial n = Vec A n

  evaluateMonic : ∀ {n} → MonicPolynomial n → A → A
  evaluateMonic [] z = 1r
  evaluateMonic (a ∷ p) z = a + z · evaluateMonic p z

  addConstant : ∀ {n} → A → MonicPolynomial (suc n) → MonicPolynomial (suc n)
  addConstant a (b ∷ p) = (a + b) ∷ p

  evaluate-addConstant : ∀ {n} a (p : MonicPolynomial (suc n)) z →
    evaluateMonic (addConstant a p) z ≡ a + evaluateMonic p z
  evaluate-addConstant a (b ∷ p) z = sym (+Assoc a b (z · evaluateMonic p z))

  multiplyLinear : ∀ {n} → A → MonicPolynomial n → MonicPolynomial (suc n)
  multiplyLinear r [] = (- r) ∷ []
  multiplyLinear r (a ∷ p) = ((- r) · a) ∷ addConstant a (multiplyLinear r p)

  evaluate-multiplyLinear : ∀ {n} r (p : MonicPolynomial n) z →
    evaluateMonic (multiplyLinear r p) z ≡ (z - r) · evaluateMonic p z
  evaluate-multiplyLinear r [] z = solve! R
  evaluate-multiplyLinear r (a ∷ p) z =
    cong (λ t → (- r) · a + z · t)
      (evaluate-addConstant a (multiplyLinear r p) z
      ∙ cong (a +_) (evaluate-multiplyLinear r p z))
    ∙ I.linearStep a r z (evaluateMonic p z)

  linearFactors : ∀ {n} → Vec A n → MonicPolynomial n
  linearFactors [] = []
  linearFactors (r ∷ roots) = multiplyLinear r (linearFactors roots)

  productOfLinearFactors : ∀ {n} → Vec A n → A → A
  productOfLinearFactors roots z =
    BigOps.Product.∏ (CommRing→Ring R) (λ i → z - lookup i roots)

  evaluate-linearFactors : ∀ {n} (roots : Vec A n) z →
    evaluateMonic (linearFactors roots) z ≡ productOfLinearFactors roots z
  evaluate-linearFactors [] z = refl
  evaluate-linearFactors (r ∷ roots) z = evaluate-multiplyLinear r (linearFactors roots) z
    ∙ cong ((z - r) ·_) (evaluate-linearFactors roots z)

  quotientMonic : ∀ {n} → MonicPolynomial (suc n) → A → MonicPolynomial n
  quotientMonic (a ∷ []) r = []
  quotientMonic (a ∷ b ∷ p) r = evaluateMonic (b ∷ p) r ∷ quotientMonic (b ∷ p) r

  private
    reconstructionHead : ∀ a r b → a ≡ (a + r · b) + (- r) · b
    reconstructionHead a r b = solve! R

  reconstructMonic : ∀ {n} (p : MonicPolynomial (suc n)) r →
    p ≡ addConstant (evaluateMonic p r) (multiplyLinear r (quotientMonic p r))
  reconstructMonic (a ∷ []) r = cong (_∷ []) (solve! R)
  reconstructMonic (a ∷ b ∷ p) r = cong₂ _∷_
    (reconstructionHead a r (evaluateMonic (b ∷ p) r)) (reconstructMonic (b ∷ p) r)

  factorMonicAtRoot : ∀ {n} (p : MonicPolynomial (suc n)) r → evaluateMonic p r ≡ 0r →
    p ≡ multiplyLinear r (quotientMonic p r)
  factorMonicAtRoot p r root = reconstructMonic p r
    ∙ cong (λ a → addConstant a (multiplyLinear r (quotientMonic p r))) root
    ∙ addZeroConstant (multiplyLinear r (quotientMonic p r))
    where
    addZeroConstant : ∀ {n} (q : MonicPolynomial (suc n)) → addConstant 0r q ≡ q
    addZeroConstant (b ∷ q) = cong (_∷ q) (+IdL b)
