module Cubical.Analysis.Complex.Polynomial.Monic.PermutationAlgebra where

-- Equalities here concern the stored coefficients, not merely evaluation.
-- Moving one root to the front preserves every coefficient and its
-- multiplicity, even when roots coincide.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; equivFun)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; drop)
open import Cubical.Algebra.CommRing
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition
import Cubical.Analysis.Complex.Polynomial.Formal as FormalDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra as DifferentialDefinition
import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PolynomialAlgebra as CertificatesDefinition
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Finite

module Permutation {ℓ} (R : CommRing ℓ) where
  open MonicDefinition.Monic R
  open DifferentialDefinition.MonicDifferential R using (monicCoefficients)
  private
    A = fst R
    module F = FormalDefinition.Formal R
    module C = CertificatesDefinition.Certificates R
    module P = CommRingStr (snd F.polynomialRing)

    coefficients-injective : ∀ {n} (p q : MonicPolynomial n) →
      C.PolynomialIdentity (monicCoefficients p) (monicCoefficients q) → p ≡ q
    coefficients-injective [] [] equal = refl
    coefficients-injective (a ∷ p) (b ∷ q) equal =
      cong₂ _∷_ (equal 0) (coefficients-injective p q (λ k → equal (suc k)))

    formal-injective : ∀ {n} (p q : MonicPolynomial n) → F.monicValue p ≡ F.monicValue q → p ≡ q
    formal-injective p q equal = coefficients-injective p q
      (F.decode-identity (monicCoefficients p) (monicCoefficients q)
        (F.encode-monic p ∙ equal ∙ sym (F.encode-monic q)))

  multiplyLinear-swap : ∀ {n} r s (p : MonicPolynomial n) →
    multiplyLinear r (multiplyLinear s p) ≡ multiplyLinear s (multiplyLinear r p)
  multiplyLinear-swap r s p = formal-injective _ _
    (F.monicValue-multiplyLinear r (multiplyLinear s p)
      ∙ cong (a P.·_) (F.monicValue-multiplyLinear s p)
      ∙ P.·Assoc a b (F.monicValue p)
      ∙ cong (P._· F.monicValue p) (P.·Comm a b)
      ∙ sym (P.·Assoc b a (F.monicValue p))
      ∙ cong (b P.·_) (sym (F.monicValue-multiplyLinear r p))
      ∙ sym (F.monicValue-multiplyLinear s (multiplyLinear r p)))
    where
    a = F.variablePolynomial P.- F.constant r
    b = F.variablePolynomial P.- F.constant s

  linearFactors-extract : ∀ {n} (roots : Vec A (suc n)) (i : Fin (suc n)) →
    linearFactors roots ≡ multiplyLinear (lookup i roots) (linearFactors (drop i roots))
  linearFactors-extract (r ∷ roots) zero = refl
  linearFactors-extract {n = suc n} (r ∷ roots) (suc i) =
    cong (multiplyLinear r) (linearFactors-extract roots i)
      ∙ multiplyLinear-swap r (lookup i roots) (linearFactors (drop i roots))

  linearFactors-permutation : ∀ {n} (roots roots′ : Vec A n) (σ : Fin n ≃ Fin n) →
    (∀ i → lookup i roots ≡ lookup (equivFun σ i) roots′) →
    linearFactors roots ≡ linearFactors roots′
  linearFactors-permutation [] [] σ equal = refl
  linearFactors-permutation (r ∷ roots) roots′ σ equal = cong₂ multiplyLinear
    (equal zero)
    (linearFactors-permutation roots (drop (equivFun σ zero) roots′)
      (removeMatchingPermutation σ)
      (λ i → equal (suc i) ∙ sym (removeMatching-lookup roots′ σ i)))
    ∙ sym (linearFactors-extract roots′ (equivFun σ zero))
