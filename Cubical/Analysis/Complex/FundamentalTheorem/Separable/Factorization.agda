module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Factorization where

-- Finite exact deflation preserves the formal certificate. At each step
-- its inverse identity also makes the new root apart from every remaining
-- root, so the conclusion includes the surveyed positive separation.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.FinData as F
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as ⊥
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Inverse.Bounds
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
import Cubical.Analysis.Complex.Polynomial.Monic.FactorsAlgebra as FactorsDefinition
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Certificate
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Root
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Deflation

private
  module C = FactorsDefinition.Factors ℂCommRing

  opaque
    productUnit-apart : ∀ {n} (roots : Vec ℂ n) r inverse →
      inverse ·ℂ productOfLinearFactors roots r ≡ 1ℂ →
      (i : F.Fin n) → 0ℝ <ℝ modulusℂ (r -ℂ lookup i roots)
    productUnit-apart roots r inverse unit i =
      unit→modulusPositiveℂ (r -ℂ lookup i roots) (C.remainingProduct roots i r ·ℂ inverse)
        (·ℂAssoc (r -ℂ lookup i roots) (C.remainingProduct roots i r) inverse
          ∙ cong (_·ℂ inverse) (sym (C.product-factor roots i r))
          ∙ ·ℂComm (productOfLinearFactors roots r) inverse ∙ unit)

    apart-cons : ∀ {n} r (roots : Vec ℂ n) → PairwiseApartRoots roots →
      ((i : F.Fin n) → 0ℝ <ℝ modulusℂ (r -ℂ lookup i roots)) → PairwiseApartRoots (r ∷ roots)
    apart-cons r roots apart separated F.zero F.zero unequal = ⊥.rec (unequal refl)
    apart-cons r roots apart separated F.zero (F.suc j) unequal = separated j
    apart-cons r roots apart separated (F.suc i) F.zero unequal =
      subst (0ℝ <ℝ_) (sym (cong modulusℂ (C.opposite (lookup i roots) r)
        ∙ modulusℂ-neg (r -ℂ lookup i roots))) (separated i)
    apart-cons r roots apart separated (F.suc i) (F.suc j) unequal =
      apart i j (λ equal → unequal (cong F.suc equal))

  opaque
    factorCertificate : (n : ℕ) (p : MonicPolynomial n) → BezoutSeparability p → SeparableExactFactorization p
    factorCertificate zero [] certificate = PT.∣ [] , refl , (λ ()) ∣₁
    factorCertificate (suc n) p certificate = PT.rec PT.squash₁ deflate
      (stronglySeparableRootExistence n p PT.∣ certificate ∣₁)
      where
      deflate : ExactRootData p → SeparableExactFactorization p
      deflate (r , root) = PT.map assemble
        (factorCertificate n (quotientMonic p r) (separableDeflation n p r root certificate))
        where
        inverse : ℂ
        inverse = evaluatePolynomialℂ (BezoutSeparability.bezoutT certificate) r

        assemble : (Σ[ roots ∈ Vec ℂ n ]
          ((linearFactors roots ≡ quotientMonic p r) × PairwiseApartRoots roots)) →
          Σ[ roots ∈ Vec ℂ (suc n) ] ((linearFactors roots ≡ p) × PairwiseApartRoots roots)
        assemble (roots , factorization , apart) = r ∷ roots ,
          (cong (multiplyLinear r) factorization ∙ sym (factorMonicAtRoot p r root)) ,
          apart-cons r roots apart (productUnit-apart roots r inverse unit)
          where
          unit : inverse ·ℂ productOfLinearFactors roots r ≡ 1ℂ
          unit = cong (inverse ·ℂ_)
            (sym (evaluate-linearFactors roots r)
              ∙ cong (λ q → evaluateMonic q r) factorization
              ∙ sym (derivative-atRoot p r root))
            ∙ bezoutSeparability-inverseAtRoot p certificate r root

stronglySeparableFundamentalTheorem : StronglySeparableFundamentalTheorem
stronglySeparableFundamentalTheorem n p = PT.rec PT.squash₁ (factorCertificate n p)
