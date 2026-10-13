module Cubical.Analysis.Complex.FundamentalTheorem.Matching.FactorContinuity where

-- Quantitative continuity of the product of linear factors on bounded
-- root configurations. The input matching is finite and may depend on the
-- requested radius; its permutation is eliminated only into a proposition.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_; equivFun)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; FinVec→Vec; FinVec→Vec→FinVec)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Metric
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
import Cubical.Analysis.Complex.Polynomial.Monic.PermutationAlgebra as PermutationDefinition
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients

private
  module C = PremetricStr (ℂPremetricSpace .snd)
  module P = PermutationDefinition.Permutation ℂCommRing

factorCoefficientBound : ℕ → ℚ₊ → ℚ₊
factorCoefficientBound zero B = 1
factorCoefficientBound (suc n) B = linearCoefficientBound n (factorCoefficientBound n B) B

factorCoefficientLipschitz : ℕ → ℚ₊ → ℚ₊
factorCoefficientLipschitz zero B = 1
factorCoefficientLipschitz (suc n) B =
  linearCoefficientLipschitz n (factorCoefficientBound n B) B ·₊ (1 +₊ factorCoefficientLipschitz n B)

opaque
  linearFactors-bound : ∀ {n} (roots : Vec ℂ n) B → RootsBounded roots B →
    CoefficientsBounded (linearFactors roots) (factorCoefficientBound n B)
  linearFactors-bound [] B bounded ()
  linearFactors-bound {n = suc n} (r ∷ roots) B bounded = multiplyLinear-bound r (linearFactors roots)
    (factorCoefficientBound n B) B (bounded zero) (linearFactors-bound roots B (λ i → bounded (suc i)))

  linearFactors-difference : ∀ {n} (roots roots′ : Vec ℂ n) B δ →
    0ℝ ≤ℝ δ → RootsBounded roots B → RootsBounded roots′ B →
    CoefficientDifferenceBound roots roots′ δ →
    CoefficientDifferenceBound (linearFactors roots) (linearFactors roots′)
      (⟦ factorCoefficientLipschitz n B ⟧₊ · δ)
  linearFactors-difference [] [] B δ nonnegative rb sb close ()
  linearFactors-difference {n = suc n} (r ∷ roots) (s ∷ roots′) B δ nonnegative rb sb close i =
    subst (normℂ (lookup i (multiplyLinear r (linearFactors roots)) -ℂ
      lookup i (multiplyLinear s (linearFactors roots′))) ≤ℝ_)
      (mulAssoc ⟦ K ⟧₊ ⟦ S ⟧₊ δ ∙ cong (_· δ) (mul-rat (fst K) (fst S)))
      (multiplyLinear-difference r s (linearFactors roots) (linearFactors roots′)
        (factorCoefficientBound n B) B (⟦ S ⟧₊ · δ) scaled-nonnegative (sb zero)
        (linearFactors-bound roots B (λ j → rb (suc j)))
        (≤ℝ-trans (normℂ (r -ℂ s)) δ (⟦ S ⟧₊ · δ) (close zero)
          (subst (_≤ℝ ⟦ S ⟧₊ · δ) (mulIdL δ)
            (mulPres≤R-0≤ 1ℝ ⟦ S ⟧₊ δ nonnegative (radius-sumL 1 L))))
        (coefficientDifference-monotone (linearFactors roots) (linearFactors roots′)
          (⟦ L ⟧₊ · δ) (⟦ S ⟧₊ · δ)
          (mulPres≤R-0≤ ⟦ L ⟧₊ ⟦ S ⟧₊ δ nonnegative (radius-sumR 1 L))
          (linearFactors-difference roots roots′ B δ nonnegative
            (λ j → rb (suc j)) (λ j → sb (suc j)) (λ j → close (suc j)))) i)
    where
    L K S : ℚ₊
    L = factorCoefficientLipschitz n B
    S = 1 +₊ L
    K = linearCoefficientLipschitz n (factorCoefficientBound n B) B
    scaled-nonnegative : 0ℝ ≤ℝ ⟦ S ⟧₊ · δ
    scaled-nonnegative = isNonnegative→0≤ (⟦ S ⟧₊ · δ)
      (mulPresIsNonnegative ⟦ S ⟧₊ δ (0≤→isNonnegative ⟦ S ⟧₊ (radius-nonnegative S))
        (0≤→isNonnegative δ nonnegative))

factorContinuityModulus : ℕ → ℚ₊ → ℚ₊ → ℚ₊
factorContinuityModulus n B ε = scaleTolerance (factorCoefficientLipschitz n B) ε

opaque
  factorContinuityEstimate : FactorContinuityEstimate factorContinuityModulus
  factorContinuityEstimate n B ε roots roots′ rb sb =
    PT.rec (isPropΠ λ i → C.isProp≈ (lookup i (linearFactors roots)) (lookup i (linearFactors roots′)) ε)
      (λ { (σ , close) → matched σ close })
    where
    δ : ℚ₊
    δ = factorContinuityModulus n B ε

    matched : (σ : Fin n ≃ Fin n) →
      (∀ i → lookup i roots ∼ℂ[ δ ] lookup (equivFun σ i) roots′) →
      CoefficientCloseness (linearFactors roots) ε (linearFactors roots′)
    matched σ close = subst (CoefficientCloseness (linearFactors roots) ε)
      (P.linearFactors-permutation reordered roots′ σ lookup-reordered)
      (λ i → scaledBound→closeness (factorCoefficientLipschitz n B) ε
        (lookup i (linearFactors roots)) (lookup i (linearFactors reordered)) (estimate i))
      where
      reordered : Vec ℂ n
      reordered = FinVec→Vec (λ i → lookup (equivFun σ i) roots′)
      lookup-reordered : ∀ i → lookup i reordered ≡ lookup (equivFun σ i) roots′
      lookup-reordered i = funExt⁻ (FinVec→Vec→FinVec (λ j → lookup (equivFun σ j) roots′)) i

      error-nonnegative : 0ℝ ≤ℝ ⟦ δ ⟧₊ + ⟦ δ ⟧₊
      error-nonnegative = subst (0ℝ ≤ℝ_) (sym (rat+rat (fst δ) (fst δ))) (radius-nonnegative (δ +₊ δ))

      estimate : CoefficientDifferenceBound (linearFactors roots) (linearFactors reordered)
        (⟦ factorCoefficientLipschitz n B ⟧₊ · (⟦ δ ⟧₊ + ⟦ δ ⟧₊))
      estimate = linearFactors-difference roots reordered B (⟦ δ ⟧₊ + ⟦ δ ⟧₊) error-nonnegative rb
        (λ i → subst (λ z → normℂ z ≤ℝ ⟦ B ⟧₊) (sym (lookup-reordered i)) (sb (equivFun σ i)))
        (λ i → <ℝ-weaken (normℂ (lookup i roots -ℂ lookup i reordered)) (⟦ δ ⟧₊ + ⟦ δ ⟧₊)
          (closeness→normℂ-difference< (lookup i roots) (lookup i reordered) δ
            (subst (lookup i roots ∼ℂ[ δ ]_) (sym (lookup-reordered i)) (close i))))

quantitativeFactorContinuity : QuantitativeFactorContinuity
quantitativeFactorContinuity = factorContinuityModulus , factorContinuityEstimate
