module Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootBounds where

-- Convert a common rational coefficient bound into a common rational
-- root bound. The radius is computed from degree and bound alone, without
-- selecting an Archimedean witness from a completed real number.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; drop)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Coercivity
import Cubical.Analysis.Complex.Polynomial.Monic.PermutationAlgebra as PermutationDefinition
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Finite
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale

private module P = PermutationDefinition.Permutation ℂCommRing

coerciveCoefficientRadius : ℕ → ℚ₊ → ℚ₊
coerciveCoefficientRadius zero A = 1
coerciveCoefficientRadius (suc n) A = (A +₊ 1) +₊ coerciveCoefficientRadius n A

coefficientRootBound : ℕ → ℚ₊ → ℚ₊
coefficientRootBound n A = (coerciveCoefficientRadius n A +₊ 1) +₊ (coerciveCoefficientRadius n A +₊ 1)

opaque
  coerciveRadius-bound : ∀ {n} (p : MonicPolynomial n) A → CoefficientsBounded p A →
    monicCoerciveRadius p ≤ℝ ⟦ coerciveCoefficientRadius n A ⟧₊
  coerciveRadius-bound [] A bounded = ≤ℝ-refl 1ℝ
  coerciveRadius-bound {n = suc n} (a ∷ p) A bounded =
    subst (monicCoerciveRadius (a ∷ p) ≤ℝ_)
      (cong (_+ ⟦ coerciveCoefficientRadius n A ⟧₊) (rat+rat (fst A) 1)
        ∙ rat+rat (fst (A +₊ 1)) (fst (coerciveCoefficientRadius n A)))
      (addPres≤ (modulusℂ a + 1ℝ) (⟦ A ⟧₊ + 1ℝ)
        (monicCoerciveRadius p) ⟦ coerciveCoefficientRadius n A ⟧₊
        (addPres≤R (modulusℂ a) ⟦ A ⟧₊ 1ℝ
          (≤ℝ-trans (modulusℂ a) (normℂ a) ⟦ A ⟧₊ (modulusℂ≤normℂ a) (bounded zero)))
        (coerciveRadius-bound p A (λ i → bounded (suc i))))

  exactRoot-bound : ∀ {n} (p : MonicPolynomial n) r A → CoefficientsBounded p A →
    evaluateMonic p r ≡ 0ℂ → normℂ r ≤ℝ ⟦ coefficientRootBound n A ⟧₊
  exactRoot-bound {n} p r A bounded root =
    ≤ℝ-trans (normℂ r) ((monicCoerciveRadius p + 1ℝ) + (monicCoerciveRadius p + 1ℝ))
      ⟦ coefficientRootBound n A ⟧₊
      (smallResidual-normBound p r
        (subst (_<ℝ 1ℝ) (sym (cong modulusℂ root ∙ modulusℂ-zero)) (radius-positive 1)))
      (subst (((monicCoerciveRadius p + 1ℝ) + (monicCoerciveRadius p + 1ℝ)) ≤ℝ_)
          (rat+rat (fst R) (fst R))
          (addPres≤ (monicCoerciveRadius p + 1ℝ) ⟦ R ⟧₊
            (monicCoerciveRadius p + 1ℝ) ⟦ R ⟧₊ enlarged enlarged))
    where
    R : ℚ₊
    R = coerciveCoefficientRadius n A +₊ 1
    enlarged : monicCoerciveRadius p + 1ℝ ≤ℝ ⟦ R ⟧₊
    enlarged = subst (monicCoerciveRadius p + 1ℝ ≤ℝ_)
      (rat+rat (fst (coerciveCoefficientRadius n A)) 1)
      (addPres≤R (monicCoerciveRadius p) ⟦ coerciveCoefficientRadius n A ⟧₊ 1ℝ
        (coerciveRadius-bound p A bounded))

  linearFactors-root : ∀ {n} (roots : Vec ℂ (suc n)) i →
    evaluateMonic (linearFactors roots) (lookup i roots) ≡ 0ℂ
  linearFactors-root roots i =
    cong (λ p → evaluateMonic p (lookup i roots)) (P.linearFactors-extract roots i)
      ∙ evaluate-multiplyLinear (lookup i roots) (linearFactors (drop i roots)) (lookup i roots)
      ∙ cong (_·ℂ evaluateMonic (linearFactors (drop i roots)) (lookup i roots)) (+ℂInvR (lookup i roots))
      ∙ ℂRing.0LeftAnnihilates (evaluateMonic (linearFactors (drop i roots)) (lookup i roots))

  factorRootsBounded : ∀ {n} (roots : Vec ℂ n) A → CoefficientsBounded (linearFactors roots) A →
    RootsBounded roots (coefficientRootBound n A)
  factorRootsBounded [] A bounded ()
  factorRootsBounded (r ∷ roots) A bounded i =
    exactRoot-bound (linearFactors (r ∷ roots)) (lookup i (r ∷ roots)) A bounded (linearFactors-root (r ∷ roots) i)

dropRootsBounded : ∀ {n} (roots : Vec ℂ (suc n)) i B → RootsBounded roots B → RootsBounded (drop i roots) B
dropRootsBounded roots i B bounded k =
  subst (λ z → normℂ z ≤ℝ ⟦ B ⟧₊) (sym (extract-lookup roots i (suc k)))
    (bounded (equivFun (extractPermutation i) (suc k)))
