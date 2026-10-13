module Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients where

-- Finite bounds for adjoining a linear factor. Generous positive rational
-- constants simplify the degree-zero case and give computable moduli.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (lookup; []; _∷_)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Norm.Difference
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale

CoefficientNormBound : ∀ {n} → MonicPolynomial n → ℝ → Type₀
CoefficientNormBound {n} p A = ∀ (i : Fin n) → normℂ (lookup i p) ≤ℝ A

CoefficientDifferenceBound : ∀ {n} → MonicPolynomial n → MonicPolynomial n → ℝ → Type₀
CoefficientDifferenceBound {n} p q δ = ∀ (i : Fin n) → normℂ (lookup i p -ℂ lookup i q) ≤ℝ δ

coefficientNorm-monotone : ∀ {n} (p : MonicPolynomial n) A B → A ≤ℝ B →
  CoefficientNormBound p A → CoefficientNormBound p B
coefficientNorm-monotone p A B below bounded i = ≤ℝ-trans (normℂ (lookup i p)) A B (bounded i) below

coefficientDifference-monotone : ∀ {n} (p q : MonicPolynomial n) A B → A ≤ℝ B →
  CoefficientDifferenceBound p q A → CoefficientDifferenceBound p q B
coefficientDifference-monotone p q A B below bounded i =
  ≤ℝ-trans (normℂ (lookup i p -ℂ lookup i q)) A B (bounded i) below

addConstant-bound : ∀ {n} a (p : MonicPolynomial (suc n)) A B →
  0ℝ ≤ℝ A → normℂ a ≤ℝ A → CoefficientNormBound p B →
  CoefficientNormBound (addConstant a p) (A + B)
addConstant-bound a (b ∷ p) A B nonnegative ab pb zero = normℂ-addBound a b A B ab (pb zero)
addConstant-bound a (b ∷ p) A B nonnegative ab pb (suc i) =
  ≤ℝ-trans (normℂ (lookup i p)) B (A + B) (pb (suc i))
    (subst (_≤ℝ A + B) (addIdL B) (addPres≤R 0ℝ A B nonnegative))

addConstant-difference : ∀ {n} a b (p q : MonicPolynomial (suc n)) δ ε →
  0ℝ ≤ℝ δ → normℂ (a -ℂ b) ≤ℝ δ → CoefficientDifferenceBound p q ε →
  CoefficientDifferenceBound (addConstant a p) (addConstant b q) (δ + ε)
addConstant-difference a b (c ∷ p) (d ∷ q) δ ε nonnegative ab pq zero =
  normℂ-sumDifference a c b d δ ε ab (pq zero)
addConstant-difference a b (c ∷ p) (d ∷ q) δ ε nonnegative ab pq (suc i) =
  ≤ℝ-trans (normℂ (lookup i p -ℂ lookup i q)) ε (δ + ε) (pq (suc i))
    (subst (_≤ℝ δ + ε) (addIdL ε) (addPres≤R 0ℝ δ ε nonnegative))

linearCoefficientBound : ℕ → ℚ₊ → ℚ₊ → ℚ₊
linearCoefficientBound zero A B = B
linearCoefficientBound (suc n) A B = (B ·₊ A) +₊ (A +₊ linearCoefficientBound n A B)

linearCoefficientLipschitz : ℕ → ℚ₊ → ℚ₊ → ℚ₊
linearCoefficientLipschitz zero A B = 1
linearCoefficientLipschitz (suc n) A B = (A +₊ B) +₊ (1 +₊ linearCoefficientLipschitz n A B)

opaque
  multiplyLinear-bound : ∀ {n} r (p : MonicPolynomial n) A B →
    normℂ r ≤ℝ ⟦ B ⟧₊ → CoefficientNormBound p ⟦ A ⟧₊ →
    CoefficientNormBound (multiplyLinear r p) ⟦ linearCoefficientBound n A B ⟧₊
  multiplyLinear-bound r [] A B rb pb zero = subst (_≤ℝ ⟦ B ⟧₊) (sym (normℂ-neg r)) rb
  multiplyLinear-bound {n = suc n} r (a ∷ p) A B rb pb zero =
    ≤ℝ-trans (normℂ ((-ℂ r) ·ℂ a)) ⟦ B ·₊ A ⟧₊ ⟦ linearCoefficientBound (suc n) A B ⟧₊
      (subst (normℂ ((-ℂ r) ·ℂ a) ≤ℝ_) (mul-rat (fst B) (fst A))
        (normℂ-mulBound (-ℂ r) a ⟦ B ⟧₊ ⟦ A ⟧₊
          (subst (_≤ℝ ⟦ B ⟧₊) (sym (normℂ-neg r)) rb) (pb zero)))
      (radius-sumL (B ·₊ A) (A +₊ linearCoefficientBound n A B))
  multiplyLinear-bound {n = suc n} r (a ∷ p) A B rb pb (suc i) =
    coefficientNorm-monotone (addConstant a (multiplyLinear r p))
      (⟦ A ⟧₊ + ⟦ linearCoefficientBound n A B ⟧₊) ⟦ linearCoefficientBound (suc n) A B ⟧₊
      (subst (_≤ℝ ⟦ linearCoefficientBound (suc n) A B ⟧₊)
        (sym (rat+rat (fst A) (fst (linearCoefficientBound n A B))))
        (radius-sumR (B ·₊ A) (A +₊ linearCoefficientBound n A B)))
      (addConstant-bound a (multiplyLinear r p) ⟦ A ⟧₊ ⟦ linearCoefficientBound n A B ⟧₊
        (radius-nonnegative A) (pb zero) (multiplyLinear-bound r p A B rb (λ j → pb (suc j)))) i

  multiplyLinear-difference : ∀ {n} r s (p q : MonicPolynomial n) A B δ →
    0ℝ ≤ℝ δ → normℂ s ≤ℝ ⟦ B ⟧₊ → CoefficientNormBound p ⟦ A ⟧₊ →
    normℂ (r -ℂ s) ≤ℝ δ → CoefficientDifferenceBound p q δ →
    CoefficientDifferenceBound (multiplyLinear r p) (multiplyLinear s q)
      (⟦ linearCoefficientLipschitz n A B ⟧₊ · δ)
  multiplyLinear-difference r s [] [] A B δ δ≥0 sb pb rs pq zero =
    subst2 _≤ℝ_ (sym (normℂ-negativeDifference r s)) (sym (mulIdL δ)) rs
  multiplyLinear-difference {n = suc n} r s (a ∷ p) (b ∷ q) A B δ δ≥0 sb pb rs pq zero =
    ≤ℝ-trans (normℂ ((-ℂ r) ·ℂ a -ℂ (-ℂ s) ·ℂ b))
      (⟦ A +₊ B ⟧₊ · δ) (⟦ linearCoefficientLipschitz (suc n) A B ⟧₊ · δ)
      (subst (normℂ ((-ℂ r) ·ℂ a -ℂ (-ℂ s) ·ℂ b) ≤ℝ_)
        (cong (_+ ⟦ B ⟧₊ · δ) (mulComm δ ⟦ A ⟧₊)
          ∙ sym (mulDistL ⟦ A ⟧₊ ⟦ B ⟧₊ δ) ∙ cong (_· δ) (rat+rat (fst A) (fst B)))
        (normℂ-productDifference (-ℂ r) a (-ℂ s) b ⟦ A ⟧₊ ⟦ B ⟧₊ δ δ
          (pb zero) (subst (_≤ℝ ⟦ B ⟧₊) (sym (normℂ-neg s)) sb)
          (subst (_≤ℝ δ) (sym (normℂ-negativeDifference r s)) rs) (pq zero)))
      (mulPres≤R-0≤ ⟦ A +₊ B ⟧₊ ⟦ linearCoefficientLipschitz (suc n) A B ⟧₊ δ δ≥0
        (radius-sumL (A +₊ B) (1 +₊ linearCoefficientLipschitz n A B)))
  multiplyLinear-difference {n = suc n} r s (a ∷ p) (b ∷ q) A B δ δ≥0 sb pb rs pq (suc i) =
    coefficientDifference-monotone (addConstant a (multiplyLinear r p)) (addConstant b (multiplyLinear s q))
      (δ + ⟦ linearCoefficientLipschitz n A B ⟧₊ · δ)
      (⟦ linearCoefficientLipschitz (suc n) A B ⟧₊ · δ)
      (subst (_≤ℝ ⟦ linearCoefficientLipschitz (suc n) A B ⟧₊ · δ) (sym sum-path)
        (mulPres≤R-0≤ ⟦ 1 +₊ linearCoefficientLipschitz n A B ⟧₊
          ⟦ linearCoefficientLipschitz (suc n) A B ⟧₊ δ δ≥0
          (radius-sumR (A +₊ B) (1 +₊ linearCoefficientLipschitz n A B))))
      (addConstant-difference a b (multiplyLinear r p) (multiplyLinear s q)
        δ (⟦ linearCoefficientLipschitz n A B ⟧₊ · δ) δ≥0 (pq zero)
        (multiplyLinear-difference r s p q A B δ δ≥0 sb (λ j → pb (suc j)) rs (λ j → pq (suc j)))) i
    where
    sum-path : δ + ⟦ linearCoefficientLipschitz n A B ⟧₊ · δ ≡
      ⟦ 1 +₊ linearCoefficientLipschitz n A B ⟧₊ · δ
    sum-path = cong (_+ ⟦ linearCoefficientLipschitz n A B ⟧₊ · δ) (sym (mulIdL δ))
      ∙ sym (mulDistL 1ℝ ⟦ linearCoefficientLipschitz n A B ⟧₊ δ)
      ∙ cong (_· δ) (rat+rat 1 (fst (linearCoefficientLipschitz n A B)))
