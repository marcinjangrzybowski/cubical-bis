module Cubical.Analysis.Complex.Polynomial.Monic.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData as Fin using (zero; suc)
open import Cubical.Data.Vec using ([]; _∷_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric

CoefficientContinuous : ∀ {n m} → (MonicPolynomial n → MonicPolynomial m) → Type₀
CoefficientContinuous f = ∀ p ε → ∥ Σ[ δ ∈ ℚ₊ ]
  ((q : _) → CoefficientCloseness p δ q → CoefficientCloseness (f p) ε (f q)) ∥₁

private module C = PremetricStr (ℂPremetricSpace .snd)

multiplyLinear-coefficientContinuous : ∀ {n} r → CoefficientContinuous (multiplyLinear {n} r)
multiplyLinear-coefficientContinuous r [] ε = ∣ ε , (λ { [] close zero → refl∼ℂ (-ℂ r) ε }) ∣₁
multiplyLinear-coefficientContinuous r (a ∷ p) ε = PT.map2 combine
  (IsContinuousAt.pres≈ (leftMultiplyℂ-isContinuous (-ℂ r) a) ε)
  (multiplyLinear-coefficientContinuous r p (ε /2₊))
  where
  combine :
    (Σ[ δ ∈ ℚ₊ ] ((b : ℂ) → a ∼ℂ[ δ ] b → ((-ℂ r) ·ℂ a) ∼ℂ[ ε ] ((-ℂ r) ·ℂ b))) →
    (Σ[ δ ∈ ℚ₊ ] ((q : _) → CoefficientCloseness p δ q →
      CoefficientCloseness (multiplyLinear r p) (ε /2₊) (multiplyLinear r q))) →
    Σ[ δ ∈ ℚ₊ ] ((q : _) → CoefficientCloseness (a ∷ p) δ q →
      CoefficientCloseness (multiplyLinear r (a ∷ p)) ε (multiplyLinear r q))
  combine (δmul , mulClose) (δtail , tailClose) = δ , preserve
    where
    δ = min₊ δmul (min₊ δtail (ε /2₊))
    δ≤mul = min₊≤L δmul (min₊ δtail (ε /2₊))
    δ≤tail = ℚ.isTrans≤ _ _ _ (min₊≤R δmul (min₊ δtail (ε /2₊))) (min₊≤L δtail (ε /2₊))
    δ≤half = ℚ.isTrans≤ _ _ _ (min₊≤R δmul (min₊ δtail (ε /2₊))) (min₊≤R δtail (ε /2₊))

    preserve : ∀ q → CoefficientCloseness (a ∷ p) δ q →
      CoefficientCloseness (multiplyLinear r (a ∷ p)) ε (multiplyLinear r q)
    preserve (b ∷ q) close zero = mulClose b (C.isMonotone≈≤ a b δ δmul δ≤mul (close zero))
    preserve (b ∷ q) close (suc k) =
      addConstant-halfCloseness a b (multiplyLinear r p) (multiplyLinear r q) ε
        (C.isMonotone≈≤ a b δ (ε /2₊) δ≤half (close zero))
        (tailClose q (coefficientCloseness-monotone p q δ δtail δ≤tail (λ j → close (suc j)))) k
