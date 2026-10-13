module Cubical.Analysis.Real.Series.PowerSeries.Difference.InteriorBound where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊; invℚ₊[x]·x)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Series.PowerSeries.Difference

-- Increasing the second endpoint increases the finite divided difference
-- when both endpoints are nonnegative. No infinite-series theorem is used.
opaque
  powerDifferenceFactor-monoRight : ∀ x y z →
    0ℝ ≤ℝ x → 0ℝ ≤ℝ y → y ≤ℝ z → ∀ n →
    powerDifferenceFactor x y n ≤ℝ powerDifferenceFactor x z n
  powerDifferenceFactor-monoRight x y z px py yz zero = ≤ℝ-refl 1ℝ
  powerDifferenceFactor-monoRight x y z px py yz (suc n) =
    addPres≤ (powℝ y (suc n)) (powℝ z (suc n))
      (x · powerDifferenceFactor x y n) (x · powerDifferenceFactor x z n)
      (powMono (suc n) py yz)
      (mulPres≤L (powerDifferenceFactor x y n) (powerDifferenceFactor x z n)
        x (0≤→isNonnegative x px)
        (powerDifferenceFactor-monoRight x y z px py yz n))

-- The elementary secant estimate (R-r)(n+1)r^n ≤ R^(n+1).
-- It controls the formal derivative at an interior radius by the original
-- series at the outer radius, including the case r = 0.
opaque
  powerDerivativeGapBound : ∀ inner outer →
    0ℝ ≤ℝ inner → inner ≤ℝ outer → ∀ n →
    (outer - inner) · (realNatural (suc n) · powℝ inner n)
      ≤ℝ powℝ outer (suc n)
  powerDerivativeGapBound inner outer positive ordered n =
    ≤ℝ-trans ((outer - inner) · (realNatural (suc n) · powℝ inner n))
      (powℝ outer (suc n) - powℝ inner (suc n)) (powℝ outer (suc n))
      (subst2 _≤ℝ_
        (cong ((outer - inner) ·_) (powerDifferenceFactor-diagonal inner n))
        (sym (powerDifferenceFactor-identity inner outer n))
        (mulPres≤L (powerDifferenceFactor inner inner n) (powerDifferenceFactor inner outer n)
          (outer - inner) (0≤→isNonnegative (outer - inner) (nonnegativeSub inner outer ordered))
          (powerDifferenceFactor-monoRight inner inner outer positive positive ordered n)))
      (subst ((powℝ outer (suc n) - powℝ inner (suc n)) ≤ℝ_) (addIdR (powℝ outer (suc n)))
        (addPres≤L (- powℝ inner (suc n)) 0ℝ (powℝ outer (suc n))
          (subst ((- powℝ inner (suc n)) ≤ℝ_) negZero
            (negPres≤ 0ℝ (powℝ inner (suc n)) (powNonnegative inner (suc n) positive)))))

-- A supplied positive rational lower bound on R-r yields an explicit
-- rational comparison constant. Such scaling preserves native Cauchy data.
opaque
  powerDerivativeBoundByOuterRadius : ∀ inner outer gap →
    0ℝ ≤ℝ inner → inner ≤ℝ outer → rat (fst gap) ≤ℝ outer - inner → ∀ n →
    realNatural (suc n) · powℝ inner n
      ≤ℝ rat (fst (gap ⁻¹₊)) · powℝ outer (suc n)
  powerDerivativeBoundByOuterRadius inner outer gap positive ordered lower n =
    subst (_≤ℝ rat (fst (gap ⁻¹₊)) · powℝ outer (suc n)) cancel
      (mulPres≤L (rat (fst gap) · weight) (powℝ outer (suc n))
        (rat (fst (gap ⁻¹₊)))
        (0≤→isNonnegative (rat (fst (gap ⁻¹₊)))
          (<ℝ-weaken 0ℝ (rat (fst (gap ⁻¹₊)))
            (<ℚ→<ℝ 0 (fst (gap ⁻¹₊)) (snd (gap ⁻¹₊)))))
        (≤ℝ-trans (rat (fst gap) · weight) ((outer - inner) · weight) (powℝ outer (suc n))
          (mulPres≤R-0≤ (rat (fst gap)) (outer - inner) weight
            (isNonnegative→0≤ weight
              (mulPresIsNonnegative (realNatural (suc n)) (powℝ inner n)
                (0≤→isNonnegative (realNatural (suc n)) (realNatural-nonnegative (suc n)))
                (powPresIsNonnegative inner n (0≤→isNonnegative inner positive)))) lower)
          (powerDerivativeGapBound inner outer positive ordered n)))
    where
    weight : ℝ
    weight = realNatural (suc n) · powℝ inner n

    cancel : rat (fst (gap ⁻¹₊)) · (rat (fst gap) · weight) ≡ weight
    cancel = mulAssoc (rat (fst (gap ⁻¹₊))) (rat (fst gap)) weight
      ∙ cong (_· weight) (mul-rat (fst (gap ⁻¹₊)) (fst gap) ∙ cong rat (invℚ₊[x]·x gap))
      ∙ mulIdL weight
