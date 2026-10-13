module Cubical.Analysis.Real.Functions.Roots.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Logarithm.Global
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  degree-positive : ∀ n → 0ℝ <ℝ realNatural (suc n)
  degree-positive n = subst2 _<ℝ_ (addIdL 0ℝ) (sym (realNatural-suc n))
    (≤<ℝ-add 0ℝ (realNatural n) 0ℝ 1ℝ (realNatural-nonnegative n)
      (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)))

  reciprocalDegree : ℕ → ℝ
  reciprocalDegree n = positiveReciprocal (realNatural (suc n)) (degree-positive n)

  scale-by-degree : ∀ n x → realNatural (suc n) · (reciprocalDegree n · x) ≡ x
  scale-by-degree n x = mulAssoc (realNatural (suc n)) (reciprocalDegree n) x
    ∙ cong (_· x) (positiveReciprocalLaw (realNatural (suc n)) (degree-positive n))
    ∙ mulIdL x

open import Cubical.Analysis.Real.Functions.Roots.PowerMap

opaque
  expℝ-naturalPower : ∀ x n → powℝ (expℝ x) n ≡ expℝ (realNatural n · x)
  expℝ-naturalPower = additiveMap-naturalPower expℝ exponentialEntireValue-zero exponentialEntireValue-add

-- Index n means a root of degree suc n. The input is positive, so the
-- native global logarithm and a witnessed positive reciprocal suffice.
opaque
  positiveRootℝ : (n : ℕ) (x : ℝ) → 0ℝ <ℝ x → ℝ
  positiveRootℝ n x positive = expℝ (reciprocalDegree n · logℝ (x , positive))

  positiveRootℝ-positive : ∀ n x positive → 0ℝ <ℝ positiveRootℝ n x positive
  positiveRootℝ-positive n x positive = expℝ-positive (reciprocalDegree n · logℝ (x , positive))

  positiveRootℝ-power : ∀ n x positive → powℝ (positiveRootℝ n x positive) (suc n) ≡ x
  positiveRootℝ-power n x positive =
    expℝ-naturalPower (reciprocalDegree n · logℝ (x , positive)) (suc n)
      ∙ cong expℝ (scale-by-degree n (logℝ (x , positive))) ∙ expℝ-logℝ (x , positive)
