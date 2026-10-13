module Cubical.Analysis.Real.Functions.Roots.PowerMap where

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

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

module _ (f : ℝ → ℝ) (atZero : f 0ℝ ≡ 1ℝ)
  (presAdd : ∀ x y → f (x + y) ≡ f x · f y) where

  opaque
    additiveMap-naturalPower : ∀ x n → powℝ (f x) n ≡ f (realNatural n · x)
    additiveMap-naturalPower x zero = sym atZero
      ∙ cong f (sym (ℝRing.0LeftAnnihilates x))
    additiveMap-naturalPower x (suc n) = cong (f x ·_) (additiveMap-naturalPower x n)
      ∙ sym (presAdd x (realNatural n · x))
      ∙ cong f (sym
        (cong (_· x) (realNatural-suc n) ∙ mulDistL (realNatural n) 1ℝ x
          ∙ cong (realNatural n · x +_) (mulIdL x) ∙ addComm (realNatural n · x) x))
