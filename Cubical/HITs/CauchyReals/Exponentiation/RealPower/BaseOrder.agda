module Cubical.HITs.CauchyReals.Exponentiation.RealPower.BaseOrder where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition using (_^ᵣ_; ln)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Laws
  using (lnStrictMonotone)
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential
  using (realExp; realExpStrictMonotone)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.BaseContinuity
  using (realPowerViaExpLn)

opaque
  -- Previous name: ^-strictMonotone.
  realPowerBaseStrictMonotone : ∀ x x' y →
    0 <ᵣ y → fst x <ᵣ fst x' →
    fst (x ^ᵣ y) <ᵣ fst (x' ^ᵣ y)
  realPowerBaseStrictMonotone x x' y 0<y x<x' =
    isTrans<≡ᵣ _ _ _
      (isTrans≡<ᵣ _ _ _
        (sym (realPowerViaExpLn x y))
        (realExpStrictMonotone _ _
          (<ᵣ-o·ᵣ (ln x) (ln x') (y , 0<y)
            (lnStrictMonotone x x' x<x'))))
      (realPowerViaExpLn x' y)
