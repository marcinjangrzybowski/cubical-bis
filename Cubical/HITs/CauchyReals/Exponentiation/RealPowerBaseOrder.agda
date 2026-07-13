module Cubical.HITs.CauchyReals.Exponentiation.RealPowerBaseOrder where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.ExponentiationMore using (_^ᵣ_; ln)
open import Cubical.HITs.CauchyReals.Exponentiation.LogarithmLaws
  using (lnStrictMonotone)
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponential
  using (realExp; realExpStrictMonotone)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerBaseContinuity
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
