module Cubical.HITs.CauchyReals.Exponentiation.RealPowerBaseContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.ExponentiationMore
  using (ln; ln-cont; _^ᵣ_; cont-^)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculus
  using (ln-realPower)
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponential
  using (eBase; realExp; realExp-ln)

opaque
  realPowerViaExpLn : ∀ x y →
    fst (realExp (y ·ᵣ ln x)) ≡ fst (x ^ᵣ y)
  realPowerViaExpLn x y =
    cong (fst ∘ realExp) (sym (ln-realPower x y))
    ∙ cong fst (realExp-ln (x ^ᵣ y))

  -- Previous name: ^-cont.
  realPowerBaseContinuous : ∀ y →
    IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y)))
  realPowerBaseContinuous y =
    subst (IsContinuousWithPred pred0<)
      (funExt₂ λ x 0<x → realPowerViaExpLn (x , 0<x) y)
      (IsContinuousWP∘' pred0< (fst ∘ realExp)
        (λ x 0<x → y ·ᵣ ln (x , 0<x))
        (cont-^ eBase)
        (IsContinuousWP∘' pred0< (y ·ᵣ_) (curry ln)
          (IsContinuous·ᵣL y) ln-cont))
