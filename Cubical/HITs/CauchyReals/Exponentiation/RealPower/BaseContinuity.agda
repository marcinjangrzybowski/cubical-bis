module Cubical.HITs.CauchyReals.Exponentiation.RealPower.BaseContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
  using (ln; ln-cont; _^ᵣ_; cont-^)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Calculus
  using (ln-realPower)
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential
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
