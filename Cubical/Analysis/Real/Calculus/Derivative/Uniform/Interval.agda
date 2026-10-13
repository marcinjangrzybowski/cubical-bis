module Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform

uniformDerivativeOn→alongInterval : ∀ F f a b → IsRadiuswiseUniformDerivativeOn F f a b →
  IsRadiuswiseUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (F ∘ fst) (f ∘ fst)
uniformDerivativeOn→alongInterval F f a b derivative ε =
  PT.map (λ { (δ , bound) → δ , λ (x , a≤x , x≤b) (y , a≤y , y≤b) → bound x y a≤x x≤b a≤y y≤b })
    (derivative ε)

uniformDerivativeAlongInterval→on : ∀ F f a b →
  IsRadiuswiseUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (F ∘ fst) (f ∘ fst) →
  IsRadiuswiseUniformDerivativeOn F f a b
uniformDerivativeAlongInterval→on F f a b derivative ε =
  PT.map (λ { (δ , bound) → δ , λ x y a≤x x≤b a≤y y≤b → bound (x , a≤x , x≤b) (y , a≤y , y≤b) })
    (derivative ε)
