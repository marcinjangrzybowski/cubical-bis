module Cubical.HITs.CauchyReals.Complex.Metric.Operations where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Mappings


opaque
  translateLeftℂ-pres≈ : ∀ u z w ε → z ≈ℂ[ ε ] w →
    (u +ℂ z) ≈ℂ[ ε ] (u +ℂ w)
  translateLeftℂ-pres≈ u z w ε z≈w =
    subst2 (_≈ℂ[ ε ]_)
      (+ℂComm z u)
      (+ℂComm w u)
      (translateℂ-pres≈ u z w ε z≈w)


opaque
  addℂ-pres≈ : ∀ z z′ w w′ ε δ →
    z ≈ℂ[ ε ] z′ → w ≈ℂ[ δ ] w′ →
    (z +ℂ w) ≈ℂ[ ε +₊ δ ] (z′ +ℂ w′)
  addℂ-pres≈ z z′ w w′ ε δ z≈z′ w≈w′ =
    complexCloseTriangle
      (z +ℂ w)
      (z′ +ℂ w)
      (z′ +ℂ w′)
      ε δ
      (translateℂ-pres≈ w z z′ ε z≈z′)
      (translateLeftℂ-pres≈ z′ w w′ δ w≈w′)
