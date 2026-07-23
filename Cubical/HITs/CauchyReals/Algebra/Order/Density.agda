module Cubical.HITs.CauchyReals.Algebra.Order.Density where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance


private
  module ℝOrder = OrderedCommRingTheory ℝOrderedCommRing

  half : ℝ
  half = rat [ 1 / 2 ]

  half·two≡one : half ·ᵣ (1 +ᵣ 1) ≡ 1
  half·two≡one =
    cong (half ·ᵣ_) (+ᵣ-rat 1 1)
    ∙ sym (rat·ᵣrat [ 1 / 2 ] (1 ℚ.+ 1))
    ∙ cong rat ℚ!!

  module ℝHalf = Characteristic≠2 ℝOrderedCommRing half half·two≡one


denseℝ : ∀ u v → u <ᵣ v → Σ[ r ∈ ℝ ] ((u <ᵣ r) × (r <ᵣ v))
denseℝ u v u<v =
  ℝHalf.mean u v , ℝHalf.<→<mean u v u<v , ℝHalf.<→mean< u v u<v
