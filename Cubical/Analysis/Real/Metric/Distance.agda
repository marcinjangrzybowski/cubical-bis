module Cubical.Analysis.Real.Metric.Distance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace

open CategoryStructures
open OrderedCommRingTheory ℚOrderedCommRing

private
  module RealBinary = BinaryNonExpanding
    ℝPremetricSpace ℝPremetricSpace ℝPremetricSpace


distanceℝ : ℝ → ℝ → ℝ
distanceℝ x y = absℝ (x - y)

distance-rat : ∀ p q →
  distanceℝ (rat p) (rat q) ≡ rat (abs (p ℚ.- q))
distance-rat p q =
  cong absℝ (sub-rat p q)
  ∙ abs-rat (p ℚ.- q)

distance-isNonExpanding₁ : ∀ y → IsNonExpanding
  (ℝPremetricSpace .snd) (flip distanceℝ y) (ℝPremetricSpace .snd)
distance-isNonExpanding₁ y = snd
  ((absℝ , abs-isNonExpanding) ∘NE
    (_+ (- y) , add-isNonExpanding₁ (- y)))

distance-isNonExpanding₂ : ∀ x → IsNonExpanding
  (ℝPremetricSpace .snd) (distanceℝ x) (ℝPremetricSpace .snd)
distance-isNonExpanding₂ x = snd
  ((absℝ , abs-isNonExpanding) ∘NE
    (((x +_) , add-isNonExpanding₂ x) ∘NE
      (-_ , neg-isNonExpanding)))

private
  distance₂ : RealBinary.NE₂[_,_,_]
  distance₂ .RealBinary.NE₂[_,_,_].fun = distanceℝ
  distance₂ .RealBinary.NE₂[_,_,_].leftNE = distance-isNonExpanding₁
  distance₂ .RealBinary.NE₂[_,_,_].rightNE = distance-isNonExpanding₂

distance-isContinuous₁ : ∀ y → isContinuous
  (ℝPremetricSpace .snd) (flip distanceℝ y) (ℝPremetricSpace .snd)
distance-isContinuous₁ y = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (flip distanceℝ y) (ℝPremetricSpace .snd)
  (distance-isNonExpanding₁ y)

distance-isContinuous₂ : ∀ x → isContinuous
  (ℝPremetricSpace .snd) (distanceℝ x) (ℝPremetricSpace .snd)
distance-isContinuous₂ x = isNonExpanding→isContinuous
  (ℝPremetricSpace .snd) (distanceℝ x) (ℝPremetricSpace .snd)
  (distance-isNonExpanding₂ x)

distance-pres∼₁ : ∀ x x' y ε →
  x ∼[ ε ] x' → distanceℝ x y ∼[ ε ] distanceℝ x' y
distance-pres∼₁ x x' y ε =
  distance-isNonExpanding₁ y .IsNonExpanding.pres≈ x x' ε

distance-pres∼₂ : ∀ x y y' ε →
  y ∼[ ε ] y' → distanceℝ x y ∼[ ε ] distanceℝ x y'
distance-pres∼₂ x y y' ε =
  distance-isNonExpanding₂ x .IsNonExpanding.pres≈ y y' ε

distanceRefl : ∀ x → distanceℝ x x ≡ 0ℝ
distanceRefl x = cong absℝ (subSelf x) ∙ absZero

distanceZeroR : ∀ x → distanceℝ x 0ℝ ≡ absℝ x
distanceZeroR x = cong absℝ (subZero x)

distanceZeroL : ∀ x → distanceℝ 0ℝ x ≡ absℝ x
distanceZeroL x = cong absℝ (zeroSub x) ∙ absNeg x

private
  subSwapNeg : ∀ x y → x - y ≡ - (y - x)
  subSwapNeg x y = sym
    (negAdd y (- x)
      ∙ cong ((- y) +_) (negInvol x)
      ∙ addComm (- y) x)


distanceSym : ∀ x y → distanceℝ x y ≡ distanceℝ y x
distanceSym x y =
  cong absℝ (subSwapNeg x y)
  ∙ absNeg (y - x)
