module Cubical.Analysis.Real.FiniteSum.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using
  ( Fin
  ; FinVec
  ; replicateFinVec
  ; _++Fin_
  )
import Cubical.Data.FinData as FD

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Data.Rationals.Base using (ℚ)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


finiteSumExt : ∀ {n} {x y : FinVec ℝ n} →
  (∀ i → x i ≡ y i) → ∑ x ≡ ∑ y
finiteSumExt = ℝSum.∑Ext


finiteSumZero : ∀ n →
  ∑ (replicateFinVec n 0ℝ) ≡ 0ℝ
finiteSumZero = ℝSum.∑0r


finiteSumLast : ∀ {n} (x : FinVec ℝ (suc n)) →
  ∑ x ≡
  ∑ (x ∘ FD.weakenFin) + x (FD.fromℕ n)
finiteSumLast = ℝSum.∑Last


finiteSumAppend : ∀ {n m} (x : FinVec ℝ n) (y : FinVec ℝ m) →
  ∑ (x ++Fin y) ≡ ∑ x + ∑ y
finiteSumAppend = ℝSum.∑Split++


finiteSumAdd : ∀ {n} (x y : FinVec ℝ n) →
  ∑ (λ i → x i + y i) ≡ ∑ x + ∑ y
finiteSumAdd = ℝSum.∑Split


finiteSumNeg : ∀ {n} (x : FinVec ℝ n) →
  ∑ (λ i → - x i) ≡ - ∑ x
finiteSumNeg = ℝSum.∑Dist-


finiteSumSub : ∀ {n} (x y : FinVec ℝ n) →
  ∑ (λ i → x i - y i) ≡ ∑ x - ∑ y
finiteSumSub = ℝSum.∑Split-


finiteSumMulLeft : ∀ {n} (c : ℝ) (x : FinVec ℝ n) →
  c · ∑ x ≡ ∑ (λ i → c · x i)
finiteSumMulLeft = ℝSum.∑Mulrdist


finiteSumMulRight : ∀ {n} (c : ℝ) (x : FinVec ℝ n) →
  (∑ x) · c ≡ ∑ (λ i → x i · c)
finiteSumMulRight = ℝSum.∑Mulldist


finiteSumRationalScale : ∀ {n} (c : ℚ) (x : FinVec ℝ n) →
  c ⋆ ∑ x ≡ ∑ (λ i → c ⋆ x i)
finiteSumRationalScale c x =
  scalar-as-mul c (∑ x)
  ∙ finiteSumMulLeft (rat c) x
  ∙ finiteSumExt (λ i → sym (scalar-as-mul c (x i)))


finiteSumExchange : ∀ {m n} (x : Fin m → Fin n → ℝ) →
  ∑ (λ i → ∑ (λ j → x i j)) ≡
  ∑ (λ j → ∑ (λ i → x i j))
finiteSumExchange = ℝSum.∑Exchange


finiteSumTelescoping : ∀ {n} (x : FinVec ℝ (suc n)) →
  ∑ {n = n} (λ i → x (FD.suc i) - x (FD.weakenFin i)) ≡
  x (FD.fromℕ n) - x FD.zero
finiteSumTelescoping = ℝSum.∑Telescoping
