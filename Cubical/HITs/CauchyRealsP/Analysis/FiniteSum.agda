module Cubical.HITs.CauchyRealsP.Analysis.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence.Cauchy

private
  module ℝSum =
    Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)

finiteSumPresIsLimitSeq :
  ∀ {n}
  (x : FinVec (ℕ → ℝ) n)
  (l : FinVec ℝ n) →
  (∀ i → isLimitSeq (x i) (l i)) →
  isLimitSeq
    (λ k → ∑ (λ i → x i k))
    (∑ l)
finiteSumPresIsLimitSeq {n = zero} x l x-lim =
  constantIsLimitSeq 0
finiteSumPresIsLimitSeq {n = suc n} x l x-lim =
  addPresIsLimitSeq
    (x FD.zero)
    (λ k → ∑ (λ i → x (FD.suc i) k))
    (l FD.zero)
    (∑ (l ∘ FD.suc))
    (x-lim FD.zero)
    (finiteSumPresIsLimitSeq
      (x ∘ FD.suc)
      (l ∘ FD.suc)
      (x-lim ∘ FD.suc))

finiteSumPresIsCauchySeq :
  ∀ {n}
  (x : FinVec (ℕ → ℝ) n) →
  (∀ i → isCauchySeq (x i)) →
  isCauchySeq
    (λ k → ∑ (λ i → x i k))
finiteSumPresIsCauchySeq {n = zero} x x-cauchy =
  (λ _ → 0) , λ ε _ _ _ _ → refl∼ 0 ε
finiteSumPresIsCauchySeq {n = suc n} x x-cauchy =
  addPresIsCauchySeq
    (x FD.zero)
    (λ k → ∑ (λ i → x (FD.suc i) k))
    (x-cauchy FD.zero)
    (finiteSumPresIsCauchySeq
      (x ∘ FD.suc)
      (x-cauchy ∘ FD.suc))
