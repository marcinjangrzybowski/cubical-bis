module Cubical.Analysis.Real.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Sequence using
  ( isLimitSequence
  ; constantSeqWitness
  ; constantIsLimitSequence
  ; addSeqWitness
  ; addPresIsLimitSequence
  )


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


finiteSumPresSeqWitness :
  ∀ {n} (x : FinVec (ℕ → ℝ) n) →
  (∀ i → SeqWitness (x i)) →
  SeqWitness (λ k → ∑ (λ i → x i k))
finiteSumPresSeqWitness {n = zero} x x-cauchy =
  constantSeqWitness 0ℝ
finiteSumPresSeqWitness {n = suc n} x x-cauchy =
  addSeqWitness
    (x-cauchy FD.zero)
    (finiteSumPresSeqWitness
      (x ∘ FD.suc)
      (x-cauchy ∘ FD.suc))


finiteSumPresIsLimitSequence :
  ∀ {n}
  (x : FinVec (ℕ → ℝ) n)
  (l : FinVec ℝ n) →
  (∀ i → isLimitSequence (x i) (l i)) →
  isLimitSequence
    (λ k → ∑ (λ i → x i k))
    (∑ l)
finiteSumPresIsLimitSequence {n = zero} x l x→l =
  constantIsLimitSequence 0ℝ
finiteSumPresIsLimitSequence {n = suc n} x l x→l =
  addPresIsLimitSequence
    (x→l FD.zero)
    (finiteSumPresIsLimitSequence
      (x ∘ FD.suc)
      (l ∘ FD.suc)
      (x→l ∘ FD.suc))
