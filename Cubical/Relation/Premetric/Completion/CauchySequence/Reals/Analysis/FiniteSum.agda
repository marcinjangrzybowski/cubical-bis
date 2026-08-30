module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence


private
  module ℝSum =
    Sum (CommRing→Ring ℝCommRing)

  0ℝ : Real.ℝ
  0ℝ = CommRingStr.0r (snd ℝCommRing)

open ℝSum using (∑)


-- A finite family does not introduce a choice issue: recursion combines
-- only finitely many radiuswise tails.  In particular, no global modulus is
-- assembled while proving the Cauchy statement.

finiteSumPresIsLimitSequence :
  ∀ {n}
  (x : FinVec (ℕ → Real.ℝ) n)
  (l : FinVec Real.ℝ n) →
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


finiteSumPresIsCauchySequence :
  ∀ {n}
  (x : FinVec (ℕ → Real.ℝ) n) →
  (∀ i → IsCauchySequence (x i)) →
  IsCauchySequence
    (λ k → ∑ (λ i → x i k))
finiteSumPresIsCauchySequence {n = zero} x x-cauchy =
  constantIsCauchySequence 0ℝ
finiteSumPresIsCauchySequence {n = suc n} x x-cauchy =
  addPresIsCauchySequence
    (x-cauchy FD.zero)
    (finiteSumPresIsCauchySequence
      (x ∘ FD.suc)
      (x-cauchy ∘ FD.suc))
