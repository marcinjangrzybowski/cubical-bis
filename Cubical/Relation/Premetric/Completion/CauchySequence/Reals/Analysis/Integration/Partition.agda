module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.FinData using (Fin ; FinVec)
import Cubical.Data.FinData as FD

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
  using (≤→zero≤difference)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  zeroℝ : Real.ℝ
  zeroℝ = CommRingStr.0r (snd ℝCommRing)

open ℝSum using
  (∑ ; ∑Ext ; ∑Dist- ; ∑Split ; ∑Split- ; ∑Mulldist ; ∑Telescoping)


-- A partition stores n+1 vertices for n subintervals.  This convention lines
-- up directly with `FinVec` telescoping and avoids manufacturing an augmented
-- endpoint vector for every proof about Riemann sums.

record Partition[_,_] (a b : Real.ℝ) : Type₀ where
  field
    intervalCount : ℕ
    points : FinVec Real.ℝ (suc intervalCount)
    leftEndpoint : points FD.zero ≡ a
    rightEndpoint : points (FD.fromℕ intervalCount) ≡ b
    monotone : (i : Fin intervalCount) →
      points (FD.weakenFin i) ≤ℝ points (FD.suc i)


record TaggedPartition[_,_] (a b : Real.ℝ) : Type₀ where
  field
    partition : Partition[ a , b ]
    tags : FinVec Real.ℝ
      (Partition[_,_].intervalCount partition)
    lower≤tag : (i : Fin (Partition[_,_].intervalCount partition)) →
      Partition[_,_].points partition (FD.weakenFin i) ≤ℝ tags i
    tag≤upper : (i : Fin (Partition[_,_].intervalCount partition)) →
      tags i ≤ℝ Partition[_,_].points partition (FD.suc i)


module _ {a b : Real.ℝ} (p : Partition[ a , b ]) where
  open Partition[_,_] p

  width : Fin intervalCount → Real.ℝ
  width i = points (FD.suc i) Group.- points (FD.weakenFin i)

  width-nonnegative : ∀ i → zeroℝ ≤ℝ width i
  width-nonnegative i =
    ≤→zero≤difference
      (points (FD.weakenFin i)) (points (FD.suc i))
      (monotone i)

  totalWidth : ∑ width ≡ b Group.- a
  totalWidth =
    ∑Telescoping points
    ∙ cong₂ Group._-_ rightEndpoint leftEndpoint


module _ {a b : Real.ℝ} (tagged : TaggedPartition[ a , b ]) where
  private
    p = TaggedPartition[_,_].partition tagged

  open Partition[_,_] p
  open TaggedPartition[_,_] tagged

  riemannSum : (Real.ℝ → Real.ℝ) → Real.ℝ
  riemannSum f = ∑ (λ i → width p i Mul.· f (tags i))

  riemannSum-cong : (f g : Real.ℝ → Real.ℝ) →
    (∀ i → f (tags i) ≡ g (tags i)) →
    riemannSum f ≡ riemannSum g
  riemannSum-cong f g agree =
    ∑Ext (λ i → cong (width p i Mul.·_) (agree i))

  riemannSum-add : (f g : Real.ℝ → Real.ℝ) →
    riemannSum (λ x → f x Add.+ g x) ≡
    riemannSum f Add.+ riemannSum g
  riemannSum-add f g =
    ∑Ext (λ i →
      mul-distrib-over-add-right (width p i) (f (tags i)) (g (tags i)))
    ∙ ∑Split
      (λ i → width p i Mul.· f (tags i))
      (λ i → width p i Mul.· g (tags i))

  riemannSum-sub : (f g : Real.ℝ → Real.ℝ) →
    riemannSum (λ x → f x Group.- g x) ≡
    riemannSum f Group.- riemannSum g
  riemannSum-sub f g =
    ∑Ext (λ i →
      ℝRing.·DistR-
        (width p i) (f (tags i)) (g (tags i)))
    ∙ ∑Split-
      (λ i → width p i Mul.· f (tags i))
      (λ i → width p i Mul.· g (tags i))

  riemannSum-neg : (f : Real.ℝ → Real.ℝ) →
    riemannSum (λ x → Neg.- f x) ≡ Neg.- riemannSum f
  riemannSum-neg f =
    ∑Ext (λ i → ℝRing.-DistR· (width p i) (f (tags i)))
    ∙ ∑Dist- (λ i → width p i Mul.· f (tags i))

  riemannSum-constant : (c : Real.ℝ) →
    riemannSum (λ _ → c) ≡ (b Group.- a) Mul.· c
  riemannSum-constant c =
    sym (∑Mulldist c (width p))
    ∙ cong (Mul._· c) (totalWidth p)
