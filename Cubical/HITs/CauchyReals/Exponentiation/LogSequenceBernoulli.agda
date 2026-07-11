{-# OPTIONS --safe --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.LogSequenceBernoulli where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (seqΣ ; seqΣ' ; _^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using
  ( invℚ
  ; _⁻¹₊
  ; x/y<z→x<y·z
  )

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisection
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Partition using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.CauchyReals.Exponentiation.Core
open import Cubical.HITs.CauchyReals.Exponentiation.Convexity

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.CommRing.Properties as CR

module 𝐙' = RingTheory (CR.CommRing→Ring ℤCRing.ℤCommRing )

ℚ≤→<+₊ : ∀ x y (ε : ℚ₊) → x ℚ.≤ y → x ℚ.< y ℚ.+ fst ε
ℚ≤→<+₊ x y ε x≤y =
  subst (λ z → z ℚ.< y ℚ.+ fst ε) (ℚ.+IdR x)
    (ℚ.≤<Monotone+ x y 0 (fst ε) x≤y (snd ε))

private
  2ℝ₊ : ℝ₊
  2ℝ₊ = fromNat 2

  2₊ : ℚ₊
  2₊ = fromNat 2

opaque
 unfolding invℝ
 bernoulli's-ineq-^ℚⁿ : ∀ x n → 1 ℚ.< x
  →
   ((fromNat (suc (suc n))) ℚ.· (x ℚ.- 1)) ℚ.+ 1  ℚ.< (x ℚ^ⁿ (suc (suc n)))
 bernoulli's-ineq-^ℚⁿ x n 1<x =
  <ᵣ→<ℚ _ _
    (subst2 _<ᵣ_
      (cong (1 +ᵣ_) (sym (rat·ᵣrat _ _)) ∙  +ᵣComm _ _) (^ⁿ-ℚ^ⁿ (suc (suc n)) x)
      (bernoulli's-ineq-^ℚ (ℚ₊→ℝ₊ (x ,
        ℚ<→0< _ (ℚ.isTrans< 0 1 _ (ℚ.0<pos  _ _) 1<x)))
        (fromNat (suc (suc n))) (<ℚ→<ᵣ _ _ 1<x)
          (<ℤ→<ℚ _ _ (ℤ.ℕ<→pos-<-pos _ _
            (ℕ.suc-≤-suc (ℕ.zero-<-suc {n}))))))



