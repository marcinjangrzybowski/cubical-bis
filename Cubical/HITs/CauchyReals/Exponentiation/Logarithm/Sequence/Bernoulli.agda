module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Bernoulli where

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

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Convexity
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Bernoulli

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
ℚ≤→<+₊ = ℚ.≤→<+₊

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
  <ᵣ→<ℚ lowerBound upperBound realBound
  where
  exponent : ℚ
  exponent = fromNat (suc (suc n))

  lowerBound : ℚ
  lowerBound = (exponent ℚ.· (x ℚ.- 1)) ℚ.+ 1

  upperBound : ℚ
  upperBound = x ℚ^ⁿ (suc (suc n))

  basePositive : 0 ℚ.< x
  basePositive = ℚ.isTrans< 0 1 x ℚ.decℚ<? 1<x

  base : ℝ₊
  base = ℚ₊→ℝ₊ (x , ℚ<→0< x basePositive)

  one<base : 1 <ᵣ fst base
  one<base = <ℚ→<ᵣ 1 x 1<x

  one<exponent : 1 ℚ.< exponent
  one<exponent =
    <ℤ→<ℚ 1 (pos (suc (suc n)))
      (ℤ.ℕ<→pos-<-pos 1 (suc (suc n))
        (ℕ.suc-≤-suc (ℕ.zero-<-suc {n})))

  bernoulliBound :
    1 +ᵣ rat exponent ·ᵣ (fst base -ᵣ 1) <ᵣ
    fst (base ^ℚ exponent)
  bernoulliBound =
    bernoulli's-ineq-^ℚ base exponent one<base one<exponent

  lowerPath :
    1 +ᵣ rat exponent ·ᵣ (fst base -ᵣ 1) ≡ rat lowerBound
  lowerPath =
    cong (λ difference → 1 +ᵣ rat exponent ·ᵣ difference)
      (-ᵣ-rat₂ x 1)
    ∙ cong (1 +ᵣ_) (sym (rat·ᵣrat exponent (x ℚ.- 1)))
    ∙ +ᵣComm 1 (rat (exponent ℚ.· (x ℚ.- 1)))
    ∙ +ᵣ-rat (exponent ℚ.· (x ℚ.- 1)) 1

  upperPath : fst (base ^ℚ exponent) ≡ rat upperBound
  upperPath = ^ⁿ-ℚ^ⁿ (suc (suc n)) x

  realBound : rat lowerBound <ᵣ rat upperBound
  realBound =
    subst2 (λ left right → left <ᵣ right)
      lowerPath upperPath bernoulliBound
