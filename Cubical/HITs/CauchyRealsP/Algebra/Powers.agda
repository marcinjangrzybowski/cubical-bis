module Cubical.HITs.CauchyRealsP.Algebra.Powers where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import
  Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Continuity
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Structure
open import Cubical.HITs.CauchyRealsP.Algebra.Order.MultiplicationLaws

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

module ℝExponentiation = Exponentiation ℝCommRing

infix 9 _^ⁿ_

_^ⁿ_ : ℝ → ℕ → ℝ
_^ⁿ_ =
  ℝExponentiation._^_

private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  module ℝOrder =
    OrderedCommRingTheory ℝOrderedCommRing

  module RatPowerHom =
    CommRingHomTheory ratCommRingHom

x²EqMulSelf : ∀ x →
  x ^ⁿ 2 ≡ x · x
x²EqMulSelf =
  ℝExponentiation.x^2≡x·x

pow-rat : ∀ n q →
  rat q ^ⁿ n ≡ rat (q ℚ.^ⁿ n)
pow-rat n q =
  sym (RatPowerHom.pres^ q n)

powerOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (f : A → ℝ) →
  isContinuous source f
    (snd ℝPremetricSpace) →
  ∀ n →
  isContinuous source
    (λ x → f x ^ⁿ n)
    (snd ℝPremetricSpace)
powerOfContinuousIsContinuous
  source f f-continuous zero x
  .IsContinuousAt.pres≈ ε =
    return
      ( 1
      , λ _ _ → refl∼ 1 ε
      )
powerOfContinuousIsContinuous
  source f f-continuous (suc n) =
  mulOfContinuousIsContinuous
    source
    f
    (λ x → f x ^ⁿ n)
    f-continuous
    (powerOfContinuousIsContinuous
      source f f-continuous n)

powIsContinuous : ∀ n →
  isContinuous
    (snd ℝPremetricSpace)
    (λ x → x ^ⁿ n)
    (snd ℝPremetricSpace)
powIsContinuous =
  powerOfContinuousIsContinuous
    (snd ℝPremetricSpace)
    (λ x → x)
    (snd
      (CategoryStructures.idᶜ
        {M = ℝPremetricSpace}))

absOne : absℝ 1 ≡ 1
absOne =
  abs-rat 1
  ∙ cong rat ℚOrder.abs1

absPow : ∀ n x →
  absℝ (x ^ⁿ n) ≡ absℝ x ^ⁿ n
absPow n x =
  ℝExponentiation.dist·→dist^ absℝ absOne absMul n x

powNonnegativeℝ : ∀ x n →
  0 ≤ℝ x →
  0 ≤ℝ x ^ⁿ n
powNonnegativeℝ =
  ℝOrder.powNonnegative

powPositiveℝ : ∀ x n →
  0 <ℝ x →
  0 <ℝ x ^ⁿ n
powPositiveℝ =
  ℝOrder.powPositive

powMonoℝ : ∀ {x y} n →
  0 ≤ℝ x →
  x ≤ℝ y →
  x ^ⁿ n ≤ℝ y ^ⁿ n
powMonoℝ =
  ℝOrder.powMono

absPowMono : ∀ n x y →
  absℝ x ≤ℝ absℝ y →
  absℝ (x ^ⁿ n) ≤ℝ absℝ (y ^ⁿ n)
absPowMono n x y absx≤absy =
  subst2 _≤ℝ_
    (sym (absPow n x))
    (sym (absPow n y))
    (powMonoℝ n (absNonnegative x) absx≤absy)
