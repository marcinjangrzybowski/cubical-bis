module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.OrderedCommRing


module ℝExponentiation = Exponentiation ℝCommRing
module ℚExponentiation = Exponentiation ℚCommRing

infix 9 _^ⁿ_

_^ⁿ_ : Real.ℝ → ℕ → Real.ℝ
_^ⁿ_ = ℝExponentiation._^_


private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing
  module ℝOrder = OrderedCommRingTheory ℝOrderedCommRing
  module ιℚPowerHom = CommRingHomTheory ιℚCommRingHom

  zeroℝ : Real.ℝ
  zeroℝ = CommRingStr.0r (snd ℝCommRing)

  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


x²EqMulSelf : ∀ x →
  x ^ⁿ 2 ≡ x Mul.· x
x²EqMulSelf = ℝExponentiation.x^2≡x·x


onePow : ∀ n → oneℝ ^ⁿ n ≡ oneℝ
onePow = ℝExponentiation.1ⁿ≡1


zeroPowSuc : ∀ n → zeroℝ ^ⁿ suc n ≡ zeroℝ
zeroPowSuc n =
  mul-zero-left (zeroℝ ^ⁿ n)


pow-ι : ∀ n q →
  Real.ιℚ q ^ⁿ n ≡ Real.ιℚ (ℚExponentiation._^_ q n)
pow-ι n q =
  sym (ιℚPowerHom.pres^ q n)


absOne : Abs.absℝ oneℝ ≡ oneℝ
absOne =
  Abs.absℝ-ι 1
  ∙ cong Real.ιℚ ℚOrder.abs1


absPow : ∀ n x →
  Abs.absℝ (x ^ⁿ n) ≡ Abs.absℝ x ^ⁿ n
absPow n x =
  ℝExponentiation.dist·→dist^
    Abs.absℝ absOne abs-mul n x


powNonnegative : ∀ x n →
  zeroℝ ≤ℝ x → zeroℝ ≤ℝ x ^ⁿ n
powNonnegative = ℝOrder.powNonnegative


powPositive : ∀ x n →
  zeroℝ <ℝ x → zeroℝ <ℝ x ^ⁿ n
powPositive = ℝOrder.powPositive


powMono : ∀ {x y} n →
  zeroℝ ≤ℝ x → x ≤ℝ y →
  x ^ⁿ n ≤ℝ y ^ⁿ n
powMono = ℝOrder.powMono


powStrictMono : ∀ {x y} n →
  zero ℕ.< n →
  zeroℝ ≤ℝ x → zeroℝ ≤ℝ y → x <ℝ y →
  x ^ⁿ n <ℝ y ^ⁿ n
powStrictMono = ℝOrder.powStrictMono


powReflects≤ : ∀ {x y} n →
  zero ℕ.< n →
  zeroℝ ≤ℝ x → zeroℝ ≤ℝ y →
  x ^ⁿ n ≤ℝ y ^ⁿ n → x ≤ℝ y
powReflects≤ = ℝOrder.powReflects≤


absPowMono : ∀ n x y →
  Abs.absℝ x ≤ℝ Abs.absℝ y →
  Abs.absℝ (x ^ⁿ n) ≤ℝ Abs.absℝ (y ^ⁿ n)
absPowMono n x y absx≤absy =
  subst2 _≤ℝ_
    (sym (absPow n x))
    (sym (absPow n y))
    (powMono n (zero≤abs x) absx≤absy)


powerOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (f : A → Real.ℝ) →
  isContinuous source f
    (snd Real.ℝPremetricSpace) →
  ∀ n →
  isContinuous source
    (λ x → f x ^ⁿ n)
    (snd Real.ℝPremetricSpace)
powerOfContinuousIsContinuous
  source f f-continuous zero x
  .IsContinuousAt.pres≈ ε =
  ∣ ε , (λ _ _ → Real.Base.isRefl≈ᶜ oneℝ ε) ∣₁
powerOfContinuousIsContinuous
  source f f-continuous (suc n) =
  mulOfContinuousIsContinuous
    source f (λ x → f x ^ⁿ n)
    f-continuous
    (powerOfContinuousIsContinuous source f f-continuous n)


powIsContinuous : ∀ n →
  isContinuous
    (snd Real.ℝPremetricSpace) (λ x → x ^ⁿ n)
    (snd Real.ℝPremetricSpace)
powIsContinuous =
  powerOfContinuousIsContinuous
    (snd Real.ℝPremetricSpace)
    (λ x → x)
    (snd (NE→C CategoryStructures.idⁿ))
