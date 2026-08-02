module Cubical.HITs.CauchyRealsP.Algebra.Order.MultiplicationLaws where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Associativity
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Structure

private
  module ℝOrder =
    OrderedCommRingTheory ℝOrderedCommRing

  module ℝPower =
    Exponentiation ℝCommRing

  squareNonnegativeInjective :
    ∀ {x y} →
    0 ≤ℝ x →
    0 ≤ℝ y →
    x · x ≡ y · y →
    x ≡ y
  squareNonnegativeInjective {x} {y} 0≤x 0≤y x²≡y² =
    ≤ℝ-antisym x y x≤y y≤x
    where
    0<2 : 0 ℕ.< 2
    0<2 = ℕ.suc-≤-suc ℕ.zero-≤

    x²≤y² : ℝPower._^_ x 2 ≤ℝ ℝPower._^_ y 2
    x²≤y² =
      subst2 _≤ℝ_
        (sym (ℝPower.x^2≡x·x x))
        (sym (ℝPower.x^2≡x·x y))
        (subst (x · x ≤ℝ_) x²≡y² (≤ℝ-refl (x · x)))

    y²≤x² : ℝPower._^_ y 2 ≤ℝ ℝPower._^_ x 2
    y²≤x² =
      subst2 _≤ℝ_
        (sym (ℝPower.x^2≡x·x y))
        (sym (ℝPower.x^2≡x·x x))
        (subst (y · y ≤ℝ_) (sym x²≡y²) (≤ℝ-refl (y · y)))

    x≤y : x ≤ℝ y
    x≤y =
      ℝOrder.powReflects≤ 2 0<2 0≤x 0≤y x²≤y²

    y≤x : y ≤ℝ x
    y≤x =
      ℝOrder.powReflects≤ 2 0<2 0≤y 0≤x y²≤x²

  rearrangeProductSquare : ∀ a b →
    (a · b) · (a · b) ≡
    (a · a) · (b · b)
  rearrangeProductSquare a b =
    sym (mulAssoc (a · b) a b)
    ∙ cong (_· b) (mulAssoc a b a)
    ∙ cong (λ z → (a · z) · b) (mulComm b a)
    ∙ mulAssoc a (a · b) b
    ∙ cong (a ·_) (mulAssoc a b b)
    ∙ sym (mulAssoc a a (b · b))

absSquare : ∀ x →
  absℝ x · absℝ x ≡ x · x
absSquare x =
  cong (λ z → z · z) (absAsMax x)
  ∙ ℝOrder.abs²≡² x

private
  rearrangeAbsSquare : ∀ x y →
    (absℝ x · absℝ y) · (absℝ x · absℝ y) ≡
    (absℝ x · absℝ x) · (absℝ y · absℝ y)
  rearrangeAbsSquare x y =
    rearrangeProductSquare (absℝ x) (absℝ y)

absMul : ∀ x y →
  absℝ (x · y) ≡ absℝ x · absℝ y
absMul x y =
  squareNonnegativeInjective
    (absNonnegative (x · y))
    (mulNonnegative
      (absℝ x) (absℝ y)
      (absNonnegative x) (absNonnegative y))
    (absSquare (x · y) ∙ sym productAbsSquare)
  where
  productAbsSquare :
    (absℝ x · absℝ y) · (absℝ x · absℝ y) ≡
    (x · y) · (x · y)
  productAbsSquare =
    (absℝ x · absℝ y) · (absℝ x · absℝ y)
      ≡⟨ rearrangeAbsSquare x y ⟩
    (absℝ x · absℝ x) · (absℝ y · absℝ y)
      ≡⟨ cong₂ _·_ (absSquare x) (absSquare y) ⟩
    (x · x) · (y · y)
      ≡⟨ sym (rearrangeProductSquare x y) ⟩
    (x · y) · (x · y) ∎
