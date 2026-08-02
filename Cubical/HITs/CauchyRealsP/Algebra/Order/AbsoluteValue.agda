module Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Properties.Lift

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing

  rationalAbsNE :
    IsNonExpanding
      (snd ℚPremetricSpace)
      (λ q → rat (abs q))
      (snd ℝPremetricSpace)
  rationalAbsNE .IsNonExpanding.pres≈ x y ε x∼y =
    rat-rat _ _ ε
      (ℚ.isTrans≤< _ _ _
        (ℚ.absFrom≤×≤
          (abs (x ℚ.- y))
          (abs x ℚ.- abs y)
          (subst2 ℚ._≤_
            (cong ℚ.-_ (sym (ℚOrder.abs-Comm x y)))
            ℚ!
            (ℚ.minus-≤
              (abs y ℚ.- abs x)
              (abs (y ℚ.- x))
              (ℚOrder.abs-abs≤abs- y x)))
          (ℚOrder.abs-abs≤abs- x y))
        x∼y)

  rationalAbs : NE[ ℚPremetricSpace , ℝPremetricSpace ]
  rationalAbs = (λ q → rat (abs q)) , rationalAbsNE

  module AbsExtension =
    LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ

  absExtension =
    AbsExtension.liftNonExpandingExtension rationalAbs

absℝ : ℝ → ℝ
absℝ = fst (fst absExtension)

abs-rat : ∀ q → absℝ (rat q) ≡ rat (abs q)
abs-rat = funExt⁻ (snd absExtension)

absIsNonExpanding :
  IsNonExpanding (snd ℝPremetricSpace) absℝ (snd ℝPremetricSpace)
absIsNonExpanding = snd (fst absExtension)

absPres∼ : ∀ x y ε →
  x ∼[ ε ] y → absℝ x ∼[ ε ] absℝ y
absPres∼ x y ε =
  IsNonExpanding.pres≈ absIsNonExpanding x y ε

private
  signedMaxIsLipschitzWith2 :
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → maxℝ x (- x))
      (snd ℝPremetricSpace) 2
  signedMaxIsLipschitzWith2
    .IsLipschitzWith.pres≈ x y ε x∼y =
      subst∼
        (maxℝ x (- x)) (maxℝ y (- y))
        {ε = ε +₊ ε} {ε' = 2 ·₊ ε}
        ℚ!
        (maxPres∼ x y (- x) (- y) ε ε
          x∼y (negPres∼ x y ε x∼y))

absAsMax : ∀ x → absℝ x ≡ maxℝ x (- x)
absAsMax =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      absℝ (λ x → maxℝ x (- x))
      (isNonExpanding→isLipschitz
        (snd ℝPremetricSpace) absℝ
        (snd ℝPremetricSpace) absIsNonExpanding)
      ∣ 2 , signedMaxIsLipschitzWith2 ∣₁
      λ q →
        abs-rat q
        ∙ sym
            (cong (maxℝ (rat q)) (neg-rat q)
            ∙ max-rat q (ℚ.- q)))

leAbs : ∀ x → x ≤ℝ absℝ x
leAbs x =
  subst (x ≤ℝ_) (sym (absAsMax x))
    (left≤max x (- x))

negLeAbs : ∀ x → (- x) ≤ℝ absℝ x
negLeAbs x =
  subst ((- x) ≤ℝ_) (sym (absAsMax x))
    (right≤max x (- x))

opaque
  unfolding _≤ℝ_

  absNonnegative : ∀ x → 0 ≤ℝ absℝ x
  absNonnegative =
    funExt⁻
      (nonExpandingExtensionality
        ℝPremetricSpace
        (λ x → maxℝ 0 (absℝ x))
        absℝ
        maxAfterAbsNE absIsNonExpanding
        λ q →
          cong (maxℝ 0) (abs-rat q)
          ∙ max-rat 0 (abs q)
          ∙ cong rat (ℚ.≤→max 0 (abs q) (ℚOrder.0≤abs q))
          ∙ sym (abs-rat q))
    where
    maxAfterAbsNE :
      IsNonExpanding
        (snd ℝPremetricSpace)
        (λ x → maxℝ 0 (absℝ x))
        (snd ℝPremetricSpace)
    maxAfterAbsNE .IsNonExpanding.pres≈ x y ε x∼y =
      maxPres∼₂ 0 (absℝ x) (absℝ y) ε
        (absPres∼ x y ε x∼y)

absNeg : ∀ x → absℝ (- x) ≡ absℝ x
absNeg x =
  absAsMax (- x)
  ∙ cong (maxℝ (- x)) (negInvol x)
  ∙ maxComm (- x) x
  ∙ sym (absAsMax x)

absZero : absℝ 0 ≡ 0
absZero =
  abs-rat 0
  ∙ cong rat ℚOrder.abs0

absOfNonnegative : ∀ x → 0 ≤ℝ x → absℝ x ≡ x
absOfNonnegative x 0≤x =
  ≤ℝ-antisym (absℝ x) x
    (subst (_≤ℝ x) (sym (absAsMax x))
      (max≤ x (- x) x
        (≤ℝ-refl x)
        (≤ℝ-trans (- x) 0 x
          (subst ((- x) ≤ℝ_) negZero (≤ℝ-neg 0 x 0≤x))
          0≤x)))
    (leAbs x)

absOfNonpositive : ∀ x → x ≤ℝ 0 → absℝ x ≡ - x
absOfNonpositive x x≤0 =
  ≤ℝ-antisym (absℝ x) (- x)
    (subst (_≤ℝ (- x)) (sym (absAsMax x))
      (max≤ x (- x) (- x)
        (≤ℝ-trans x 0 (- x)
          x≤0
          (subst (_≤ℝ (- x)) negZero (≤ℝ-neg x 0 x≤0)))
        (≤ℝ-refl (- x))))
    (negLeAbs x)

absIdem : ∀ x → absℝ (absℝ x) ≡ absℝ x
absIdem x = absOfNonnegative (absℝ x) (absNonnegative x)

absEqZero→EqZero : ∀ x → absℝ x ≡ 0 → x ≡ 0
absEqZero→EqZero x absx≡0 =
  ≤ℝ-antisym x 0
    (subst (x ≤ℝ_) absx≡0 (leAbs x))
    (subst2 _≤ℝ_ negZero (negInvol x)
      (≤ℝ-neg (- x) 0
        (subst ((- x) ≤ℝ_) absx≡0 (negLeAbs x))))

absTriangle : ∀ x y →
  absℝ (x + y) ≤ℝ absℝ x + absℝ y
absTriangle x y =
  subst (_≤ℝ (absℝ x + absℝ y))
    (sym (absAsMax (x + y)))
    (max≤
      (x + y) (- (x + y))
      (absℝ x + absℝ y)
      (≤ℝ-add x (absℝ x) y (absℝ y)
        (leAbs x) (leAbs y))
      (subst (_≤ℝ (absℝ x + absℝ y))
        (sym (negAdd x y))
        (≤ℝ-add (- x) (absℝ x) (- y) (absℝ y)
          (negLeAbs x) (negLeAbs y))))

absSubTriangle : ∀ x y →
  absℝ (x - y) ≤ℝ absℝ x + absℝ y
absSubTriangle x y =
  subst (absℝ (x - y) ≤ℝ_)
    (cong (absℝ x +_) (absNeg y))
    (absTriangle x (- y))

absSubComm : ∀ x y → absℝ (x - y) ≡ absℝ (y - x)
absSubComm x y =
  sym (absNeg (x - y))
  ∙ cong absℝ (negSub x y)
