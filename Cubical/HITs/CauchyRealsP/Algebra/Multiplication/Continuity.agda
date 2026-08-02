module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.MultiplicationLaws

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  module ℝP =
    PremetricStr (snd ℝPremetricSpace)

mulIsLipschitzRAtBound : ∀ B y →
  absℝ y ≤ℝ rat (fst B) →
  IsLipschitzWith
    (snd ℝPremetricSpace)
    (λ x → x · y)
    (snd ℝPremetricSpace) B
mulIsLipschitzRAtBound B y absy≤B
  .IsLipschitzWith.pres≈ x x' ε x∼x' =
    absDifference<→closeness
      (x · y) (x' · y) (B ·₊ ε)
      (subst
        (_<ℝ rat (fst (B ·₊ ε)))
        (sym outputAbsPath)
        productStrict)
  where
  absDifferenceStrict :
    absℝ (x - x') <ℝ rat (fst ε)
  absDifferenceStrict =
    closeness→absDifference< x x' ε x∼x'

  product≤ :
    absℝ (x - x') · absℝ y
      ≤ℝ
    absℝ (x - x') · rat (fst B)
  product≤ =
    subst2 _≤ℝ_
      (mulComm (absℝ y) (absℝ (x - x')))
      (mulComm (rat (fst B)) (absℝ (x - x')))
      (mulMonoR≤
        (absℝ y) (rat (fst B))
        (absℝ (x - x'))
        (absNonnegative (x - x'))
        absy≤B)

  productStrictBeforeRationalPath :
    absℝ (x - x') · absℝ y
      <ℝ
    rat (fst ε) · rat (fst B)
  productStrictBeforeRationalPath =
    ≤<ℝ-trans
      (absℝ (x - x') · absℝ y)
      (absℝ (x - x') · rat (fst B))
      (rat (fst ε) · rat (fst B))
      product≤
      (mulMonoR<
        (absℝ (x - x')) (rat (fst ε))
        (rat (fst B))
        (<ℚ→<ℝ 0 (fst B) (snd B))
        absDifferenceStrict)

  radiusPath :
    rat (fst ε) · rat (fst B) ≡
    rat (fst (B ·₊ ε))
  radiusPath =
    mul-rat (fst ε) (fst B)
    ∙ cong rat (ℚ.·Comm (fst ε) (fst B))

  productStrict :
    absℝ (x - x') · absℝ y
      <ℝ
    rat (fst (B ·₊ ε))
  productStrict =
    subst
      (absℝ (x - x') · absℝ y <ℝ_)
      radiusPath
      productStrictBeforeRationalPath

  outputAbsPath :
    absℝ ((x · y) - (x' · y)) ≡
    absℝ (x - x') · absℝ y
  outputAbsPath =
    cong absℝ
      (sym (ℝRing.·DistL- x x' y))
    ∙ absMul (x - x') y

mulIsLipschitzLAtBound : ∀ B x →
  absℝ x ≤ℝ rat (fst B) →
  IsLipschitzWith
    (snd ℝPremetricSpace)
    (x ·_)
    (snd ℝPremetricSpace) B
mulIsLipschitzLAtBound B x absx≤B
  .IsLipschitzWith.pres≈ y y' ε y∼y' =
    subst∼
      (x · y) (x · y')
      {ε = B ·₊ ε}
      {ε' = B ·₊ ε}
      refl
      (subst2 (_∼[ B ·₊ ε ]_)
        (mulComm y x)
        (mulComm y' x)
        (IsLipschitzWith.pres≈
          (mulIsLipschitzRAtBound B x absx≤B)
          y y' ε y∼y'))

module _
  {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  where
  private
    module Source = PremetricStr source

  mulOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (snd ℝPremetricSpace) →
    isContinuous source g (snd ℝPremetricSpace) →
    isContinuous source
      (λ x → f x · g x)
      (snd ℝPremetricSpace)
  mulOfContinuousIsContinuous f g f-cont g-cont x
    .IsContinuousAt.pres≈ ε = do
    w ← jointNaturalAbsBounds (f x) (g x)
    let
      B : ℚ₊
      B =
        jointBound {x = f x} {y = g x} w

      C : ℚ₊
      C =
        B +₊ B

      absfx≤B : absℝ (f x) ≤ℝ rat (fst B)
      absfx≤B =
        jointBoundContainsLeft {x = f x} {y = g x} w

      absgx≤B : absℝ (g x) ≤ℝ rat (fst B)
      absgx≤B =
        jointBoundContainsRight {x = f x} {y = g x} w
    (δf , f-near) ←
      f-cont x .IsContinuousAt.pres≈
        ((ε /2₊) ₊／₊ B)
    (δB , f-bounded-near) ←
      f-cont x .IsContinuousAt.pres≈ B
    (δg , g-near) ←
      g-cont x .IsContinuousAt.pres≈
        ((ε /2₊) ₊／₊ C)
    let
      δ = min₊ δf (min₊ δB δg)
    return
      ( δ
      , λ y x∼δy →
        let
          x∼δfy : x Source.≈[ δf ] y
          x∼δfy =
            Source.isMonotone≈≤ x y δ δf
              (min₊≤L δf (min₊ δB δg))
              x∼δy

          x∼δBy : x Source.≈[ δB ] y
          x∼δBy =
            Source.isMonotone≈≤ x y δ δB
              (ℚ.isTrans≤
                (fst δ) (fst (min₊ δB δg)) (fst δB)
                (min₊≤R δf (min₊ δB δg))
                (min₊≤L δB δg))
              x∼δy

          x∼δgy : x Source.≈[ δg ] y
          x∼δgy =
            Source.isMonotone≈≤ x y δ δg
              (ℚ.isTrans≤
                (fst δ) (fst (min₊ δB δg)) (fst δg)
                (min₊≤R δf (min₊ δB δg))
                (min₊≤R δB δg))
              x∼δy

          fx∼fy :
            f x ∼[ (ε /2₊) ₊／₊ B ] f y
          fx∼fy =
            f-near y x∼δfy

          fx∼Bfy : f x ∼[ B ] f y
          fx∼Bfy =
            f-bounded-near y x∼δBy

          gx∼gy :
            g x ∼[ (ε /2₊) ₊／₊ C ] g y
          gx∼gy =
            g-near y x∼δgy

          absfy≤absfx+B :
            absℝ (f y) ≤ℝ absℝ (f x) + rat (fst B)
          absfy≤absfx+B =
            close→upperBound
              (absℝ (f y)) (absℝ (f x)) B
              (sym∼
                (absℝ (f x)) (absℝ (f y)) B
                (absPres∼ (f x) (f y) B fx∼Bfy))

          absfx+B≤C :
            absℝ (f x) + rat (fst B) ≤ℝ rat (fst C)
          absfx+B≤C =
            subst
              (absℝ (f x) + rat (fst B) ≤ℝ_)
              (rat+rat (fst B) (fst B))
              (≤ℝ-add
                (absℝ (f x)) (rat (fst B))
                (rat (fst B)) (rat (fst B))
                absfx≤B (≤ℝ-refl (rat (fst B))))

          absfy≤C : absℝ (f y) ≤ℝ rat (fst C)
          absfy≤C =
            ≤ℝ-trans
              (absℝ (f y))
              (absℝ (f x) + rat (fst B))
              (rat (fst C))
              absfy≤absfx+B absfx+B≤C

          firstHalf :
            (f x · g x) ∼[ ε /2₊ ] (f y · g x)
          firstHalf =
            subst∼
              (f x · g x) (f y · g x)
              {ε = B ·₊ ((ε /2₊) ₊／₊ B)}
              {ε' = ε /2₊}
              (·／ B (ε /2₊))
              (IsLipschitzWith.pres≈
                (mulIsLipschitzRAtBound B (g x) absgx≤B)
                (f x) (f y)
                ((ε /2₊) ₊／₊ B)
                fx∼fy)

          secondHalf :
            (f y · g x) ∼[ ε /2₊ ] (f y · g y)
          secondHalf =
            subst∼
              (f y · g x) (f y · g y)
              {ε = C ·₊ ((ε /2₊) ₊／₊ C)}
              {ε' = ε /2₊}
              (·／ C (ε /2₊))
              (IsLipschitzWith.pres≈
                (mulIsLipschitzLAtBound C (f y) absfy≤C)
                (g x) (g y)
                ((ε /2₊) ₊／₊ C)
                gx∼gy)
        in
          subst∼
            (f x · g x) (f y · g y)
            {ε = (ε /2₊) +₊ (ε /2₊)}
            {ε' = ε}
            (1/2∈ℚ./2+/2≡id (fst ε))
            (triangle∼
              (f x · g x) (f y · g x) (f y · g y)
              (ε /2₊) (ε /2₊)
              firstHalf secondHalf))
