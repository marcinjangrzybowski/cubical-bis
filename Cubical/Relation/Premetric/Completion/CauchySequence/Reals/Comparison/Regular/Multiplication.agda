module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Multiplication where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.HITs.CauchyRealsP.Foundation.Closeness as CR
import Cubical.HITs.CauchyRealsP.Foundation.Approximation as CRApprox
import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue as CRAbs
import Cubical.HITs.CauchyRealsP.Algebra.Order.Base as CROrder
import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition as CROrderAdd
import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric as CRMetric
import Cubical.HITs.CauchyRealsP.Algebra.Addition as CRAdd
import Cubical.HITs.CauchyRealsP.Algebra.Multiplication as CRMul
import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Continuity as CRMulCont

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as RealMul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular
  as Comparison
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition


private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

  module CRP = PremetricStr (snd CR.ℝPremetricSpace)

  multiplicationGraph : ℚ → ℚ → Real.ℝ
  multiplicationGraph p q =
    Real.ιℚ (RealMul.rationalMultiplication p q)


opaque
  regularMultiplicationGraph : ∀ x y →
    B.BaseGraphClosure RealMul.rationalMultiplication
      (Comparison.fromRegular x)
      (Comparison.fromRegular y)
      (Comparison.fromRegular (CRMul._·_ x y))
  regularMultiplicationGraph x y α β γ =
    PT.rec squash₁ withBound (CRMul.jointNaturalAbsBounds x y)
    where
    withBound : CRMul.JointNaturalAbsBounds x y →
      ∥ Σ[ p ∈ ℚ ]
          Σ[ q ∈ ℚ ]
            (Real.ιℚ p Real.Base.≈ᶜ[ α ]
              Comparison.fromRegular x) ×
            (Real.ιℚ q Real.Base.≈ᶜ[ β ]
              Comparison.fromRegular y) ×
            (Real.ιℚ (RealMul.rationalMultiplication p q)
              Real.Base.≈ᶜ[ γ ]
              Comparison.fromRegular
                (CRMul._·_ x y)) ∥₁
    withBound w =
      PT.rec2 squash₁ combine
        (CRApprox.∃ratApprox x leftRadius)
        (CRApprox.∃ratApprox y rightRadius)
      where
      B₀ : ℚ₊
      B₀ = CRMul.jointBound {x = x} {y = y} w

      C : ℚ₊
      C = B₀ +₊ B₀

      leftScale rightScale : ℚ₊
      leftScale = (γ /2₊) ₊／₊ C
      rightScale = (γ /2₊) ₊／₊ B₀

      leftRadius rightRadius : ℚ₊
      leftRadius = min₊ α leftScale /2₊
      rightRadius = min₊ β (min₊ B₀ rightScale) /2₊

      leftRadius<α : leftRadius <₊ α
      leftRadius<α = min/2₊<L α leftScale

      leftRadius<leftScale : leftRadius <₊ leftScale
      leftRadius<leftScale = min/2₊<R α leftScale

      rightRadius<β : rightRadius <₊ β
      rightRadius<β = min/2₊<L β (min₊ B₀ rightScale)

      rightRadius<B : rightRadius <₊ B₀
      rightRadius<B =
        ℚ.isTrans<≤ _ (fst (min₊ B₀ rightScale)) _
          (min/2₊<R β (min₊ B₀ rightScale))
          (min₊≤L B₀ rightScale)

      rightRadius<rightScale : rightRadius <₊ rightScale
      rightRadius<rightScale =
        ℚ.isTrans<≤ _ (fst (min₊ B₀ rightScale)) _
          (min/2₊<R β (min₊ B₀ rightScale))
          (min₊≤R B₀ rightScale)

      absx≤B : CRAbs.absℝ x CROrder.≤ℝ CR.rat (fst B₀)
      absx≤B = CRMul.jointBoundContainsLeft {x = x} {y = y} w

      absy≤B : CRAbs.absℝ y CROrder.≤ℝ CR.rat (fst B₀)
      absy≤B = CRMul.jointBoundContainsRight {x = x} {y = y} w

      combine :
        ( Σ[ p ∈ ℚ ] CR.rat p CR.∼[ leftRadius ] x ) →
        ( Σ[ q ∈ ℚ ] CR.rat q CR.∼[ rightRadius ] y ) →
        ∥ Σ[ p ∈ ℚ ]
            Σ[ q ∈ ℚ ]
              (Real.ιℚ p Real.Base.≈ᶜ[ α ]
                Comparison.fromRegular x) ×
              (Real.ιℚ q Real.Base.≈ᶜ[ β ]
                Comparison.fromRegular y) ×
              (Real.ιℚ (RealMul.rationalMultiplication p q)
                Real.Base.≈ᶜ[ γ ]
                Comparison.fromRegular
                  (CRMul._·_ x y)) ∥₁
      combine (p , p∼x) (q , q∼y) =
        ∣ p , q , leftClose , rightClose , productClose ∣₁
        where
        p∼xAtScale : CR.rat p CR.∼[ leftScale ] x
        p∼xAtScale =
          CRP.isMonotone≈< _ _ leftRadius leftScale
            leftRadius<leftScale p∼x

        q∼yAtScale : CR.rat q CR.∼[ rightScale ] y
        q∼yAtScale =
          CRP.isMonotone≈< _ _ rightRadius rightScale
            rightRadius<rightScale q∼y

        q∼yAtB : CR.rat q CR.∼[ B₀ ] y
        q∼yAtB =
          CRP.isMonotone≈< _ _ rightRadius B₀
            rightRadius<B q∼y

        absq≤absy+B :
          CRAbs.absℝ (CR.rat q) CROrder.≤ℝ
          CRAdd._+_ (CRAbs.absℝ y) (CR.rat (fst B₀))
        absq≤absy+B =
          CRMetric.close→upperBound
            (CRAbs.absℝ (CR.rat q)) (CRAbs.absℝ y) B₀
            (CRAbs.absPres∼ (CR.rat q) y B₀ q∼yAtB)

        absy+B≤C :
          CRAdd._+_ (CRAbs.absℝ y) (CR.rat (fst B₀))
            CROrder.≤ℝ CR.rat (fst C)
        absy+B≤C =
          subst
            (CRAdd._+_ (CRAbs.absℝ y) (CR.rat (fst B₀))
              CROrder.≤ℝ_)
            (CRAdd.rat+rat (fst B₀) (fst B₀))
            (CROrderAdd.≤ℝ-add
              (CRAbs.absℝ y) (CR.rat (fst B₀))
              (CR.rat (fst B₀)) (CR.rat (fst B₀))
              absy≤B (CROrder.≤ℝ-refl (CR.rat (fst B₀))))

        absq≤C : CRAbs.absℝ (CR.rat q) CROrder.≤ℝ CR.rat (fst C)
        absq≤C = CROrder.≤ℝ-trans
          (CRAbs.absℝ (CR.rat q))
          (CRAdd._+_ (CRAbs.absℝ y) (CR.rat (fst B₀)))
          (CR.rat (fst C)) absq≤absy+B absy+B≤C

        firstHalfRaw :
          CRMul._·_ (CR.rat p) (CR.rat q) CR.∼[ γ /2₊ ]
          CRMul._·_ x (CR.rat q)
        firstHalfRaw =
          subst∼ _ _
            {ε = C ·₊ leftScale} {ε' = γ /2₊}
            (·／ C (γ /2₊))
            (CRMulCont.mulIsLipschitzRAtBound C (CR.rat q) absq≤C
              .IsLipschitzWith.pres≈
                (CR.rat p) x leftScale p∼xAtScale)

        firstHalf :
          CR.rat (RealMul.rationalMultiplication p q) CR.∼[ γ /2₊ ]
          CRMul._·_ x (CR.rat q)
        firstHalf =
          subst
            (CR._∼[ γ /2₊ ] CRMul._·_ x (CR.rat q))
            (CRMul.mul-rat p q) firstHalfRaw

        secondHalf :
          CRMul._·_ x (CR.rat q) CR.∼[ γ /2₊ ]
          CRMul._·_ x y
        secondHalf =
          subst∼ _ _
            {ε = B₀ ·₊ rightScale} {ε' = γ /2₊}
            (·／ B₀ (γ /2₊))
            (CRMulCont.mulIsLipschitzLAtBound B₀ x absx≤B
              .IsLipschitzWith.pres≈
                (CR.rat q) y rightScale q∼yAtScale)

        rationalProductClose :
          CR.rat (RealMul.rationalMultiplication p q) CR.∼[ γ ]
          CRMul._·_ x y
        rationalProductClose =
          subst
            (λ ρ → CR.rat (RealMul.rationalMultiplication p q)
              CR.∼[ ρ ] CRMul._·_ x y)
            (ℚ₊≡ (/2+/2≡id (fst γ)))
            (CR.triangle∼
              (CR.rat (RealMul.rationalMultiplication p q))
              (CRMul._·_ x (CR.rat q))
              (CRMul._·_ x y)
              (γ /2₊) (γ /2₊) firstHalf secondHalf)

        leftClose :
          Real.ιℚ p Real.Base.≈ᶜ[ α ]
          Comparison.fromRegular x
        leftClose =
          Real.Base.isMonotone≈ᶜ< _ _ leftRadius α leftRadius<α
            (subst
              (λ z → z Real.Base.≈ᶜ[ leftRadius ]
                Comparison.fromRegular x)
              (Comparison.fromRegular-rat p)
              (Comparison.fromRegular-pres≈ p∼x))

        rightClose :
          Real.ιℚ q Real.Base.≈ᶜ[ β ]
          Comparison.fromRegular y
        rightClose =
          Real.Base.isMonotone≈ᶜ< _ _ rightRadius β rightRadius<β
            (subst
              (λ z → z Real.Base.≈ᶜ[ rightRadius ]
                Comparison.fromRegular y)
              (Comparison.fromRegular-rat q)
              (Comparison.fromRegular-pres≈ q∼y))

        productClose :
          Real.ιℚ (RealMul.rationalMultiplication p q)
            Real.Base.≈ᶜ[ γ ]
          Comparison.fromRegular (CRMul._·_ x y)
        productClose =
          subst
            (λ z → z Real.Base.≈ᶜ[ γ ]
              Comparison.fromRegular (CRMul._·_ x y))
            (Comparison.fromRegular-rat
              (RealMul.rationalMultiplication p q))
            (Comparison.fromRegular-pres≈
              rationalProductClose)


fromRegular-presMultiplication : ∀ x y →
  Comparison.fromRegular (CRMul._·_ x y) ≡
  RealMul._·_
    (Comparison.fromRegular x)
    (Comparison.fromRegular y)
fromRegular-presMultiplication x y =
  sym
    (B.graphClosureUnique multiplicationGraph
      RealMul.rationalMultiplication-preservesCauchyGraphs
      (Comparison.fromRegular x)
      (Comparison.fromRegular y)
      _ _
      (RealMul.multiplication-joint
        (Comparison.fromRegular x)
        (Comparison.fromRegular y))
      (regularMultiplicationGraph x y))
