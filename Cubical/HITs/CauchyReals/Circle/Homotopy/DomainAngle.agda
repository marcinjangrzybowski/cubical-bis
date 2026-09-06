module Cubical.HITs.CauchyReals.Circle.Homotopy.DomainAngle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Homotopy.LocalLift
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open CategoryStructures using (_∘UC_)

CirclePair : PremetricSpace ℓ-zero ℓ-zero
CirclePair = PremetricProduct CirclePremetricSpace CirclePremetricSpace

private
  module C = PremetricStr (snd CirclePremetricSpace)
  module D = PremetricStr (snd distCirclePremetricSpace)
  to-β : ∀ p → fst Circle→distCircleUC p ≡ Circle→distCircle p
  to-β p = refl

opaque
  differenceAngleUC : UC[ CirclePair , ℝPremetricSpace ]
  differenceAngleUC = localAngleUC ∘UC (circleYCoordinateUC ∘UC
    addDistCircleUC (Circle→distCircleUC ∘UC productSndUC)
      (distCircleNegUC ∘UC (Circle→distCircleUC ∘UC productFstUC)))

  differenceAngle-β : ∀ p q → fst differenceAngleUC (p , q) ≡
    localAngle (snd (fst (Circle→distCircle q ℝS¹.+ (ℝS¹.- Circle→distCircle p))))
  differenceAngle-β p q = refl

opaque
  differenceAngle-local : ∀ p q → fst differenceAngleUC (p , q) ≡
    fst (localLiftUC (Circle→distCircle p) Circle→distCircleUC) q
  differenceAngle-local p q = differenceAngle-β p q
    ∙ sym (localLift-β (Circle→distCircle p) Circle→distCircleUC q)

  differenceAngle-centre : ∀ p → fst differenceAngleUC (p , p) ≡ 0
  differenceAngle-centre p = differenceAngle-local p p
    ∙ localLift-centre (Circle→distCircle p) Circle→distCircleUC p refl

  differenceAngle-cover : ∀ p q → p C.≈[ localLiftRadius ] q →
    Circle→distCircle p ℝS¹.+ cover (fst differenceAngleUC (p , q)) ≡ Circle→distCircle q
  differenceAngle-cover p q close =
    cong (Circle→distCircle p ℝS¹.+_) (cong cover (differenceAngle-local p q))
    ∙ localLift-near (Circle→distCircle p) Circle→distCircleUC q
      (subst (λ z → z D.≈[ localLiftRadius ] Circle→distCircle p) (sym (to-β q))
        (C.isSym≈ p q localLiftRadius close))
    ∙ to-β q

AngleModulus : Type
AngleModulus = Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
  (∀ p q ε → p C.≈[ μ ε ] q → fst differenceAngleUC (p , q) ∼[ ε ] 0)

differenceAngle-modulus : ∥ AngleModulus ∥₁
differenceAngle-modulus = PT.map obtain (snd differenceAngleUC)
  where
  obtain : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
    (snd CirclePair) (fst differenceAngleUC) (snd ℝPremetricSpace) μ) → AngleModulus
  obtain (μ , uc) = μ , λ p q ε close →
    subst (fst differenceAngleUC (p , q) ∼[ ε ]_) (differenceAngle-centre p)
      (≈ℝ→∼ _ _ ε (IsUniformlyContinuousWith.pres≈ uc (p , q) (p , p) ε
        (C.isRefl≈ p (μ ε) , C.isSym≈ p q (μ ε) close)))
