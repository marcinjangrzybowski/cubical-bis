module Cubical.HITs.CauchyReals.Circle.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_;_choose_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_ ; ^ⁿ-even)


open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; fromNatℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds using (abs<→ointerval)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base using (interpℝ)
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base using (invℚ₊ ; isEquiv-₊^ⁿ)

open import Cubical.Algebra.Ring.BigOps

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.PNorm
open import Cubical.HITs.CauchyReals.Analysis.Metric.Product
open import Cubical.Relation.Premetric.Base using (PremetricSpace)
open import Cubical.Relation.Premetric.Mappings using (NE[_,_]; UC[_,_]; NE→UC)
open import Cubical.Relation.Premetric.Instances.Subspace
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  ( sin
  ; cos
  ; sin·sin+cos·cos=1
  ; cos·cos=1-sin·sin
  ; cos0=1
  ; sin0=0
  ; cos-even
  ; sin-odd
  )
open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic using
  ( ∣x∣<π/2→0<cos[x] )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base using
  ( arcSin⟨⟩
  ; arcSin⟨⟩∈
  )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Inverse using
  ( sin∘arcSin⟨⟩
  ; arcSin⟨⟩∘sin
  )
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Equivalence public
open import Cubical.HITs.CauchyReals.Circle.Group public
open import Cubical.HITs.CauchyReals.Circle.Chart public

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

distCircleMetricSpaceStr : MetricSpaceStr distCircle
distCircleMetricSpaceStr =
 MetricSubSpaceStr (ℝ × ℝ)
  (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)
  𝐑²MetricSpaceStr

distCircleMetricSpace : MetricSpace₀
distCircleMetricSpace = _ , distCircleMetricSpaceStr


distCirclePremetricSpace : PremetricSpace ℓ-zero ℓ-zero
distCirclePremetricSpace =
  PremetricSubspace ℝ²PremetricSpace
    (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)


distCircleInclusionNE :
  NE[ distCirclePremetricSpace , ℝ²PremetricSpace ]
distCircleInclusionNE =
  subspaceInclusionNE ℝ²PremetricSpace
    (λ z → (cartNorm² z ≡ 1) , isSetℝ _ _)


distCircleInclusionUC :
  UC[ distCirclePremetricSpace , ℝ²PremetricSpace ]
distCircleInclusionUC = NE→UC distCircleInclusionNE


[x-y][x-y]≡xx-2xy+yy : ∀ x y →
  (x -ᵣ y) ·ᵣ (x -ᵣ y) ≡
    x ·ᵣ x +ᵣ (-ᵣ (2 ·ᵣ (x ·ᵣ y) )) +ᵣ y ·ᵣ y
[x-y][x-y]≡xx-2xy+yy x y =
  ℝ! ∙ cong₂ _+ᵣ_
   (cong₂ _-ᵣ_  refl (x+x≡2x _) )
    refl
opaque

 cartDist≃upperHalf :  (p : distCircle) →
    (cartDist² (fst circle0) (fst p) <ᵣ 2)
     ≃ (0 <ᵣ fst (fst p))
 cartDist≃upperHalf ((x , y) , p) =
        subst2Equiv _<ᵣ_
          ( (cong cartNorm²
             (cong₂ _,_
               refl
               (+IdL _))
           ∙ (cong₂ _+ᵣ_
              ([x-y][x-y]≡xx-2xy+yy 1 x)
              (-ᵣ·-ᵣ y y)
           ∙ sym (+ᵣAssoc _ _ _))
           ∙ sym (+ᵣAssoc _ _ _)
           ∙ cong₂ _+ᵣ_ refl (+ᵣComm _ _)
           ∙ +ᵣAssoc _ _ _ )
           ∙ cong₂ (_-ᵣ_)
              ( cong₂ (_+ᵣ_) (·IdR _) p ∙  (+ᵣ-rat 1 1)  )
               (cong (2 ·ᵣ_) (Rℝ.·IdL x)))
          (sym (-ᵣ-rat₂ _ _) ∙
            cong₂ _-ᵣ_ refl (rat·ᵣrat _ _))
     ∙ₑ x+y<x+z≃y<z 2 _ _
     ∙ₑ invEquiv (x<y≃-y<-x _ _)
     ∙ₑ invEquiv (z<x≃y₊·z<y₊·x x 0 2)
