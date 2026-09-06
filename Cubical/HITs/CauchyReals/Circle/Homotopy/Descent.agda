module Cubical.HITs.CauchyReals.Circle.Homotopy.Descent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using (∼-monotone≤)
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra using (circle-image-injective)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.RealPaths
open import Cubical.HITs.CauchyReals.Circle.Homotopy.LocalLift
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Overlap
open import Cubical.HITs.CauchyReals.Circle.Homotopy.DomainAngle
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  ε-overlap : ℝ₊
  ε-overlap = ℚ₊→ℝ₊ ([ 1 / 2 ]₊)
  Inside : ℝ → Type
  Inside r = r ∈ ointervalℙ 0 (1 +ᵣ fst ε-overlap)
  module C = PremetricStr (snd CirclePremetricSpace)
  module R = PremetricStr (snd ℝPremetricSpace)

  opaque
    inner-inside : ∀ r → rat [ 1 / 8 ] <ᵣ r → r <ᵣ rat [ 5 / 4 ] → Inside r
    inner-inside r lower upper = isTrans<ᵣ 0 (rat [ 1 / 8 ]) r decℚ<ᵣ? lower ,
      isTrans<ᵣ r (rat [ 5 / 4 ]) _ upper
        (isTrans<≡ᵣ _ (rat [ 3 / 2 ]) _ decℚ<ᵣ? (sym (+ᵣ-rat 1 [ 1 / 2 ])))

    perturb-inside : ∀ r d → rat [ 1 / 8 ] <ᵣ r → r <ᵣ rat [ 5 / 4 ] →
      (-ᵣ rat [ 1 / 8 ]) <ᵣ d → d <ᵣ rat [ 1 / 8 ] → Inside (r +ᵣ d)
    perturb-inside r d rlo rhi dlo dhi =
      isTrans≡<ᵣ _ _ _ ℝ!
        (<ᵣMonotone+ᵣ (rat [ 1 / 8 ]) r (-ᵣ rat [ 1 / 8 ]) d rlo dlo) ,
      isTrans<ᵣ _ (rat [ 5 / 4 ] +ᵣ rat [ 1 / 8 ]) _
        (<ᵣMonotone+ᵣ r (rat [ 5 / 4 ]) d (rat [ 1 / 8 ]) rhi dhi)
        (subst2 _<ᵣ_ (sym (+ᵣ-rat [ 5 / 4 ] [ 1 / 8 ])) (sym (+ᵣ-rat 1 [ 1 / 2 ])) decℚ<ᵣ?)

module CircleDescent (h : RealPath)
  (periodic : ∀ t → -1 ≤ᵣ t → t ≤ᵣ 1 → fst h (t +ᵣ 1) ≡ fst h t) where

  private
    chart : CircleOverlap[ ε-overlap ] → ℝ
    chart = SQ.rec isSetℝ (λ (r , _) → fst h r)
      (λ (x , xlo , xhi) (y , ylo , yhi) related → overlap-respects (fst h) periodic x y
        xlo (isTrans<≡ᵣ _ _ _ xhi (+ᵣ-rat 1 [ 1 / 2 ]))
        ylo (isTrans<≡ᵣ _ _ _ yhi (+ᵣ-rat 1 [ 1 / 2 ])) related)

  opaque
    descend : Circle → ℝ
    descend p = chart (invEq (overlapCircleEquivalence ε-overlap) p)

    descend-β : ∀ r → Inside r → descend (injCircle r) ≡ fst h r
    descend-β r inside = cong chart
      (cong (invEq (overlapCircleEquivalence ε-overlap)) (sym (overlapCircle-β ε-overlap r inside))
        ∙ retEq (overlapCircleEquivalence ε-overlap) SQ.[ (r , inside) ])

    descend-bounded : (B : ℝ₊) → (∀ t → absᵣ (fst h t) ≤ᵣ fst B) → ∀ p → absᵣ (descend p) ≤ᵣ fst B
    descend-bounded B bounded p = chart-bound (invEq (overlapCircleEquivalence ε-overlap) p)
      where
      chart-bound : ∀ z → absᵣ (chart z) ≤ᵣ fst B
      chart-bound = SQ.elimProp (λ _ → isProp≤ᵣ _ _) (λ (r , _) → bounded r)

  private
    descend-at : ∀ r → Inside r → ∀ p → injCircle r ≡ p → descend p ≡ fst h r
    descend-at r inside p represents = sym (cong descend represents) ∙ descend-β r inside

    perturb-represents : ∀ r p q → injCircle r ≡ p → p C.≈[ localLiftRadius ] q →
      injCircle (r +ᵣ fst differenceAngleUC (p , q)) ≡ q
    perturb-represents r p q represents close = circle-image-injective _ _
      (sym (cover-β _) ∙ cover-add r (fst differenceAngleUC (p , q))
        ∙ cong (ℝS¹._+ cover (fst differenceAngleUC (p , q)))
          (cover-β r ∙ cong Circle→distCircle represents)
        ∙ differenceAngle-cover p q close)

    continuity :
      (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
        (snd ℝPremetricSpace) (fst h) (snd ℝPremetricSpace) ν) →
      AngleModulus → Σ[ δ ∈ (ℚ₊ → ℚ₊) ]
        IsUniformlyContinuousWith (snd CirclePremetricSpace) descend (snd ℝPremetricSpace) δ
    continuity (ν , hc) (μ , angle-close) =
      (λ ε → min₊ localLiftRadius (μ (min₊ (ν ε) ([ 1 / 8 ]₊)))) , preserves
      where
      preserves : IsUniformlyContinuousWith (snd CirclePremetricSpace) descend (snd ℝPremetricSpace)
        (λ ε → min₊ localLiftRadius (μ (min₊ (ν ε) ([ 1 / 8 ]₊))))
      IsUniformlyContinuousWith.pres≈ preserves p q ε close =
        PT.rec (R.isProp≈ (descend p) (descend q) ε) compare (innerRepresentative p)
        where
        η : ℚ₊
        η = min₊ (ν ε) ([ 1 / 8 ]₊)
        d : ℝ
        d = fst differenceAngleUC (p , q)
        near : p C.≈[ localLiftRadius ] q
        near = C.isMonotone≈≤ p q (min₊ localLiftRadius (μ η)) localLiftRadius
          (min₊≤L localLiftRadius (μ η)) close
        d-small : d ∼[ η ] 0
        d-small = angle-close p q η
          (C.isMonotone≈≤ p q (min₊ localLiftRadius (μ η)) (μ η)
            (min₊≤R localLiftRadius (μ η)) close)
        d-bounds : ((-ᵣ rat [ 1 / 8 ]) <ᵣ d) × (d <ᵣ rat [ 1 / 8 ])
        d-bounds = abs<→ointerval d (rat [ 1 / 8 ])
          (isTrans≡<ᵣ _ _ _ (cong absᵣ ℝ!)
            (equivFun (∼≃abs<ε d 0 ([ 1 / 8 ]₊))
              (∼-monotone≤ (min₊≤R (ν ε) ([ 1 / 8 ]₊)) d-small)))
        compare : (Σ[ r ∈ ℝ ] ((rat [ 1 / 8 ] <ᵣ r) × (r <ᵣ rat [ 5 / 4 ])) × (injCircle r ≡ p)) →
          descend p R.≈[ ε ] descend q
        compare (r , (rlo , rhi) , represents) = subst2 (λ u v → u R.≈[ ε ] v)
          (sym (descend-at r (inner-inside r rlo rhi) p represents))
          (sym (descend-at (r +ᵣ d) (perturb-inside r d rlo rhi (fst d-bounds) (snd d-bounds)) q
            (perturb-represents r p q represents near)))
          (IsUniformlyContinuousWith.pres≈ hc r (r +ᵣ d) ε
            (∼→≈ℝ r (r +ᵣ d) (ν ε)
              (subst (λ u → u ∼[ ν ε ] (r +ᵣ d)) (+IdR r)
                (+ᵣ-neL r 0 d (ν ε)
                  (sym∼ d 0 (ν ε) (∼-monotone≤ (min₊≤L (ν ε) ([ 1 / 8 ]₊)) d-small))))))

  descendUC : UC[ CirclePremetricSpace , ℝPremetricSpace ]
  descendUC = descend , PT.map2 continuity (snd h) differenceAngle-modulus
