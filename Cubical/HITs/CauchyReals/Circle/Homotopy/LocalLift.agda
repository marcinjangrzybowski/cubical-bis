module Cubical.HITs.CauchyReals.Circle.Homotopy.LocalLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict using (≤absᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.Uniform using
  (clampᵣ∼; IsUContinuous-ᵣ₂)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base using
  (IsUContinuous·ᵣR; IsUContinuous∘)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition using (arcSin)
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Continuity.Estimate using (arcSinDiff-Help)
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base using (arcSin⟨⟩)
open import Cubical.HITs.CauchyReals.Trigonometry.Pi using (π-number/2₊)
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Chart
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

private
  half : ℝ
  half = rat [ 1 / 2 ]
  clipped : ℝ → ℝ
  clipped = clampᵣ 0 half
  clipped-in : ∀ x → clipped x ∈ pred≤< 0 1
  clipped-in x = ≤clampᵣ 0 half x decℚ≤ᵣ? ,
    isTrans≤<ᵣ _ half 1 (clamp≤ᵣ 0 half x) decℚ<ᵣ?

opaque
  clippedArcSin : ℝ → ℝ
  clippedArcSin x = arcSin (clipped x) (clipped-in x)

  clippedArcSin-uc : ∥ IsUContinuous clippedArcSin ∥₁
  clippedArcSin-uc = PT.map continuous (IsUContinuous·ᵣR (fst L))
    where
    L : ℝ₊
    L = fst (arcSinDiff-Help half decℚ≤ᵣ? decℚ<ᵣ?)
    estimate : ∀ x y → absᵣ (clippedArcSin x -ᵣ clippedArcSin y) ≤ᵣ
      absᵣ (clipped x -ᵣ clipped y) ·ᵣ fst L
    estimate x y = snd (arcSinDiff-Help half decℚ≤ᵣ? decℚ<ᵣ?)
      (clipped x) (clipped y) (clipped-in x) (clipped-in y)
      (clamp≤ᵣ 0 half x) (clamp≤ᵣ 0 half y)
    continuous : IsUContinuous (_·ᵣ fst L) → IsUContinuous clippedArcSin
    continuous lc ε = fst (lc ε) , λ x y xy → invEq (∼≃abs<ε _ _ ε)
      (isTrans≤<ᵣ _ _ _ (estimate x y)
        (isTrans≡<ᵣ _ _ _
          (cong (absᵣ (clipped x -ᵣ clipped y) ·ᵣ_) (sym (absᵣPos (fst L) (snd L)))
            ∙ sym (·absᵣ _ _) ∙ cong absᵣ (Rℝ.·DistL- _ _ _))
          (equivFun (∼≃abs<ε _ _ ε)
            (snd (lc ε) (clipped x) (clipped y) (clampᵣ∼ xy)))))

private
  same-clamp : ∀ x → x ≤ᵣ half → clampᵣ 0 1 x ≡ clipped x
  same-clamp x bound = ≤→minᵣ (maxᵣ 0 x) 1
    (isTrans≤ᵣ _ half 1 (max≤-lem 0 x half decℚ≤ᵣ? bound) decℚ≤ᵣ?)
    ∙ sym (≤→minᵣ (maxᵣ 0 x) half (max≤-lem 0 x half decℚ≤ᵣ? bound))

opaque
  unfolding clippedArcSin arcSin⟨⟩
  symmetric-clippedArcSin : ∀ x x∈ → absᵣ x ≤ᵣ half →
    clippedArcSin x -ᵣ clippedArcSin (-ᵣ x) ≡ arcSin⟨⟩ x x∈
  symmetric-clippedArcSin x x∈ bound = +ᵣComm _ _
    ∙ cong₂ _+ᵣ_
      (cong -ᵣ_ (cong (uncurry arcSin) (Σ≡Prop (λ _ → isProp× (isProp≤ᵣ _ _) (isProp<ᵣ _ _))
        (sym (same-clamp (-ᵣ x) (isTrans≤ᵣ _ _ _
          (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ x)) (sym (-absᵣ x))) bound))))))
      (cong (uncurry arcSin) (Σ≡Prop (λ _ → isProp× (isProp≤ᵣ _ _) (isProp<ᵣ _ _))
        (sym (same-clamp x (isTrans≤ᵣ _ _ _ (≤absᵣ x) bound)))))

-- A globally uniformly continuous extension of the inverse sine chart
-- on the strip |y| ≤ 1/2. This supplies a uniform local lift without
-- invoking compactness or choosing representatives of circle points.
localArcSin : ℝ → ℝ
localArcSin x = clippedArcSin x -ᵣ clippedArcSin (-ᵣ x)

localArcSin-uc : ∥ IsUContinuous localArcSin ∥₁
localArcSin-uc = PT.map (λ c → IsUContinuous-ᵣ₂ clippedArcSin (clippedArcSin ∘ -ᵣ_) c
  (IsUContinuous∘ c (λ ε → ε , λ x y → -ᵣ-nonExpanding x y ε))) clippedArcSin-uc

localArcSin-agrees : ∀ x x∈ → absᵣ x ≤ᵣ half → localArcSin x ≡ arcSin⟨⟩ x x∈
localArcSin-agrees = symmetric-clippedArcSin

private
  inverse-turn : ℝ
  inverse-turn = fst (invℝ₊ (π-number/2₊ ₊·ᵣ 4))

localAngle : ℝ → ℝ
localAngle y = localArcSin y ·ᵣ inverse-turn

localAngle-uc : ∥ IsUContinuous localAngle ∥₁
localAngle-uc = PT.map2 IsUContinuous∘ (IsUContinuous·ᵣR inverse-turn) localArcSin-uc

opaque
  localAngle-chart : (p : distCircle) (positive : 0 <ᵣ fst (fst p)) →
    absᵣ (snd (fst p)) ≤ᵣ rat [ 1 / 2 ] →
    localAngle (snd (fst p)) ≡ fst (Iso.inv openHalfCircleIso (p , positive))
  localAngle-chart p@((x , y) , norm) positive bound =
    cong (_·ᵣ inverse-turn) (localArcSin-agrees y y∈ bound) ∙ same-angle
    where
    y∈ : y ∈ ointervalℙ -1 1
    y∈ = subst (λ a → y ∈ ointervalℙ a 1) (-ᵣ-rat 1)
      (abs<→ointerval y 1 (isTrans≤<ᵣ _ half 1 bound decℚ<ᵣ?))
    same-angle : arcSin⟨⟩ y y∈ ·ᵣ inverse-turn ≡ fst (Iso.inv openHalfCircleIso (p , positive))
    same-angle = cong (λ proof → arcSin⟨⟩ y proof ·ᵣ inverse-turn)
      (∈-isProp (ointervalℙ -1 1) y _ _)

  localAngle-cover : (p : distCircle) → 0 <ᵣ fst (fst p) →
    absᵣ (snd (fst p)) ≤ᵣ rat [ 1 / 2 ] → cover (localAngle (snd (fst p))) ≡ p
  localAngle-cover p positive bound = cong cover (localAngle-chart p positive bound)
    ∙ cover-β (fst (Iso.inv openHalfCircleIso (p , positive)))
    ∙ cong fst (Iso.sec openHalfCircleIso (p , positive))

  localAngle-bound : (p : distCircle) → 0 <ᵣ fst (fst p) →
    absᵣ (snd (fst p)) ≤ᵣ rat [ 1 / 2 ] →
    absᵣ (localAngle (snd (fst p))) <ᵣ rat [ 1 / 4 ]
  localAngle-bound p positive bound = isTrans≡<ᵣ _ _ _
    (cong absᵣ (localAngle-chart p positive bound))
    (ointerval→abs< _ _ (snd (Iso.inv openHalfCircleIso (p , positive))))

localAngleUC : UC[ ℝPremetricSpace , ℝPremetricSpace ]
localAngleUC = localAngle , PT.rec squash₁
  (λ c → snd (IsUContinuous→ℝUC localAngle c)) localAngle-uc

circleYCoordinateUC : UC[ distCirclePremetricSpace , ℝPremetricSpace ]
circleYCoordinateUC = productSndUC ∘UC distCircleInclusionUC

-- The centre is an arbitrary circle point. The lift is defined on the
-- whole domain; it lifts f wherever its rotation lies in the small strip.
module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'}
  (p : distCircle) (f : UC[ M , distCirclePremetricSpace ]) where

  rotatedMap : UC[ M , distCirclePremetricSpace ]
  rotatedMap = addDistCircleUC f (constantUC (ℝS¹.- p))

  opaque
    localLiftUC : UC[ M , ℝPremetricSpace ]
    localLiftUC = localAngleUC ∘UC (circleYCoordinateUC ∘UC rotatedMap)

    localLift-β : ∀ x → fst localLiftUC x ≡ localAngle (snd (fst (fst rotatedMap x)))
    localLift-β x = refl

  localLift-cong : ∀ x y → fst f x ≡ fst f y → fst localLiftUC x ≡ fst localLiftUC y
  localLift-cong x y same = localLift-β x
    ∙ cong (localAngle ∘ snd ∘ fst ∘ (ℝS¹._+ (ℝS¹.- p))) same
    ∙ sym (localLift-β y)

  opaque
    localLift-cover : ∀ x → 0 <ᵣ fst (fst (fst rotatedMap x)) →
      absᵣ (snd (fst (fst rotatedMap x))) ≤ᵣ rat [ 1 / 2 ] →
      p ℝS¹.+ cover (fst localLiftUC x) ≡ fst f x
    localLift-cover x positive bound =
      cong (p ℝS¹.+_) (cong cover (localLift-β x)
        ∙ localAngle-cover (fst rotatedMap x) positive bound)
      ∙ ℝS¹.+Comm p (fst f x ℝS¹.+ ℝS¹.- p)
      ∙ sym (ℝS¹.+Assoc (fst f x) (ℝS¹.- p) p)
      ∙ cong (fst f x ℝS¹.+_) (ℝS¹.+InvL p)
      ∙ ℝS¹.+IdR (fst f x)

private
  module D = PremetricStr (snd distCirclePremetricSpace)

  half-close-strip : (p : distCircle) → p D.≈[ [ 1 / 2 ]₊ ] circle0 →
    (0 <ᵣ fst (fst p)) × (absᵣ (snd (fst p)) ≤ᵣ rat [ 1 / 2 ])
  half-close-strip ((x , y) , norm) close = positive , <ᵣWeaken≤ᵣ _ _ small-y
    where
    x-close : absᵣ (x -ᵣ 1) <ᵣ rat [ 1 / 2 ]
    x-close = equivFun (∼≃abs<ε x 1 ([ 1 / 2 ]₊))
      (≈ℝ→∼ x 1 ([ 1 / 2 ]₊) (fst close))
    positive : 0 <ᵣ x
    positive = isTrans<ᵣ 0 (rat [ 1 / 2 ]) x decℚ<ᵣ?
      (subst2 _<ᵣ_ ℝ! ℝ!
        (<ᵣ-+o _ _ 1 (fst (abs<→ointerval (x -ᵣ 1) (rat [ 1 / 2 ]) x-close))))
    small-y : absᵣ y <ᵣ rat [ 1 / 2 ]
    small-y = isTrans≡<ᵣ _ _ _ (cong absᵣ ℝ!)
      (equivFun (∼≃abs<ε y 0 ([ 1 / 2 ]₊))
        (≈ℝ→∼ y 0 ([ 1 / 2 ]₊) (snd close)))

  opaque
    close-difference : (p q r : distCircle) → r ≡ p ℝS¹.+ (ℝS¹.- q) →
      p D.≈[ circleAddModulus ([ 1 / 2 ]₊) ] q → r D.≈[ [ 1 / 2 ]₊ ] circle0
    close-difference p q r image close = subst2 (λ a b → a D.≈[ [ 1 / 2 ]₊ ] b)
      (sym image) (ℝS¹.+InvR q)
      (circle-add-close p (ℝS¹.- q) q (ℝS¹.- q) ([ 1 / 2 ]₊) close
        (D.isRefl≈ (ℝS¹.- q) (circleAddModulus ([ 1 / 2 ]₊))))

localLiftRadius : ℚ₊
localLiftRadius = circleAddModulus ([ 1 / 2 ]₊)

module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'}
  (p : distCircle) (f : UC[ M , distCirclePremetricSpace ]) where

  opaque
    localLift-strip : ∀ x → fst f x D.≈[ localLiftRadius ] p →
      (0 <ᵣ fst (fst (fst (rotatedMap p f) x))) ×
      (absᵣ (snd (fst (fst (rotatedMap p f) x))) ≤ᵣ rat [ 1 / 2 ])
    localLift-strip x close = half-close-strip (fst (rotatedMap p f) x)
      (close-difference (fst f x) p (fst (rotatedMap p f) x) refl close)

    localLift-near : ∀ x → fst f x D.≈[ localLiftRadius ] p →
      p ℝS¹.+ cover (fst (localLiftUC p f) x) ≡ fst f x
    localLift-near x close = localLift-cover p f x
      (fst (localLift-strip x close)) (snd (localLift-strip x close))

    localLift-near-bound : ∀ x → fst f x D.≈[ localLiftRadius ] p →
      absᵣ (fst (localLiftUC p f) x) <ᵣ rat [ 1 / 4 ]
    localLift-near-bound x close = isTrans≡<ᵣ _ _ _ (cong absᵣ (localLift-β p f x))
      (localAngle-bound (fst (rotatedMap p f) x)
        (fst (localLift-strip x close)) (snd (localLift-strip x close)))

    localLift-centre : ∀ x → fst f x ≡ p → fst (localLiftUC p f) x ≡ 0
    localLift-centre x centre = cover-injective-near _ 0
      (isTrans≡<ᵣ _ _ _ (cong absᵣ
        (cong (fst (localLiftUC p f) x +ᵣ_) (-ᵣ-rat 0) ∙ +IdR (fst (localLiftUC p f) x)))
        (isTrans<ᵣ _ (rat [ 1 / 4 ]) 1 (localLift-near-bound x close) decℚ<ᵣ?))
      (ℝS¹.·CancelL p
        (localLift-near x close ∙ centre ∙ sym (ℝS¹.+IdR p)
          ∙ cong (p ℝS¹.+_) (sym cover-zero)))
      where
      close : fst f x D.≈[ localLiftRadius ] p
      close = subst (λ z → z D.≈[ localLiftRadius ] p) (sym centre) (D.isRefl≈ p localLiftRadius)
