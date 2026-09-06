module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Pasting where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using (Dichotomyℝ')
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Stitching
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

-- The first path runs on [0,1/3], the second on [2/3,1].
-- Both are constant at the common endpoint throughout the open overlap.
early late : UC[ Interval , Interval ]
early = clipUC ∘UC (scaleUC 3 ∘UC coordinateUC)
late = clipUC ∘UC (affineUC 3 (-ᵣ 2) ∘UC coordinateUC)

early-0 : fst early 𝟘 ≡ 𝟘
early-0 = cong clip ℝ! ∙ clip-fixes 𝟘
early-1 : fst early 𝟙 ≡ 𝟙
early-1 = clip-above _ (isTrans≤≡ᵣ 1 3 _ decℚ≤ᵣ? ℝ!)
late-0 : fst late 𝟘 ≡ 𝟘
late-0 = clip-below _ (isTrans≡≤ᵣ _ (rat (ℚ.- 2)) 0 ℝ! decℚ≤ᵣ?)
late-1 : fst late 𝟙 ≡ 𝟙
late-1 = cong clip ℝ! ∙ clip-fixes 𝟙

early-finished : (t : 𝕀) → rat [ 1 / 3 ] ≤ᵣ fst t → fst early t ≡ 𝟙
early-finished t lower = clip-above _ (isTrans≡≤ᵣ 1 (rat [ 1 / 3 ] ·ᵣ 3) _ ℝ!
  (≤ᵣ-·o (rat [ 1 / 3 ]) (fst t) 3 <≤ℚ! lower))

late-not-started : (t : 𝕀) → fst t ≤ᵣ rat [ 2 / 3 ] → fst late t ≡ 𝟘
late-not-started t upper = clip-below _ (isTrans≤≡ᵣ _ (rat [ 2 / 3 ] ·ᵣ 3 -ᵣ 2) 0
  (≤ᵣ-+o (fst t ·ᵣ 3) (rat [ 2 / 3 ] ·ᵣ 3) (-ᵣ 2)
    (≤ᵣ-·o (fst t) (rat [ 2 / 3 ]) 3 <≤ℚ! upper)) ℝ!)

module Paste {ℓ ℓ' ℓY ℓY'} (X : PremetricSpace ℓ ℓ') (Y : PremetricSpace ℓY ℓY')
  (f g : UC[ PremetricProduct Interval Y , X ])
  (join : ∀ y → fst f (𝟙 , y) ≡ fst g (𝟘 , y)) where

  private
    module P = PremetricStr (snd X)
    left right : UC[ PremetricProduct ℝPremetricSpace Y , X ]
    left = f ∘UC pairUC (clipUC ∘UC productFstUC) productSndUC
    right = g ∘UC pairUC (clipUC ∘UC (translateUC (-ᵣ 2) ∘UC productFstUC)) productSndUC

    agrees : ∀ t y → 1 <ᵣ t → t <ᵣ 2 → fst left (t , y) ≡ fst right (t , y)
    agrees t y lower upper = cong (λ u → fst f (u , y))
      (clip-above t (<ᵣWeaken≤ᵣ _ _ lower)) ∙ join y ∙
      sym (cong (λ u → fst g (u , y)) (clip-below (t -ᵣ 2)
        (isTrans≤≡ᵣ _ _ _ (≤ᵣ-+o t 2 (-ᵣ 2) (<ᵣWeaken≤ᵣ _ _ upper)) ℝ!)))

    module S = Stitch X Y 1 left right
      (λ t y lower upper → agrees t y lower (subst (t <ᵣ_) (cong rat ℚ!) upper))

  pastedUC : UC[ PremetricProduct Interval Y , X ]
  pastedUC = S.stitchedUC ∘UC pairUC
    (scaleUC 3 ∘UC (coordinateUC ∘UC productFstUC)) productSndUC

  pasted-left : ∀ t y → fst t ·ᵣ 3 <ᵣ 2 →
    fst pastedUC (t , y) ≡ fst f (fst early t , y)
  pasted-left t y upper = S.stitched-left (fst t ·ᵣ 3) y
    (subst (fst t ·ᵣ 3 <ᵣ_) (sym (cong rat ℚ!)) upper)

  pasted-right : ∀ t y → 1 <ᵣ fst t ·ᵣ 3 →
    fst pastedUC (t , y) ≡ fst g (fst late t , y)
  pasted-right t y = S.stitched-right (fst t ·ᵣ 3) y

  -- An equation can be proved on the two overlapping open pieces.
  pasted-eq : ∀ t y (v : fst X) →
    (fst t ·ᵣ 3 <ᵣ 2 → fst f (fst early t , y) ≡ v) →
    (1 <ᵣ fst t ·ᵣ 3 → fst g (fst late t , y) ≡ v) →
    fst pastedUC (t , y) ≡ v
  pasted-eq t y v onLeft onRight = PT.rec (P.isSetM _ _)
    (λ { (inl upper) → pasted-left t y upper ∙ onLeft upper
       ; (inr lower) → pasted-right t y lower ∙ onRight lower })
    (Dichotomyℝ' 1 (fst t ·ᵣ 3) 2 decℚ<ᵣ?)

  pasted-0 : ∀ y → fst pastedUC (𝟘 , y) ≡ fst f (𝟘 , y)
  pasted-0 y = pasted-left 𝟘 y (isTrans≡<ᵣ _ 0 2 ℝ! decℚ<ᵣ?)
    ∙ cong (λ t → fst f (t , y)) early-0

  pasted-1 : ∀ y → fst pastedUC (𝟙 , y) ≡ fst g (𝟙 , y)
  pasted-1 y = pasted-right 𝟙 y (isTrans<≡ᵣ 1 3 _ decℚ<ᵣ? ℝ!)
    ∙ cong (λ t → fst g (t , y)) late-1
