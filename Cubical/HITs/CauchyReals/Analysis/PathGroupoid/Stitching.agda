module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Stitching where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using (module Stiching; Dichotomyℝ')
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Unit
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

opaque
  close-upper : ∀ t u ε → t ≈ℝ[ ε ] u → u <ᵣ t +ᵣ rat (fst ε)
  close-upper t u ε close = isTrans≡<ᵣ _ _ _ ℝ!
    (isTrans<≡ᵣ _ _ _
      (<ᵣ-+o (u -ᵣ t) (rat (fst ε)) t
        (snd (abs<→ointerval (u -ᵣ t) (rat (fst ε))
          (equivFun (∼≃abs<ε u t ε) (sym∼ t u ε (≈ℝ→∼ t u ε close)))))) ℝ!)

  close-lower : ∀ t u ε → t ≈ℝ[ ε ] u → t -ᵣ rat (fst ε) <ᵣ u
  close-lower t u ε close = isTrans≡<ᵣ _ _ _ ℝ!
    (isTrans<≡ᵣ _ _ _
      (<ᵣ-+o (-ᵣ rat (fst ε)) (u -ᵣ t) t
        (fst (abs<→ointerval (u -ᵣ t) (rat (fst ε))
          (equivFun (∼≃abs<ε u t ε) (sym∼ t u ε (≈ℝ→∼ t u ε close)))))) ℝ!)

-- A fixed positive overlap gives one modulus for the pasted family.
-- Only set-valued truncation elimination is used; completeness is unnecessary.
module Stitch {ℓ ℓ' ℓY ℓY'} (X : PremetricSpace ℓ ℓ') (Y : PremetricSpace ℓY ℓY')
  (a : ℚ) (f g : UC[ PremetricProduct ℝPremetricSpace Y , X ])
  (agrees : ∀ t y → rat a <ᵣ t → t <ᵣ rat (a ℚ.+ 1) → fst f (t , y) ≡ fst g (t , y)) where

  private
    module P = PremetricStr (snd X)
    module S = PremetricStr (snd (PremetricProduct ℝPremetricSpace Y))
    module R = PremetricStr (snd ℝPremetricSpace)

    ab : rat a <ᵣ rat (a ℚ.+ 1)
    ab = <ℚ→<ᵣ a (a ℚ.+ 1) <≤ℚ!

    module At (y : fst Y) = Stiching.hLev2 (fst X) (rat a) (rat (a ℚ.+ 1)) ab
      (λ t _ → fst f (t , y)) (λ t _ → fst g (t , y))
      (λ t upper lower → agrees t y lower upper) P.isSetM

  opaque
    stitched : ℝ × fst Y → fst X
    stitched (t , y) = At.stichSetFns y t

    stitched-left : ∀ t y → t <ᵣ rat (a ℚ.+ 1) → stitched (t , y) ≡ fst f (t , y)
    stitched-left t y = At.stichSetFns-x< y t

    stitched-right : ∀ t y → rat a <ᵣ t → stitched (t , y) ≡ fst g (t , y)
    stitched-right t y = At.stichSetFns-<x y t

  private
    continuity :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd (PremetricProduct ℝPremetricSpace Y))
        (fst f) (snd X) μ) →
      (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd (PremetricProduct ℝPremetricSpace Y))
        (fst g) (snd X) ν) →
      Σ[ δ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd (PremetricProduct ℝPremetricSpace Y))
        stitched (snd X) δ
    continuity (μ , fc) (ν , gc) = (λ ε → min₊ ([ 1 / 4 ]₊) (min₊ (μ ε) (ν ε))) , preserves
      where
      δ : ℚ₊ → ℚ₊
      δ ε = min₊ ([ 1 / 4 ]₊) (min₊ (μ ε) (ν ε))
      preserves : IsUniformlyContinuousWith (snd (PremetricProduct ℝPremetricSpace Y)) stitched (snd X) δ
      IsUniformlyContinuousWith.pres≈ preserves (t , y) (u , z) ε close =
        PT.rec (P.isProp≈ _ _ ε) choose
          (Dichotomyℝ' (rat (a ℚ.+ [ 1 / 4 ])) t (rat (a ℚ.+ [ 3 / 4 ]))
            (<ℚ→<ᵣ (a ℚ.+ [ 1 / 4 ]) (a ℚ.+ [ 3 / 4 ]) <≤ℚ!))
        where
        time-close : t ≈ℝ[ [ 1 / 4 ]₊ ] u
        time-close = R.isMonotone≈≤ t u (δ ε) ([ 1 / 4 ]₊)
          (min₊≤L ([ 1 / 4 ]₊) (min₊ (μ ε) (ν ε))) (fst close)
        common-close : (t , y) S.≈[ min₊ (μ ε) (ν ε) ] (u , z)
        common-close = S.isMonotone≈≤ (t , y) (u , z) (δ ε) (min₊ (μ ε) (ν ε))
          (min₊≤R ([ 1 / 4 ]₊) (min₊ (μ ε) (ν ε))) close
        choose : (t <ᵣ rat (a ℚ.+ [ 3 / 4 ])) ⊎ (rat (a ℚ.+ [ 1 / 4 ]) <ᵣ t) →
          stitched (t , y) P.≈[ ε ] stitched (u , z)
        choose (inl upper) = subst2 (λ v w → v P.≈[ ε ] w)
          (sym (stitched-left t y (isTrans<ᵣ _ _ _ upper (<ℚ→<ᵣ (a ℚ.+ [ 3 / 4 ]) (a ℚ.+ 1) <≤ℚ!))))
          (sym (stitched-left u z (isTrans<ᵣ _ _ _ (close-upper t u ([ 1 / 4 ]₊) time-close)
            (isTrans<≡ᵣ _ _ _ (<ᵣ-+o t (rat (a ℚ.+ [ 3 / 4 ])) (rat [ 1 / 4 ]) upper)
              (+ᵣ-rat (a ℚ.+ [ 3 / 4 ]) [ 1 / 4 ] ∙ cong rat ℚ!)))))
          (IsUniformlyContinuousWith.pres≈ fc (t , y) (u , z) ε
            (S.isMonotone≈≤ (t , y) (u , z) (min₊ (μ ε) (ν ε)) (μ ε)
              (min₊≤L (μ ε) (ν ε)) common-close))
        choose (inr lower) = subst2 (λ v w → v P.≈[ ε ] w)
          (sym (stitched-right t y (isTrans<ᵣ _ _ _ (<ℚ→<ᵣ a (a ℚ.+ [ 1 / 4 ]) <≤ℚ!) lower)))
          (sym (stitched-right u z (isTrans<ᵣ _ _ _
            (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat₂ (a ℚ.+ [ 1 / 4 ]) [ 1 / 4 ] ∙ cong rat ℚ!))
              (<ᵣ-+o (rat (a ℚ.+ [ 1 / 4 ])) t (-ᵣ rat [ 1 / 4 ]) lower))
            (close-lower t u ([ 1 / 4 ]₊) time-close))))
          (IsUniformlyContinuousWith.pres≈ gc (t , y) (u , z) ε
            (S.isMonotone≈≤ (t , y) (u , z) (min₊ (μ ε) (ν ε)) (ν ε)
              (min₊≤R (μ ε) (ν ε)) common-close))

  stitchedUC : UC[ PremetricProduct ℝPremetricSpace Y , X ]
  stitchedUC = stitched , PT.map2 continuity (snd f) (snd g)

module StitchReal {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') (a : ℚ)
  (f g : UC[ ℝPremetricSpace , X ])
  (agrees : ∀ t → rat a <ᵣ t → t <ᵣ rat (a ℚ.+ 1) → fst f t ≡ fst g t) where
  private
    module S = Stitch X UnitPremetricSpace a (f ∘UC productFstUC) (g ∘UC productFstUC)
      (λ t _ → agrees t)
  stitchedUC : UC[ ℝPremetricSpace , X ]
  stitchedUC = S.stitchedUC ∘UC rightInsertionUC ℝPremetricSpace UnitPremetricSpace tt
  stitched-left : ∀ t → t <ᵣ rat (a ℚ.+ 1) → fst stitchedUC t ≡ fst f t
  stitched-left t = S.stitched-left t tt
  stitched-right : ∀ t → rat a <ᵣ t → fst stitchedUC t ≡ fst g t
  stitched-right t = S.stitched-right t tt
