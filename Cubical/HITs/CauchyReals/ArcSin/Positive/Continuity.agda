module Cubical.HITs.CauchyReals.ArcSin.Positive.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (min≤ ; min≤')
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using (_⁻¹₊ ; y·[x/y])

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (_·₊_ ; min₊)
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0<)

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition using
  ( arcSin )
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Continuity.Estimate public
  using (IntegralNonNeg ; arcSinDiff-Help)

IsContinuousWithPredArcSin : IsContinuousWithPred (pred≤< 0 1) arcSin
IsContinuousWithPredArcSin u ε u∈@(0≤u , u<1) = do
  let (b , u<b , b<1) = denseℝ _ _ u<1
  (η , 0<η , η<b-u) ← denseℚinℝ _ _ (x<y→0<y-x _ _ u<b)
  let L , ≤L = arcSinDiff-Help b
            (isTrans≤ᵣ _ _ _ 0≤u (<ᵣWeaken≤ᵣ _ _ u<b)) b<1
  (υ , L<υ) ← ∃ℚ₊LargerThanℝ₊ L
  let η₊ = η , ℚ<→0< η (<ᵣ→<ℚ 0 η 0<η)
      δ = min₊ η₊ ((υ ℚ.⁻¹₊) ·₊ ε)
  ∣ δ , (λ v v∈ u∼v →
      invEq (∼≃abs<ε _ _ _)
       let z = fst (∼≃abs<ε _ _ _) u∼v
           zz = isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ _ _) (isTrans<≤ᵣ _ _ _ z
                 (≤ℚ→≤ᵣ _ _ (ℚ.min≤ η _))))
       in isTrans≤<ᵣ _ _ _  (≤L u v u∈ v∈ (<ᵣWeaken≤ᵣ _ _ u<b)
                       (<ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ _ _ _
                         (a-b<c⇒a<c+b _ _ _ zz)
                         (a<b-c⇒a+c<b _ _ _ η<b-u))))
           (isTrans<≡ᵣ _ _ _
             (<ᵣ₊Monotone·ᵣ _ _ _ _
               (0≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (snd L))
               (isTrans<≤ᵣ _ _ _
                 z
                 (≤ℚ→≤ᵣ _ _ (ℚ.min≤' η _))) L<υ)

                  ((·ᵣComm _ _ ∙ sym (rat·ᵣrat _ _) ∙
                 cong rat (ℚ.y·[x/y] υ _))))) ∣₁
