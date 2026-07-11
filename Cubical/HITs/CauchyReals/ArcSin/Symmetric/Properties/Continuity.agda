module Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Inverse

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Continuity using
  ( IsContinuousWithPredArcSin )
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Extras using
  ( IsContinuousWithPred-ᵣ )
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition using
  ( arcSin )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base public

opaque
  unfolding arcSin⟨⟩ _+ᵣ_

  IsContinuousWPArcSin⟨⟩ : IsContinuousWithPred (ointervalℙ -1 1) arcSin⟨⟩
  IsContinuousWPArcSin⟨⟩ =
    contDiagNE₂WP sumR (ointervalℙ -1 1)
             (λ x x∈ → -ᵣ (arcSin (clampᵣ 0 1 (-ᵣ x))
             ((≤clampᵣ 0 1 (-ᵣ x) decℚ≤ᵣ?) ,
              isTrans≤<ᵣ _ (maxᵣ 0 (-ᵣ x)) _
                  (min≤ᵣ (maxᵣ 0 (-ᵣ x)) 1 )
                  (max<-lem 0 (-ᵣ x) 1 (decℚ<ᵣ? {0} {1})
                    ((isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (fst x∈))
                     (-ᵣ-rat -1)))))))
           (λ x x∈ →
             arcSin (clampᵣ 0 1 x)
              ((≤clampᵣ 0 1 x decℚ≤ᵣ?)
               , isTrans≤<ᵣ _ (maxᵣ 0 x) _
                  (min≤ᵣ (maxᵣ 0 x) 1 )
                  (max<-lem 0 x 1 (decℚ<ᵣ? {0} {1}) (snd x∈))))
            (IsContinuousWithPred-ᵣ (ointervalℙ -1 1)
              _
              (IsContinuousWP∘ (pred≤< 0 1) (ointervalℙ -1 1)
             _
             _ _
             IsContinuousWithPredArcSin
             (IsContinuousWP∘ (ointervalℙ -1 1) (ointervalℙ -1 1)
              _
              _
              (λ x (<x , x<) → (isTrans≡<ᵣ _ _ _ (sym (-ᵣ-rat 1))
                (-ᵣ<ᵣ _ _ x<)) ,
               (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ <x) (-ᵣ-rat -1)))
              (AsContinuousWithPred (ointervalℙ -1 1)
                _ (IsContinuousClamp 0 1))
              ((AsContinuousWithPred (ointervalℙ -1 1)
                _ IsContinuous-ᵣ)))))
            (IsContinuousWP∘ (pred≤< 0 1) (ointervalℙ -1 1)
             arcSin
             _ _
             IsContinuousWithPredArcSin
             (((AsContinuousWithPred (ointervalℙ -1 1)
              (clampᵣ 0 1 ) (IsContinuousClamp 0 1)))))
