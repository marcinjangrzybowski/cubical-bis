module Cubical.HITs.CauchyReals.ArcSin.Positive.Continuity.Estimate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using
  (absᵣ-min-max)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (rtp-1/n)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Properties
open import Cubical.HITs.CauchyReals.Calculus.Integration.Uniform
open IntegrationUC rtp-1/n
open import Cubical.HITs.CauchyReals.Calculus.Integration.FundamentalTheorem using
  ( Integral-additive* )
open import Cubical.HITs.CauchyReals.Trigonometry.Pi

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition using
  ( arcSin )

private
  opaque
    sameLeftMinus : ∀ a b c → (a +ᵣ b) -ᵣ (a +ᵣ c) ≡ b -ᵣ c
    sameLeftMinus a b c = ℝ!

opaque
  IntegralNonNeg : ∀ a b → a ≤ᵣ b → ∀ f s →  on[ a , b ]IntegralOf f is s →
                 (∀ x ≤x x≤ → 0 ≤ᵣ f x ≤x x≤ ) → 0 ≤ᵣ s
  IntegralNonNeg a b a≤b f _ s∫ 0≤f =
   isTrans≡≤ᵣ _ _ _ (sym (𝐑'.0LeftAnnihilates _))
    (Integral-≤ a b a≤b (λ _ _ _ → 0) _ _ _
    0≤f (IntegralConstℙ a b a≤b  0) s∫)


ArcSinLipschitzEstimate : ℝ → Type
ArcSinLipschitzEstimate U =
  0 ≤ᵣ U → U <ᵣ 1 → Σ[ L ∈ ℝ₊ ]
    (∀ u u' u∈ u'∈ →  u ≤ᵣ U → u' ≤ᵣ U
                  →  absᵣ (arcSin u u∈ -ᵣ arcSin u' u'∈) ≤ᵣ
                     absᵣ (u -ᵣ u') ·ᵣ fst L )

private
  arcSinDiff-Help-impl : ∀ U → ArcSinLipschitzEstimate U
  arcSinDiff-Help-impl U 0≤U U<1 =
     2 ₊·ᵣ L , w

   where

    U∈ = (0≤U , U<1)

    L : ℝ₊
    L = arcSin'₊ U U∈


    w : _
    w u u' u∈@(0≤u , u<1) u'∈@(0≤u' , u'<1) u≤U u'≤U =
     isTrans≤ᵣ _ _ _
     (isTrans≡≤ᵣ _ _ _
      (cong absᵣ (cong₂ _-ᵣ_ h h' ∙ sameLeftMinus _ _ _))
        (isTrans≤≡ᵣ _ _ _
          (absᵣ-triangle _ _)
          (cong₂ _+ᵣ_ (absᵣNonNeg _
             (IntegralNonNeg _ _ (min≤ᵣ u u') _ _ (snd u∫ )
              λ x ≤x x< →
                <ᵣWeaken≤ᵣ _ _ (snd (arcSin'₊ _ (_ , isTrans≤<ᵣ _ _ _ x< _)))))
           (sym (-absᵣ _)  ∙ absᵣNonNeg _
             ((IntegralNonNeg _ _ (min≤ᵣ' u u') _ _ (snd u'∫)
               λ x ≤x x< →
                <ᵣWeaken≤ᵣ _ _ (snd (arcSin'₊ _ (_ , isTrans≤<ᵣ _ _ _ x< _)))))))))
      (isTrans≤ᵣ _ _ _
        (≤ᵣMonotone+ᵣ _ _ _ _
          (Integral-≤ _ _ (min≤ᵣ u u') _ _ _ _
            (λ x ≤x x≤ →
              arcSin'-Monotone _ _ _ U∈
                (isTrans≤ᵣ _ _ _ x≤ (u≤U)) )
            (snd u∫) (IntegralConstℙ _ _ (min≤ᵣ u u') (fst L)))
          (Integral-≤ _ _ (min≤ᵣ' u u') _ _ _ _
            (λ x ≤x x≤ →
              arcSin'-Monotone _ _ _ U∈
                 (isTrans≤ᵣ _ _ _ x≤ u'≤U))
            (snd u'∫) (IntegralConstℙ _ _ (min≤ᵣ' u u') (fst L))))
        (isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _
          (sym (·DistL+ _ _ _) ∙ ·ᵣComm _ _ )

          (≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd L))
           (isTrans≤≡ᵣ _ _ _
             (≤ᵣMonotone+ᵣ _ _ _ _
               (≤ᵣ-+o _ _ _ (≤maxᵣ u u'))
               (≤ᵣ-+o _ _ _ (isTrans≤≡ᵣ _ _ _ (≤maxᵣ u' u) (maxᵣComm u' u))))
             (x+x≡2x _ ∙ (·ᵣComm _ _ ))))
           ) (sym (·ᵣAssoc _ 2 (fst L)) ∙ cong₂ _·ᵣ_ (sym (absᵣNonNeg _
           (fst (x≤y≃0≤y-x _ _)
           (isTrans≤ᵣ _ _ _ (min≤ᵣ u u' ) (≤maxᵣ u u'))))
           ∙ absᵣ-min-max u u') refl) ) )
      where


         u⊓u' : ℝ₀₊
         u⊓u' = minᵣ₀₊ (_ ,  0≤u) (_ , 0≤u')

         u⊓u'∈ : fst u⊓u' ∈ pred≤< 0 1
         u⊓u'∈ = snd u⊓u' , isTrans≤<ᵣ _ _ _ (min≤ᵣ _ _) u<1

         u∫ = (PT.rec
                    (IntegratedℙPropℙ _ _ (min≤ᵣ u u') _)
                     ((Integrate-UContinuousℙ
                     (fst u⊓u')
                     u
                     (min≤ᵣ u u')
                     (λ x' x'∈ → arcSin' _ _))
                     ∘ IsUContinuousℙ-restr (intervalℙ 0 u)
                        (intervalℙ _ _) _
                        λ x → map-fst (isTrans≤ᵣ _ _ _ (snd u⊓u') ))
                     ((arcSin'-UC u u∈)))

         u'∫ = (PT.rec
                    (IntegratedℙPropℙ _ _ (min≤ᵣ' u u') _)
                     ((Integrate-UContinuousℙ
                     (fst u⊓u')
                     u'
                     (min≤ᵣ' u u')
                     (λ x' x'∈ → arcSin' _ _))
                     ∘ IsUContinuousℙ-restr (intervalℙ 0 u')
                        (intervalℙ _ _) _
                        λ x → map-fst (isTrans≤ᵣ _ _ _ (snd u⊓u') ))
                     ((arcSin'-UC u' u'∈)))

         h : _
         h = sym (Integral-additive* (pred≤< 0 1)
                 0 (fst u⊓u') u (snd u⊓u') (min≤ᵣ u u') arcSin'
                 (snd (arcSinDef _ u⊓u'∈))
                  (snd u∫)
                  (snd (arcSinDef _ _)))


         h' : _
         h' = sym (Integral-additive* (pred≤< 0 1)
                 0 (fst u⊓u') u' (snd u⊓u') (min≤ᵣ' u u') arcSin'
                 (snd (arcSinDef _ u⊓u'∈))
                  (snd u'∫)
                  (snd (arcSinDef _ _)))

opaque
  arcSinDiff-Help : ∀ U → ArcSinLipschitzEstimate U
  arcSinDiff-Help = arcSinDiff-Help-impl
