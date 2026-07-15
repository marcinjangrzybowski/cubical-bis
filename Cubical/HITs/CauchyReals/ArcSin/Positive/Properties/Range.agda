module Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Range where

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
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
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
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; _+₊_ ; _·₊_ ; _/2₊ ; min₊)
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; rtp-1/n ; riemannSum-empty)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Properties
open import Cubical.HITs.CauchyReals.Calculus.Integration.Uniform
open IntegrationUC rtp-1/n
open import Cubical.HITs.CauchyReals.Calculus.Derivative.MeanValue
open import Cubical.HITs.CauchyReals.Calculus.Integration.FundamentalTheorem using
  ( Integral-additive
  ; FTOC⇒*
  ; FTOC⇐''
  )
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Analysis.Uniform
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base hiding (invℚ₊ ; _ℚ₊^ⁿ_)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Monotone public
secArcSin : ∀ x sinx∈ (x∈ : x ∈ pred≤< 0 π-number/2) → arcSin (sin x) sinx∈ ≡ x
secArcSin x sinx∈ x∈@(0≤x , _) =
 let (x' , x<x' , x'<π/2) = (denseℝ x π-number/2 (snd x∈))
     0<x' = (isTrans≤<ᵣ _ _ _ (fst x∈) x<x')
     z = FTOC⇐'' 0 x' 0<x'
           _ _ (IsUContinuousℙ-const (intervalℙ 0 x') _) ([arcSin∘Sin]'=1 x'
             (isTrans≤<ᵣ _ _ _ (fst x∈) x<x' , x'<π/2))
          x ((fst x∈) , (<ᵣWeaken≤ᵣ _ _ x<x'))
 in (cong (arcSin (sin x)) (∈-isProp (pred≤< 0 1) _ _ _)
       ∙ sym (𝐑'.+IdR' _ _
         (cong -ᵣ_ (cong (uncurry arcSin)
           (Σ≡Prop (∈-isProp (pred≤< 0 1)) {v = _ , ≤ᵣ-refl 0 , decℚ<ᵣ? {0} {1}}
            sin0=0) ∙ arcSin[0]≡0 _)  ∙ -ᵣ-rat 0))) ∙∙ IntegralUniq 0 x 0≤x (λ r _ _ → 1) _ _
     z (IntegralConstℙ 0 x 0≤x 1)
    ∙∙ (Rℝ.·IdL _ ∙ 𝐑'.+IdR' _ _ (-ᵣ-rat 0))

arcSin∈[0,1⟩ : ∀ x x∈ → arcSin x x∈ ∈ pred≤< 0 π-number/2
arcSin∈[0,1⟩ x x∈ =

  PT.rec (∈-isProp (pred≤< 0 π-number/2) _)
   (λ (q , x<q , q<1) →
     let z = ≤ᵣ-ᵣ _ _ (≤-o+-cancel _ _ _ (subst2 _≤ᵣ_
             (cong absᵣ (cong₂ _-ᵣ_ sin[π/2]≡1 refl)
               ∙ absᵣNonNeg _ (x≤y→0≤y-x _ _ (sin≤1 _)))
            (cong absᵣ ℝ!
               ∙ absᵣPos _ (x<y→0<y-x _ _  q<1))
             (sinDiffBound π-number/2
            (π-number/2 -ᵣ (1 -ᵣ rat q)))))
         zz = (isTrans<≡ᵣ _ _ _
                   (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ ((x<y→0<y-x _ _  q<1))))
                   (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))
         zzz = (x≤y→0≤y-x _ _
                 (isTrans≤ᵣ _ _ _

                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-o+ _ _ _
                       (-ᵣ≤ᵣ _ _ (isTrans≤ᵣ _ _ _
                        (fst x∈) (<ᵣWeaken≤ᵣ _ _ x<q))))
                      (𝐑'.+IdR' _ _ (-ᵣ-rat 0)))
                    (<ᵣWeaken≤ᵣ _ _ 1<π-number/2)))
     in isTrans≡≤ᵣ _ _ _
          (sym (arcSin[0]≡0 _))
          (arcSin-Monotone 0 x (≤ᵣ-refl 0 , decℚ<ᵣ? {0} {1})
            x∈ (fst x∈)) ,
         isTrans<ᵣ _ _ _
           (arcSin-MonotoneStrict x (sin (π-number/2 -ᵣ (1 -ᵣ rat q)))
             x∈ (isTrans≡≤ᵣ _ _ _
                  (sym sin0=0)
                  (sin-firstQuarter-Monotone 0
                    _ (≤ᵣ-refl _ , (<ᵣWeaken≤ᵣ _ _ 0<π-number/2))
                    (zzz , <ᵣWeaken≤ᵣ _ _ zz)
                 zzz) ,
              isTrans<≡ᵣ _ _ _
               (sin-firstQuarter-strictMonotone _ _
                (zzz
                  , (<ᵣWeaken≤ᵣ _ _ zz))
                (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) zz)
                sin[π/2]≡1)
            (isTrans<≤ᵣ _ _ _ x<q
               z)) (isTrans≡<ᵣ _ _ _
                 (secArcSin _ _
                  (zzz , zz)) zz))
   (denseℚinℝ _ _ (snd x∈))
