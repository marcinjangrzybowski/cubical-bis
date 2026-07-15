module Cubical.HITs.CauchyReals.ArcSin.Positive.Core where

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
open import Cubical.Data.Rationals.Order as ℚ using ()
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using ()


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

arcSin'₊ : ∀ x → x ∈ pred≤< 0 1 → ℝ₊
arcSin'₊ x (0≤x , x<1) =
  invℝ₊ (root 2 (1 -ᵣ (x ^ⁿ 2) , x<y→0<y-x _ _
   (^<1 x 0≤x 1 x<1)))

arcSin' : ∀ x → x ∈ pred≤< 0 1 → ℝ
arcSin' x x∈ = fst (arcSin'₊ x x∈)

1≡arcSin'0 : 1 ≡ arcSin' 0 (≤ᵣ-refl _ , decℚ<ᵣ? {0} {1})
1≡arcSin'0 = cong fst (sym invℝ₊1) ∙
  cong (fst ∘ invℝ₊) (ℝ₊≡ (sym (cong fst (ₙ√1 2)) ∙
    cong (fst ∘ (root 2))
    (ℝ₊≡ (sym (𝐑'.+IdR' _ _
      (cong -ᵣ_ (0^ⁿ 1) ∙ -ᵣ-rat 0)))) ))

arcSin'-Monotone : ∀ x y x∈ y∈ → x ≤ᵣ y → arcSin' x x∈ ≤ᵣ arcSin' y y∈
arcSin'-Monotone x y x∈ y∈ x≤y =
  invEq (invℝ₊-≤-invℝ₊ _ _)
    (ₙ√-Monotone 2 ((≤ᵣ-o+ _ _ 1
                    (-ᵣ≤ᵣ _ _ (^ⁿ-Monotone 2 (fst x∈)  x≤y)))))

pre-invℝ₊UC : ∀ (x : ℚ₊) →
  IsUContinuousℙ (pred≥ (rat (fst x)))
         (λ x' x≤x' → fst (invℝ₊ (x' ,
           isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ x)) x≤x')))
pre-invℝ₊UC q ε =
  ((q ℚ₊^ⁿ 2) ·₊ ε) ,
   λ u v u∈ v∈ → invEq (∼≃abs<ε _ _ _) ∘S
     (λ ∣u-v∣<ε² →
      let u₊ : ℝ₊
          u₊ = (u , isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ q)) u∈)
          v₊ : ℝ₊
          v₊ = (v , isTrans<≤ᵣ _ _ _ (snd (ℚ₊→ℝ₊ q)) v∈)
      in isTrans≡<ᵣ _ (absᵣ (u -ᵣ v) ·ᵣ
        fst (invℝ₊ (u₊ ₊·ᵣ v₊))) _
          (minusComm-absᵣ _ _ ∙ cong absᵣ (invℝ₊-diff u₊ v₊)
             ∙ ·absᵣ _ _ ∙
            cong₂ _·ᵣ_
              refl (absᵣPos _ (snd (invℝ₊ (u₊ ₊·ᵣ v₊)))))

           (invEq (z/y<x₊≃z<y₊·x _ _ _)
             (isTrans<≤ᵣ _ _ _ ∣u-v∣<ε²
              (isTrans≡≤ᵣ _ _ _
               (rat·ᵣrat (fst (q ℚ₊^ⁿ 2)) _)
               (≤ᵣ-·ᵣo _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ ε)))
                (isTrans≡≤ᵣ _ _ _
                 (cong fst (sym (^ℤ-rat q (pos 2))))
                 (isTrans≡≤ᵣ _ _ _
                   (cong (rat (fst q) ·ᵣ_) (Rℝ.·IdR _))
                   (≤ᵣ₊Monotone·ᵣ (rat (fst q)) u (rat (fst q)) v
                     (<ᵣWeaken≤ᵣ _ _ (snd u₊))
                     (<ᵣWeaken≤ᵣ _ _ (ℚ₊→ℝ₊ q .snd))
                     u∈ v∈)))))))) ∘S
     fst (∼≃abs<ε _ _ _)





invℝ₊UC : ∀ x → (0<x : 0 <ᵣ x) → ∥ IsUContinuousℙ (pred≥ x)
         (λ x' x≤x' → fst (invℝ₊ (x' , isTrans<≤ᵣ _ _ _ 0<x x≤x'))) ∥₁
invℝ₊UC x 0<x =
  PT.map (λ (δ , 0<q , q<x) →
    subst (IsUContinuousℙ (pred≥ x))
      (funExt₂ λ _ _ →
        cong (fst ∘ invℝ₊)
          (Σ≡Prop (∈-isProp (pred> _)) refl))
      (IsUContinuousℙ-restr (pred≥ (rat δ)) (pred≥ x) _
       (λ x x∈ → isTrans≤ᵣ _ _ _
         (<ᵣWeaken≤ᵣ _ _ q<x)
         x∈)
      (pre-invℝ₊UC (δ , ℚ<→0< δ (<ᵣ→<ℚ 0 δ 0<q)))))
    (denseℚinℝ _ _ 0<x)

arcSin'-UC : ∀ x → (x∈ : x ∈ pred≤< 0 1) →
   ∥ IsUContinuousℙ (intervalℙ 0 x)
      (λ x' x'∈ → arcSin' x' (fst x'∈ , isTrans≤<ᵣ x' x 1 (snd x'∈) (snd x∈)))
      ∥₁
arcSin'-UC y (0≤y , y<1) =
 let z =
      PT.map (flip (IsUContinuousℙ∘ℙ (intervalℙ 0 y)
        (intervalℙ (fst (root 2 (1 -ᵣ y ^ⁿ 2 ,
          (x<y→0<y-x _ _ (^<1 y 0≤y 1 y<1)))))  1)
        {λ x x∈ → fst
          (invℝ₊
           ((x , isTrans<≤ᵣ _ _ _
             (snd (root 2 (1 -ᵣ (y ^ⁿ 2) ,
             x<y→0<y-x (y ^ⁿ 2) 1 (^<1 y 0≤y 1 y<1))))
             (fst  x∈))))}
                 λ x' (0≤x' , x'<y) →
                   ₙ√-Monotone 2 (≤ᵣ-o+ _ _ 1
                    (-ᵣ≤ᵣ _ _ (^ⁿ-Monotone 2 0≤x'  x'<y)))  ,
                   (isTrans≤≡ᵣ _ _ _
                   (ₙ√-Monotone {y = 1} 2 (isTrans≤≡ᵣ _ _ _
                     (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ _ _ ( 0≤x^ⁿ x' 2 0≤x')))
                      (𝐑'.+IdR' _ _ (-ᵣ-rat 0))))
                    (cong fst (ₙ√1 2) )) )

         (IsUContinuousℙ∘ℙ (intervalℙ 0 y) (pred> 0)
           {λ x x∈ → fst (root 2 (x , x∈)) }
            {λ x _ → 1 -ᵣ (x ^ⁿ 2)}
           (λ x x∈ → x<y→0<y-x _ _ (^<1 x (fst x∈) 1
            (isTrans≤<ᵣ _ _ _ (snd x∈) y<1)))
           (uContRoot 2)
           (IsUContinuousℙ+ᵣ₂ (intervalℙ 0 y) _ _
            (IsUContinuousℙ-const (intervalℙ 0 y) 1)
            (IsUContinuousℙ-ᵣ∘
             (intervalℙ 0 y) _
               (IsUContinuousℙ-restr (intervalℙ 0 1) (intervalℙ 0 y)
                 _ (λ x → map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ y<1) ))
               (IsUContinuousℙ^ⁿ 0 1 ((decℚ≤ᵣ? {0} {1})) 2)))))
               )

        (PT.map
         (subst (IsUContinuousℙ (intervalℙ _ 1))
          (funExt₂ λ x _ → cong (fst ∘ invℝ₊) (ℝ₊≡ refl)) ∘
            IsUContinuousℙ-restr (pred≥ _)
             (intervalℙ _ 1)
              (λ x x∈ → fst (invℝ₊ (x , _)))
               λ _ → fst)
            (invℝ₊UC _ ((snd (root 2 (1 -ᵣ y ^ⁿ 2 ,
          (x<y→0<y-x _ _ (^<1 y 0≤y 1 y<1))))))))
  in
    PT.map (subst (IsUContinuousℙ (intervalℙ (rat [ pos 0 / 1+ 0 ]) y))
     (funExt₂ λ x x∈ →
        cong (fst ∘ invℝ₊) (ℝ₊≡
          refl))) z

opaque
 arcSinDef : ∀ x → (x∈ : x ∈ pred≤< 0 1) →
   Σ[ arcSinX ∈ ℝ ]
     (on[ 0 , x ]IntegralOf
       (λ x' ≤x x< → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x< (snd x∈))) is arcSinX )
 arcSinDef x x∈@(0≤x , x<1) =
  PT.rec
   (IntegratedℙPropℙ _ _ 0≤x _)
    (Integrate-UContinuousℙ
    0
    x
    0≤x
    (λ x' x'∈ → arcSin' x' ((fst x'∈) , isTrans≤<ᵣ _ _ _ (snd x'∈) x<1)))
    (arcSin'-UC x x∈)
