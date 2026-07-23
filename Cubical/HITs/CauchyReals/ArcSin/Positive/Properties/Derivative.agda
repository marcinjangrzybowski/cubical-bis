module Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT


open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Archimedean using
  (∃ℚ₊LargerThanℝ₊)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.FundamentalTheorem using
  ( FTOC⇒* )
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base using (isEquiv-₊^ⁿ)

open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic
open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone.Quarter
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Definition public
arcSinDer : ∀ x → (x∈ : x ∈ ointervalℙ 0 1) →
 uDerivativeOfℙ intervalℙ 0 x ,
  (λ x' (≤x , x≤) → arcSin x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈))) is
    (λ x' (≤x , x≤) → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈)))
arcSinDer x x∈ =
   PT.rec (isProp-uDerivativeOfℙ (intervalℙ 0 x) _ _)
        (FTOC⇒* 0 x (<ᵣWeaken≤ᵣ _ _ (fst x∈))
          _
          _
            (λ x₁ x∈₁ y y∈ →
              (fst y∈ , isTrans≤ᵣ _ _ _ (snd y∈) (snd x∈₁)))
            λ y y∈ →
              subst (λ f → on[ 0 , y ]IntegralOf
                f
                is (arcSinDef y (y∈ .fst ,
                 isTrans≤<ᵣ y x 1 (y∈ .snd) (snd x∈)) .fst))
                (funExt₃ λ x' _ _ →
                 cong (arcSin' x') (∈-isProp (pred≤< 0 1) _ _ _) )
                  ((snd (arcSinDef y
                         (y∈ .fst , isTrans≤<ᵣ y x 1 (y∈ .snd) (snd x∈))))))
        (arcSin'-UC x (<ᵣWeaken≤ᵣ _ _ (fst x∈) , snd x∈))



x∈[0,π/2⟩→sin[x]∈[0,1⟩ : ∀ x → x ∈ pred≤< 0 π-number/2 → sin x ∈ pred≤< 0 1
x∈[0,π/2⟩→sin[x]∈[0,1⟩ x x∈ =
 isTrans≡≤ᵣ _ _ _ (sym sin0=0)
  (sin-firstQuarter-Monotone 0 x
   (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ 0<π-number/2)
    (map-snd (<ᵣWeaken≤ᵣ _ _) x∈)
    (fst x∈))
  ,
  (isTrans<≡ᵣ _ _ _
   (sin-firstQuarter-strictMonotone _ _
    (fst x∈ , <ᵣWeaken≤ᵣ _ _ (snd x∈))
     (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) (snd x∈))
   sin[π/2]≡1)

x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ : ∀ x → x ∈ ointervalℙ 0 π-number/2 → sin x ∈ ointervalℙ 0 1
x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈ =
  isTrans≡<ᵣ _ _ _ (sym sin0=0)
  (sin-firstQuarter-strictMonotone 0 x
   ((≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ 0<π-number/2))
    (ointervalℙ⊆intervalℙ _ _ _ x∈)
    (fst x∈))
  ,
  (isTrans<≡ᵣ _ _ _
   (sin-firstQuarter-strictMonotone _ _
    (ointervalℙ⊆intervalℙ _ _ _ x∈ )
     (<ᵣWeaken≤ᵣ _ _ 0<π-number/2 , ≤ᵣ-refl _) (snd x∈))
   sin[π/2]≡1)


bounded-arcSin' : ∀ x → (x∈ : x ∈ ointervalℙ 0 1) →
  ∥ Bounded (intervalℙ 0 x)
    (λ x' (≤x , x≤) → arcSin' x' (≤x , isTrans≤<ᵣ _ _ _ x≤ (snd x∈)))
    ∥₁
bounded-arcSin' x x∈ =
  PT.map
   (map-snd (λ {q} X x' x'∈ →
     isTrans≡≤ᵣ _ _ _ (absᵣPos _ (snd (arcSin'₊ x'
        (map-snd (flip (isTrans≤<ᵣ _ _ _) (snd x∈)) x'∈ ))))
      (isTrans≤ᵣ _ _ _
       (arcSin'-Monotone x' x _ _ (snd x'∈))
       (<ᵣWeaken≤ᵣ _ _ X))))
   (∃ℚ₊LargerThanℝ₊
    (arcSin'₊ x (map-fst (<ᵣWeaken≤ᵣ _ _) x∈)))


sin＃-firstQuarter : (x y : ℝ) (x∈ : x ∈ intervalℙ 0 π-number/2)
      (y∈ : y ∈ intervalℙ 0 π-number/2) →
      x ＃ y → sin x ＃ sin y
sin＃-firstQuarter x y x∈ y∈ =
 ⊎.map (sin-firstQuarter-strictMonotone x y x∈ y∈)
       (sin-firstQuarter-strictMonotone y x y∈ x∈)

[arcSin∘Sin]'=1 : ∀ x → (x∈ : x ∈ ointervalℙ 0 π-number/2) →
  uDerivativeOfℙ (intervalℙ 0 x) ,
     (λ x' x'∈ → arcSin (sin x')
      ((x∈[0,π/2⟩→sin[x]∈[0,1⟩ x'
       (map-snd (flip (isTrans≤<ᵣ _ _ _) (snd x∈)) x'∈)))) is λ _ _ → 1
[arcSin∘Sin]'=1 x x∈ =
  subst2 (uDerivativeOfℙ (intervalℙ 0 x) ,_is_)
      (funExt₂ λ _ _ → cong (uncurry arcSin)
       (Σ≡Prop (∈-isProp (pred≤< 0 1)) refl))
      (funExt₂ w=)
      w
 where
 w : uDerivativeOfℙ intervalℙ 0 x , _ is _

 w = chainRule-uDerivativeℙ (intervalℙ 0 x) (intervalℙ 0 (sin x))
        (λ x _ → sin x) (λ x _ → cos x) _ _
        (bounded-cos (intervalℙ 0 x))
        (bounded-arcSin' (sin x) (x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈)) --bounded-arcSin'
        (λ y y∈ → fst (x∈[0,π/2⟩→sin[x]∈[0,1⟩ y
          ((map-snd (flip (isTrans≤<ᵣ y x π-number/2) (snd x∈)) y∈))) ,
         sin-firstQuarter-Monotone y x
           (map-snd (flip (isTrans≤ᵣ _ _ _) (<ᵣWeaken≤ᵣ _ _ (snd x∈))) y∈)
           (ointervalℙ⊆intervalℙ _ _ _ x∈) (snd y∈))
        (uContSin (intervalℙ 0 x))
        (arcSinDer (sin x) (x∈⟨0,π/2⟩→sin[x]∈⟨0,1⟩ x x∈))
        (sin'=cos-uder' 0 x (fst x∈))



 w= : ∀ (x' : ℝ) x'∈ →
      _ ≡ 1
 w= x' x'∈ =
   cong (_·ᵣ fst cosx₊)
    (cong (fst ∘ invℝ₊)
      (ℝ₊≡ (cong fst (sym
       (invEq (equivAdjointEquiv
         (_ , isEquiv-₊^ⁿ 2) {_ , snd cosx₊})
        (ℝ₊≡
         (sym (𝐑'.plusMinus _ _)
         ∙ cong (_-ᵣ (sin x' ^ⁿ 2))
         (+ᵣComm _ _ ∙ sin²+cos²=1 x'))))))))
    ∙ ·ᵣComm _ _ ∙ x·invℝ₊[x] cosx₊
  where
   cosx₊ : ℝ₊
   cosx₊ = (cos x' , 0≤x<π/2→0<cos[x] x' (fst x'∈)
     (isTrans≤<ᵣ _ _ _ (snd x'∈) (snd x∈)))
