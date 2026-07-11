module Cubical.HITs.CauchyReals.Circle.Angle.CaseSplit where

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
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Circle.Base public

open import Cubical.HITs.CauchyReals.Circle.Angle.FirstQuadrant public
from-√½< : ∀ x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1
 → fst √½ <ᵣ absᵣ x → absᵣ (-ᵣ y) ≤ᵣ rat [ 3 / 4 ]
from-√½< x y x²+y²=1 √½<∣x∣ =
 let z = sym (𝐑'.plusMinus _ _)
           ∙ cong (_-ᵣ (x ^ⁿ 2)) (+ᵣComm _ _ ∙ x²+y²=1)

     zz = isTrans<≡ᵣ _ _ _ (^ⁿ-StrictMonotone 2
           (ℕ.≤-solver 1 2)
           (<ᵣWeaken≤ᵣ _ _ (snd √½) )
           (0≤absᵣ _) √½<∣x∣)
            (sym (abs[x^²ⁿ] 1 x ∙ absᵣ^ⁿ x 2))
     zzz : (y ^ⁿ 2) <ᵣ rat [ 1 / 2 ]
     zzz = isTrans<≡ᵣ _ _ (rat [ 1 / 2 ]) (isTrans≡<ᵣ _ _ _ z
             (<ᵣ-o+ _ _ 1 (-ᵣ<ᵣ _ _ zz)))
              (cong (1 +ᵣ_) (cong -ᵣ_
                (cong fst (Iso.sec
                  (nth-pow-root-iso 2) (ℚ₊→ℝ₊ ([ 1 / 2 ] , _))) ))
               ∙  (-ᵣ-rat₂ _ _) ∙ decℚ≡ᵣ?)

 in isTrans≡≤ᵣ _ _ _
    (sym (-absᵣ _))
     (^ⁿMonotone⁻¹-with0 2 (ℕ.≤-solver 1 2)
       (0≤absᵣ _) decℚ<ᵣ?
        (isTrans≡≤ᵣ _ _ _
          (sym (abs[x^²ⁿ] 1 y ∙ absᵣ^ⁿ y 2))
          (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ zzz)
          (isTrans≤≡ᵣ _ _ _ decℚ≤ᵣ? (sym (cong fst (^ℤ-rat _ 2)))))))





distCircle→angle-badConvention : ∀ (ε : ℝ₊) x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1 →
  ∃[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
    × ((sin φ ≡ x) × (cos φ ≡ y)))
distCircle→angle-badConvention ε x y x²+y²=1 = do
 c ← Dichotomyℝ' (fst √½) (absᵣ x)
      (rat [ 3 / 4 ])
      √½<3/4

 let f-inl-inl (φ , φ∈ , sinφ , cosφ) =
        ∣ φ , ointervalℙ⊆ointervalℙ
            (-ᵣ≤ᵣ _ _ (isTrans≡≤ᵣ _ _ _
                (sym (+IdR _))
                (isTrans≤≡ᵣ _ _ _
                 ((≤ᵣ-o+ _ _ _ (<ᵣWeaken≤ᵣ _ _ 0<π-number/2)))
                  (x+x≡2x _))))
            (isTrans≤≡ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (sym (+IdR _))
                (≤ᵣ-o+ _ _ _ (<ᵣWeaken≤ᵣ _ _
                 (snd ((_ , 0<π-number/2) ₊+ᵣ ε)))))
              (+ᵣAssoc _ _ _ ∙ cong₂ _+ᵣ_ (x+x≡2x _) refl))
            φ φ∈ , sinφ , cosφ ∣₁
     f-inl-inr (φ , φ∈ , sinφ , cosφ) = do
       c ← Dichotomyℝ' π-number φ (π-number +ᵣ fst ε)
             (isTrans≡<ᵣ _ _ _
                (sym (+IdR _))
                (<ᵣ-o+ _ _ _ (snd ε)))
       let f-inl-inr-inl : φ <ᵣ π-number +ᵣ fst ε →
              ∃[ φ ∈ ℝ ]
                ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
                 × ((sin φ ≡ x) × (cos φ ≡ y)))
           f-inl-inr-inl φ<π+ε =
               (∣ φ , (isTrans<ᵣ _ _ _
                    (-ℝ₊<ℝ₊ π-number₊ π-number/2₊) (fst φ∈)
                      , φ<π+ε) , sinφ , cosφ ∣₁)
           f-inl-inr-inr : π-number <ᵣ φ   →
              ∃[ φ ∈ ℝ ]
                ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
                 × ((sin φ ≡ x) × (cos φ ≡ y)))
           f-inl-inr-inr π<φ =
              ∣ (φ -ᵣ 2 ·ᵣ π-number) ,
                   (isTrans≡<ᵣ _ _ _
                      (𝐑'.equalByDifference _ _
                        (sym (-ᵣDistr _ _)
                          ∙ cong -ᵣ_
                           (+ᵣAssoc _ _ _ ∙
                            𝐑'.+InvR' _ _
                             (x+x≡2x _))
                          ∙ -ᵣ-rat 0))
                      (<ᵣ-+o _ _ (-ᵣ (2 ·ᵣ π-number)) π<φ)
                  , isTrans<ᵣ _ _ _
                      (<ᵣ-+o _ _ (-ᵣ (2 ·ᵣ π-number)) (snd φ∈))
                      (isTrans≡<ᵣ _ _ _
                       (cong₂ _+ᵣ_ refl (cong -ᵣ_ (sym (x+x≡2x _))
                         ∙ -ᵣDistr _ _) ∙ sym (+ᵣAssoc _ _ _) ∙
                        cong₂ _+ᵣ_ refl (+ᵣAssoc _ _ _ ∙
                         𝐑'.+IdL' _ _ (+-ᵣ _ ))
                         ∙ cong₂ _+ᵣ_ refl (cong -ᵣ_ (sym (x+x≡2x _))
                         ∙ -ᵣDistr _ _) ∙
                         +ᵣComm _ _ ∙ 𝐑'.minusPlus _  _)
                         (-ℝ₊<ℝ₊ π-number/2₊ (π-number₊ ₊+ᵣ ε))))
                    , sym (sin-period _) ∙
                      cong sin (𝐑'.minusPlus _ _) ∙ sinφ
                    , (sym (cos-period _) ∙
                      cong cos (𝐑'.minusPlus _ _)) ∙ cosφ ∣₁
       ⊎.rec f-inl-inr-inl f-inl-inr-inr c
     f-inl =
          ⊎.rec f-inl-inl f-inl-inr
       ∘S (λ (φ , u , v) → ⊎.map (λ u → φ , u , v) (λ u → φ , u , v) u)
       ∘S pre-distCircle→angle x y x²+y²=1
       ∘S <ᵣWeaken≤ᵣ _ _
     f-inr-inl (φ , φ∈ , sinφ , cosφ) =
       ∣ φ +ᵣ π-number/2 ,
           ((isTrans<ᵣ _ _ _
             (isTrans<≡ᵣ _ _ _
               (-ᵣ<ᵣ _ _ (snd π-number₊))
               (-ᵣ-rat 0 ∙ sym (+-ᵣ _) ∙ +ᵣComm _ _))
             (<ᵣ-+o _ _ (π-number/2) (fst φ∈))) ,
             isTrans<ᵣ _ _ _
               (<ᵣ-+o _ _ (π-number/2) (snd φ∈))
               (isTrans≡<ᵣ _ _ _ (x+x≡2x _ ∙ sym (+IdR _))
                 (<ᵣ-o+ _ _ _ (snd ε))))
             , sin[x+π/2]=cos[x] φ ∙ cosφ
             , cos[x+π/2]=-sin[x] φ ∙
                    cong -ᵣ_ sinφ ∙ -ᵣInvol _ ∣₁
     f-inr-inr (φ , φ∈ , sinφ , cosφ) = do
       c ← Dichotomyℝ' π-number/2 φ (π-number/2 +ᵣ fst ε)
             (isTrans≡<ᵣ _ _ _
                (sym (+IdR _))
                (<ᵣ-o+ _ _ _ (snd ε)))
       let sinφ' = sin[x+π/2]=cos[x] φ ∙ cosφ
           cosφ' = cos[x+π/2]=-sin[x] φ ∙
                    cong -ᵣ_ sinφ ∙ -ᵣInvol _
           f-inr-inr-inl : φ <ᵣ π-number/2 +ᵣ fst ε →
              ∃[ φ ∈ ℝ ]
                ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
                 × ((sin φ ≡ x) × (cos φ ≡ y)))
           f-inr-inr-inl φ<π/2+ε =
               (∣ φ +ᵣ π-number/2
                 , (isTrans<ᵣ _ _ _
                      (-ℝ₊<ℝ₊ π-number₊ (π-number/2₊ ₊+ᵣ π-number/2₊))
                      (<ᵣ-+o _ _ π-number/2 (fst φ∈)) ,
                  subst2 _<ᵣ_
                    (+ᵣComm _ _)
                    (+ᵣAssoc _ _ _  ∙
                     cong₂ _+ᵣ_
                       (x+x≡2x _)
                       refl)
                    (<ᵣ-o+ _ _ π-number/2 φ<π/2+ε))
                , sinφ' , cosφ' ∣₁)
           f-inr-inr-inr : π-number/2 <ᵣ φ   →
              ∃[ φ ∈ ℝ ]
                ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
                 × ((sin φ ≡ x) × (cos φ ≡ y)))
           f-inr-inr-inr π/2<φ =
              ∣ _ ,
                ( isTrans<≡ᵣ _ _ _
                    (a-b<c⇒a<c+b _ _ _
                     (isTrans≡<ᵣ _ _ _
                        (cong₂ _-ᵣ_
                           (cong -ᵣ_ (sym (x+x≡2x _)))
                           (cong₂ _-ᵣ_ refl
                             (cong (2 ·ᵣ_) (sym (x+x≡2x _))
                              ∙ sym (x+x≡2x _)))
                          ∙ ℝ!)
                          π/2<φ))
                    (+ᵣAssoc _ _ _)
                , <-o+-cancel _ _ π-number/2
                  (isTrans<ᵣ _ _ _
                   (isTrans≡<ᵣ _ _ _
                     (+ᵣComm _ _ ∙
                      sym (+ᵣAssoc _ _ _ ∙ +ᵣAssoc _ _ _) ∙
                      cong (φ +ᵣ_) (+ᵣComm _ _ ∙ sym (+ᵣAssoc _ _ _) ∙
                       cong₂ _+ᵣ_ (cong -ᵣ_ (sym (x+x≡2x _))) (x+x≡2x _)
                        ∙ cong₂ _+ᵣ_ (-ᵣDistr _ _) refl
                          ∙ 𝐑'.minusPlus _ _ ))
                     (<ᵣ-o+ _ _ _ (isTrans<≡ᵣ _ _ _
                       (-ᵣ<ᵣ _ _ (snd (π-number₊)))
                       (-ᵣ-rat 0))))
                   (isTrans<≡ᵣ _ _ _
                     (<ᵣMonotone+ᵣ _ _ _ _ (snd φ∈) (snd ε))
                     (sym (+ᵣAssoc _ _ _)))))
               , sym (sin-period _) ∙
                      cong sin (𝐑'.minusPlus _ _) ∙ sinφ'
               , (sym (cos-period _) ∙
                      cong cos (𝐑'.minusPlus _ _)) ∙ cosφ' ∣₁
       ⊎.rec f-inr-inr-inl f-inr-inr-inr c
     f-inr = ⊎.rec f-inr-inl f-inr-inr
       ∘S (λ (φ , u , v) → ⊎.map (λ u → φ , u , v) (λ u → φ , u , v) u)

 ⊎.rec
   f-inl
   (f-inr
    ∘S pre-distCircle→angle (-ᵣ y) x
     (cong₂ _+ᵣ_ (sym (^ⁿ-even 1 y)) refl ∙ +ᵣComm _ _ ∙ x²+y²=1)
    ∘S from-√½< x y x²+y²=1) c


distCircle→angle : ∀ (ε : ℝ₊) x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1 →
  ∃[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
    × ((cos φ ≡ x) × (sin φ ≡ y)))
distCircle→angle ε x y p =
  PT.map (map-snd (map-snd λ (x , y) → y , x))
    (distCircle→angle-badConvention ε y x
    (+ᵣComm _ _ ∙ p))
