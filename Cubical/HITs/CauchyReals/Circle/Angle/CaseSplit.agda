module Cubical.HITs.CauchyReals.Circle.Angle.CaseSplit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.Rationals as ℚ using ([_/_])
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_ ; ^ⁿ-even)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence using (Dichotomyℝ')
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.Positive

open import Cubical.HITs.CauchyReals.TrigBase using (sin ; cos)
open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Circle.Base public

open import Cubical.HITs.CauchyReals.Circle.Angle.FirstQuadrant public
open import Cubical.HITs.CauchyReals.Circle.Angle.Bounds public using (from-√½<)

AngleTarget : ℝ₊ → ℝ → ℝ → Type
AngleTarget ε x y =
  ∃[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
    × ((sin φ ≡ x) × (cos φ ≡ y)))

PreAngleTarget : ℝ → ℝ → Type
PreAngleTarget x y =
  Σ[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number/2) π-number/2)
              ⊎ (φ ∈ ointervalℙ π-number/2 (π-number/2 +ᵣ π-number)))
      × ((sin φ ≡ x) × (cos φ ≡ y))

angle-from-first-half : ∀ ε x y → PreAngleTarget x y → AngleTarget ε x y
angle-from-first-half ε x y (φ , inl φ∈ , sinφ , cosφ) =
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
angle-from-first-half ε x y (φ , inr φ∈ , sinφ , cosφ) = do
  c ← Dichotomyℝ' π-number φ (π-number +ᵣ fst ε)
        (isTrans≡<ᵣ _ _ _
           (sym (+IdR _))
           (<ᵣ-o+ _ _ _ (snd ε)))
  let f-inl : φ <ᵣ π-number +ᵣ fst ε → AngleTarget ε x y
      f-inl φ<π+ε =
          ∣ φ , (isTrans<ᵣ _ _ _
               (-ℝ₊<ℝ₊ π-number₊ π-number/2₊) (fst φ∈)
                 , φ<π+ε) , sinφ , cosφ ∣₁
      f-inr : π-number <ᵣ φ → AngleTarget ε x y
      f-inr π<φ =
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
  ⊎.rec f-inl f-inr c

angle-from-second-half : ∀ ε x y → PreAngleTarget (-ᵣ y) x → AngleTarget ε x y
angle-from-second-half ε x y (φ , inl φ∈ , sinφ , cosφ) =
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
angle-from-second-half ε x y (φ , inr φ∈ , sinφ , cosφ) = do
  c ← Dichotomyℝ' π-number/2 φ (π-number/2 +ᵣ fst ε)
        (isTrans≡<ᵣ _ _ _
           (sym (+IdR _))
           (<ᵣ-o+ _ _ _ (snd ε)))
  let sinφ' = sin[x+π/2]=cos[x] φ ∙ cosφ
      cosφ' = cos[x+π/2]=-sin[x] φ ∙
               cong -ᵣ_ sinφ ∙ -ᵣInvol _
      f-inl : φ <ᵣ π-number/2 +ᵣ fst ε → AngleTarget ε x y
      f-inl φ<π/2+ε =
          ∣ φ +ᵣ π-number/2
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
           , sinφ' , cosφ' ∣₁
      f-inr : π-number/2 <ᵣ φ → AngleTarget ε x y
      f-inr π/2<φ =
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
  ⊎.rec f-inl f-inr c

distCircle→angle-badConvention : ∀ (ε : ℝ₊) x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1 →
  ∃[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
    × ((sin φ ≡ x) × (cos φ ≡ y)))
distCircle→angle-badConvention ε x y x²+y²=1 = do
 c ← Dichotomyℝ' (fst √½) (absᵣ x)
      (rat [ 3 / 4 ])
      √½<3/4
 ⊎.rec
   (λ ∣x∣<3/4 →
      angle-from-first-half ε x y
        (pre-distCircle→angle x y x²+y²=1
          (<ᵣWeaken≤ᵣ _ _ ∣x∣<3/4)))
   (λ √½<∣x∣ →
      angle-from-second-half ε x y
        (pre-distCircle→angle (-ᵣ y) x
          (cong₂ _+ᵣ_ (sym (^ⁿ-even 1 y)) refl ∙ +ᵣComm _ _ ∙ x²+y²=1)
          (from-√½< x y x²+y²=1 √½<∣x∣)))
   c


distCircle→angle : ∀ (ε : ℝ₊) x y → x ^ⁿ 2 +ᵣ y ^ⁿ 2 ≡ 1 →
  ∃[ φ ∈ ℝ ] ((φ ∈ ointervalℙ (-ᵣ π-number) (π-number +ᵣ fst ε))
    × ((cos φ ≡ x) × (sin φ ≡ y)))
distCircle→angle ε x y p =
  PT.map (map-snd (map-snd λ (x , y) → y , x))
    (distCircle→angle-badConvention ε y x
    (+ᵣComm _ _ ∙ p))
