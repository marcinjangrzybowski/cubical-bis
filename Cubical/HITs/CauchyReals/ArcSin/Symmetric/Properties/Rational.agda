module Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Rational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (_≤_ ; clamp)
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Order.Positive
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using (sin[π/2]≡1)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Derivative using
  ( x∈[0,π/2⟩→sin[x]∈[0,1⟩ )
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Inverse using
  ( arcSin
  ; arcSin[0]≡0
  ; retArcSin
  ; secArcSin
  )
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Base public

opaque
  unfolding arcSin⟨⟩

  arcSin⟨⟩∘sin-ℚ : ∀ (Q : ℚ₊) → (Q<π/2 : rat (fst Q) <ᵣ π-number/2)
    → ∀ q → (0 ℚ.≤ q) ⊎ (q ℚ.≤ 0)
    →  (q∈ : rat q ∈ intervalℙ (-ᵣ (rat (fst Q))) (rat (fst Q)))
    → ∀ sinq∈
     → arcSin⟨⟩ (sin (rat q)) sinq∈

     ≡ (rat q)
  arcSin⟨⟩∘sin-ℚ Q Q<π/2 q (inl 0≤q') (_ , q<Q) sinq∈@(_ , sinq<1) =
    let 0≤q : 0 ≤ᵣ (rat q)
        0≤q = ≤ℚ→≤ᵣ _ _ 0≤q'
        q<π/2 : (rat q) <ᵣ π-number/2
        q<π/2 = isTrans≤<ᵣ _ _ _ q<Q Q<π/2
        0≤sinq : 0 ≤ᵣ sin (rat q)
        0≤sinq = fst $ x∈[0,π/2⟩→sin[x]∈[0,1⟩ (rat q)
            (0≤q , q<π/2)

    in 𝐑'.+IdL' _ _ (
         cong -ᵣ_
           (cong (uncurry arcSin)
              (Σ≡Prop (∈-isProp (pred≤< 0 1))
               (x≤→clampᵣ≡ 0 1 (-ᵣ (sin (rat q)))
                decℚ≤ᵣ?
                (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _  0≤sinq)
                 (-ᵣ-rat 0)  )))
             ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
         ∙ -ᵣ-rat 0)
       ∙ cong (uncurry arcSin)
           ((Σ≡Prop (∈-isProp (pred≤< 0 1))
            (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ ( 0≤sinq , sin≤1 _)))))
            ∙ secArcSin _ (0≤sinq , sinq<1) (0≤q , q<π/2)
  arcSin⟨⟩∘sin-ℚ Q Q<π/2 q (inr q'≤0) (-Q<-q , _) sinq∈@(-1<sinq , _) =
    let 0≤-q : 0 ≤ᵣ -ᵣ rat q
        0≤-q = isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0))
                (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ _ _ q'≤0))

        sin-q<1 : sin (-ᵣ rat q) <ᵣ 1
        sin-q<1 = subst2 _<ᵣ_ (sin-odd (rat q)) (-ᵣ-rat -1)
            (-ᵣ<ᵣ _ _ -1<sinq)

        -q<π/2 : -ᵣ rat q <ᵣ π-number/2
        -q<π/2 = isTrans≤<ᵣ _ _ _ (-ᵣ≤ᵣ _ _ -Q<-q)
                  (isTrans≡<ᵣ _ _ _ (-ᵣInvol _) Q<π/2)

        sinq≤0 : sin (rat q) ≤ᵣ 0
        sinq≤0 = ≤ᵣ-ᵣ _ _
          (subst2 _≤ᵣ_ (sym (-ᵣ-rat 0)) (sym (sin-odd (rat q)))
           (fst (x∈[0,π/2⟩→sin[x]∈[0,1⟩ (-ᵣ (rat q))
            (0≤-q , -q<π/2))))

    in 𝐑'.+IdR' _ _
        (cong (uncurry arcSin)
              (Σ≡Prop (∈-isProp (pred≤< 0 1))
               (x≤→clampᵣ≡ 0 1 (sin (rat q))
                decℚ≤ᵣ? sinq≤0))
             ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
       ∙ cong -ᵣ_
         (cong (uncurry arcSin)
           (Σ≡Prop (∈-isProp (pred≤< 0 1)) {clampᵣ 0 1 (-ᵣ sin (rat q)) , _}
             (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _
               (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _ sinq≤0) ,
                (isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _
                 (≤absᵣ _) (sym (-absᵣ _))) (∣sin∣≤1 (rat q))))) ∙ sin-odd _))
           ∙ secArcSin _ (subst2 _≤ᵣ_
             (-ᵣ-rat 0) (sin-odd _) (-ᵣ≤ᵣ _ _ sinq≤0) , sin-q<1)
             (0≤-q , -q<π/2))
       ∙ -ᵣInvol (rat q)



  sin∘arcSin⟨⟩ℚ :
        ∀ q q∈ → (0 ℚ.≤ q) ⊎ (q ℚ.≤ 0)
      → sin (arcSin⟨⟩ (rat q) q∈) ≡ (rat q)
  sin∘arcSin⟨⟩ℚ q (-1<q , q<1) (inl 0≤q') =
     let 0≤q = ≤ℚ→≤ᵣ 0 q 0≤q'

     in cong sin (𝐑'.+IdL' _ _
          (cong -ᵣ_
            (cong (uncurry arcSin)
              (Σ≡Prop (∈-isProp (pred≤< 0 1))
               (x≤→clampᵣ≡ 0 1 (-ᵣ rat q)
                decℚ≤ᵣ?
                (isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _  0≤q)
                 (-ᵣ-rat 0)  )))
             ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))  ∙
            -ᵣ-rat 0)
            ∙ cong (uncurry arcSin)
                (Σ≡Prop (∈-isProp (pred≤< 0 1))
                  (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _
                   (0≤q , <ᵣWeaken≤ᵣ _ _ q<1)))))
           ∙ retArcSin _ (0≤q , q<1)
  sin∘arcSin⟨⟩ℚ q (-1<q , _) (inr q≤0') =
     let q≤0 = ≤ℚ→≤ᵣ q 0 q≤0'
         0≤-q : 0 ≤ᵣ -ᵣ rat q
         0≤-q = isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat 0)) (-ᵣ≤ᵣ _ _ q≤0)
         -q<1 : -ᵣ rat q <ᵣ 1
         -q<1 = isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ -1<q)
                  (-ᵣ-rat -1)
     in cong sin (𝐑'.+IdR' _ _ (cong (uncurry arcSin)
              (Σ≡Prop (∈-isProp (pred≤< 0 1))
               (x≤→clampᵣ≡ 0 1 (rat q)
                decℚ≤ᵣ? q≤0))
                ∙ arcSin[0]≡0 (≤ᵣ-refl 0 , decℚ<ᵣ?))
        ∙ cong -ᵣ_ (cong (uncurry arcSin)
           (Σ≡Prop (∈-isProp (pred≤< 0 1))
             (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 _ (0≤-q , (<ᵣWeaken≤ᵣ _ _ -q<1)))))))
       ∙ sym (sin-odd _)
       ∙ cong -ᵣ_ (retArcSin _ (0≤-q , -q<1))
       ∙ -ᵣInvol _


opaque
  ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ : ∀ x → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
         → sin x ∈ ointervalℙ -1 1
  ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ x x∈@(<x , x<) =
    isTrans≡<ᵣ _ _ _ ((sym (-ᵣ-rat 1) ∙ cong -ᵣ_ (sym (sin[π/2]≡1)))
     ∙ sin-odd π-number/2)
     (sin-strictMonotone (-ᵣ π-number/2) x
       (≤ᵣ-refl _ , <ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ π-number/2₊ π-number/2₊)) (ointervalℙ⊆intervalℙ _ _ x x∈) <x) ,
     isTrans<≡ᵣ _ _ _
       (sin-strictMonotone x (π-number/2)
        (ointervalℙ⊆intervalℙ _ _ x x∈)
         (<ᵣWeaken≤ᵣ _ _ ((-ℝ₊<ℝ₊ π-number/2₊ π-number/2₊)) , ≤ᵣ-refl _) x<)
       sin[π/2]≡1


sym-clamp-rat : ∀ q (Q : ℚ₊) →
                     clampᵣ (-ᵣ rat (fst Q)) (rat (fst Q)) (rat q) ≡
                    rat (ℚ.clamp (ℚ.- (fst Q)) (fst Q) q)
sym-clamp-rat q Q = (cong clampᵣ (-ᵣ-rat (fst Q))
  ≡$ (rat (fst Q)) ≡$ rat q) ∙ clampᵣ-rat (ℚ.- (fst Q)) (fst Q) q
