module Cubical.HITs.CauchyReals.Algebra.Order.Apartness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.NatPlusOne

open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


_＃_ : ℝ → ℝ → Type
x ＃ y = (x <ᵣ y) ⊎ (y <ᵣ x)


isProp＃ : ∀ x y → isProp (x ＃ y)
isProp＃ x y (inl x₁) (inl x₂) = cong inl (isProp<ᵣ _ _ x₁ x₂)
isProp＃ x y (inl x₁) (inr x₂) = ⊥.rec (isAsym<ᵣ _ _ x₁ x₂)
isProp＃ x y (inr x₁) (inl x₂) = ⊥.rec (isAsym<ᵣ _ _ x₁ x₂)
isProp＃ x y (inr x₁) (inr x₂) = cong inr (isProp<ᵣ _ _ x₁ x₂)


rat＃ : ∀ q q' → (rat q ＃ rat q') ≃ (q ℚ.# q')
rat＃ q q' = propBiimpl→Equiv (isProp＃ _ _) (ℚ.isProp# _ _)
  (⊎.map (<ᵣ→<ℚ _ _) (<ᵣ→<ℚ _ _))
  (⊎.map (<ℚ→<ᵣ _ _) (<ℚ→<ᵣ _ _))


decCut : ∀ x → 0 <ᵣ absᵣ x → 0 ＃ x
decCut x 0<absX =
  PT.rec (isProp＃ 0 x)
    (λ (Δ , Δ<absX) →
      PT.rec (isProp＃ 0 x)
        (λ (q , q-x<Δ/2 , x<q) →
          let z→ : 0 ℚ.< q → 0 <ᵣ x
              z→ 0<q =
                let zzz : rat q <ᵣ rat (fst (Δ /2₊)) → 0 <ᵣ x
                    zzz q<Δ/2 =
                      let zzz' =
                            subst2 _≤ᵣ_
                              (cong absᵣ ℝ!)
                              (cong₂ _+ᵣ_
                                (absᵣNonNeg _
                                  (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ 0 q 0<q)))
                                (minusComm-absᵣ _ _ ∙
                                  absᵣNonNeg _
                                    (subst (_≤ᵣ (rat q +ᵣ -ᵣ x))
                                      (+-ᵣ x)
                                      (≤ᵣ-+o _ _ (-ᵣ x)
                                        (<ᵣWeaken≤ᵣ _ _ x<q)))))
                              (absᵣ-triangle (rat q) (x +ᵣ -ᵣ rat q))
                          zzzz' =
                            subst (absᵣ x <ᵣ_)
                              (+ᵣ-rat _ _ ∙ cong rat ℚ!!)
                              (isTrans≤<ᵣ _ _ _ zzz'
                                (<ᵣMonotone+ᵣ _ _ _ _
                                  q<Δ/2 q-x<Δ/2))
                      in ⊥.rec (isAsym<ᵣ _ _ Δ<absX zzzz')
                in ⊎.rec
                  (λ Δ≤q →
                    subst2 _<ᵣ_
                      (+-ᵣ (rat (fst (Δ /2₊))))
                      (cong (rat q +ᵣ_) (-ᵣDistr (rat q) (-ᵣ x))
                        ∙ (λ i → +ᵣAssoc (rat q) (-ᵣ rat q)
                          (-ᵣInvol x i) i)
                        ∙ cong (_+ᵣ x) (+-ᵣ (rat q))
                        ∙ +IdL x)
                      (≤<ᵣMonotone+ᵣ (rat (fst (Δ /2₊))) (rat q) _ _
                        (≤ℚ→≤ᵣ _ _ Δ≤q) (-ᵣ<ᵣ _ _ q-x<Δ/2)))
                  (zzz ∘S <ℚ→<ᵣ _ _)
                  (ℚ.Dichotomyℚ (fst (Δ /2₊)) q)
              z← : q ℚ.≤ 0 → x <ᵣ 0
              z← q≤0 = isTrans<≤ᵣ _ _ _ x<q (≤ℚ→≤ᵣ q 0 q≤0)
          in ⊎.rec (inr ∘ z←) (inl ∘ z→) (ℚ.Dichotomyℚ q 0))
        (∃rationalApprox< x (Δ /2₊)))
    (lowerℚBound _ 0<absX)


opaque
  ＃≃0<dist : ∀ x y → x ＃ y ≃ (0 <ᵣ absᵣ (x +ᵣ -ᵣ y))
  ＃≃0<dist x y = propBiimpl→Equiv (isProp＃ _ _) (isProp<ᵣ _ _)
    (⊎.rec
      (λ x<y → subst (0 <ᵣ_)
        (minusComm-absᵣ y x)
        (isTrans<≤ᵣ _ _ _
          (subst (_<ᵣ (y +ᵣ -ᵣ x))
            (+-ᵣ x) (<ᵣ-+o _ _ (-ᵣ x) x<y))
          (≤absᵣ _)))
      (λ y<x → isTrans<≤ᵣ _ _ _
        (subst (_<ᵣ (x +ᵣ -ᵣ y))
          (+-ᵣ y) (<ᵣ-+o _ _ (-ᵣ y) y<x))
        (≤absᵣ _)))
    (⊎.rec
      (inr ∘S subst2 _<ᵣ_ (+IdL _) ℝ! ∘S <ᵣ-+o _ _ y)
      (inl ∘S subst2 _<ᵣ_ ℝ! (+IdR y) ∘S <ᵣ-o+ _ _ y)
      ∘S decCut (x +ᵣ -ᵣ y))


isSym＃ : BinaryRelation.isSym _＃_
isSym＃ _ _ = fst ⊎-swap-≃


opaque
  unfolding _<ᵣ_

  0＃→0<abs : ∀ r → 0 ＃ r → 0 <ᵣ absᵣ r
  0＃→0<abs r 0＃r =
    subst (rat 0 <ᵣ_) (cong absᵣ (+IdR r))
      (fst (＃≃0<dist r 0) (isSym＃ 0 r 0＃r))
