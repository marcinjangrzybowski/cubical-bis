module Cubical.HITs.CauchyReals.Algebra.Order.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

import Cubical.Functions.Logic as L

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Binary

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
 unfolding _<ᵣ_

 isIrrefl<ᵣ : BinaryRelation.isIrrefl _<ᵣ_
 isIrrefl<ᵣ a = PT.rec isProp⊥
   λ ((q , q') , (a≤q , q<q' , q'≤a)) →
     ℚ.≤→≯ _ _ (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _ q'≤a a≤q)) q<q'


Dichotomyℝ' : ∀ x y z → x <ᵣ z →
              ∥ (y <ᵣ z) ⊎ (x <ᵣ y) ∥₁
Dichotomyℝ' x y z x<z =
  PT.map2
   (λ (q  , x<q  , q<x+Δ)
      (q' , y-Δ<q' , q'<y)
     → ⊎.map
         (λ q'≤q →
           isTrans<ᵣ _ _ _
             (a-b<c⇒a<c+b _ _ _ y-Δ<q')
             (isTrans<≡ᵣ _ _ _
               (<ᵣ-+o _ _ _
                 ((isTrans≤<ᵣ _ _ _ (≤ℚ→≤ᵣ q' _ q'≤q)
                  q<x+Δ ))) ℝ!))
         (λ q<q' →
           isTrans<ᵣ _ _ _ (isTrans<ᵣ _ _ _
               x<q
               (<ℚ→<ᵣ q _ q<q'))
             q'<y)
         (ℚ.Dichotomyℚ q' q))
    (denseℚinℝ x (x +ᵣ (fst Δ₊))
      (isTrans≡<ᵣ _ _ _
        (sym (+IdR x)) (<ᵣ-o+ _ _ _ (snd Δ₊))))
    (denseℚinℝ (y -ᵣ (fst Δ₊)) y
      (isTrans<≡ᵣ _ _ _
         (<ᵣ-o+ _ _ _
           (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ (snd Δ₊)) (-ᵣ-rat 0)))
         (+IdR y)))
 where
 Δ₊ : ℝ₊
 Δ₊ =
   ( (z -ᵣ x) ·ᵣ fst (ℚ₊→ℝ₊ [ 1 / 2 ]₊)
   , ℝ₊· (z -ᵣ x , x<y→0<y-x _ _ x<z) (ℚ₊→ℝ₊ [ 1 / 2 ]₊))


x<δ→x≤0 : ∀ x → ((ε : ℚ₊) → x <ᵣ (rat (fst ε))) → x ≤ᵣ 0
x<δ→x≤0 x p = ≡→≤ᵣ (eqℝ _ _
  λ ε → invEq (∼≃abs<ε _ _ _)
    (isTrans≡<ᵣ _ _ _
      (cong absᵣ (ℝ! ∙ maxᵣComm _ _)
        ∙ absᵣNonNeg _ (≤maxᵣ 0 x) ∙ maxᵣComm _ _)
      (p' ε)))
  where
  p' : (ε : ℚ₊) → maxᵣ x 0 <ᵣ rat (fst ε)
  p' ε = max<-lem _ _ _ (p ε) (snd (ℚ₊→ℝ₊ ε))


x<y+δ→x≤y : ∀ x y →
  ((ε : ℚ₊) → x <ᵣ y +ᵣ rat (fst ε)) → x ≤ᵣ y
x<y+δ→x≤y x y p = invEq (x≤y≃0≤y-x _ _)
  (isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _ ℝ!
      (-ᵣ≤ᵣ _ 0 (x<δ→x≤0 _ (a<c+b⇒a-c<b _ _ _ ∘ p))))
    (-[x-y]≡y-x _ _))


≤ᵣ→≯ᵣ : ∀ x y → x ≤ᵣ y → (y <ᵣ x) → ⊥
≤ᵣ→≯ᵣ x y x≤y y<x =
  let x=y = isAntisym≤ᵣ x y x≤y (<ᵣWeaken≤ᵣ _ _ y<x)
  in isAsym<ᵣ y x y<x (subst2 _<ᵣ_ (sym x=y) x=y y<x)


≯ᵣ→≤ᵣ : ∀ x y → ((y <ᵣ x) → ⊥) → x ≤ᵣ y
≯ᵣ→≤ᵣ x y f = x<y+δ→x≤y _ _
  λ ε → PT.rec (isProp<ᵣ _ _)
      (⊎.rec (idfun _) (⊥.rec ∘ f))
      (Dichotomyℝ' y x (y +ᵣ rat (fst ε))
        (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
          (<ᵣ-o+ _ _ _ (snd (ℚ₊→ℝ₊ ε)))))


≤ᵣ≃≯ᵣ : ∀ x y → (x ≤ᵣ y) ≃ ((y <ᵣ x) → ⊥)
≤ᵣ≃≯ᵣ _ _ = propBiimpl→Equiv (isProp≤ᵣ _ _)
  (isPropΠ λ _ → isProp⊥)
  (≤ᵣ→≯ᵣ _ _) (≯ᵣ→≤ᵣ _ _)


isWeaklyLinear<ᵣ : BinaryRelation.isWeaklyLinear _<ᵣ_
isWeaklyLinear<ᵣ x y z x<y =
  PT.map (⊎.rec inr inl) (Dichotomyℝ' x z y x<y)


posSum→pos∨posᵣ : ∀ x y → 0 <ᵣ x +ᵣ y → (0 <ᵣ x) L.⊔′ (0 <ᵣ y)
posSum→pos∨posᵣ x y 0<x+y =
  PT.map (⊎.rec (inr ∘ x<x+y→0<y) inl)
    (Dichotomyℝ' 0 x (x +ᵣ y) 0<x+y)
  where
  x<x+y→0<y : x <ᵣ x +ᵣ y → 0 <ᵣ y
  x<x+y→0<y x<x+y =
    <-o+-cancel 0 y x
      (subst (_<ᵣ (x +ᵣ y)) (sym (+IdR x)) x<x+y)
