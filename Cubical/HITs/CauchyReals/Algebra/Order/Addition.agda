module Cubical.HITs.CauchyReals.Algebra.Order.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


<ᵣMonotone+ᵣ : ∀ m n o s → m <ᵣ n → o <ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
<ᵣMonotone+ᵣ m n o s m<n o<s =
  isTrans<ᵣ _ _ _ (<ᵣ-+o m n o m<n) (<ᵣ-o+ o s n o<s)

≤<ᵣMonotone+ᵣ : ∀ m n o s → m ≤ᵣ n → o <ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
≤<ᵣMonotone+ᵣ m n o s m≤n o<s =
  isTrans≤<ᵣ _ _ _ (≤ᵣ-+o m n o m≤n) (<ᵣ-o+ o s n o<s)

<≤ᵣMonotone+ᵣ : ∀ m n o s → m <ᵣ n → o ≤ᵣ s → (m +ᵣ o) <ᵣ (n +ᵣ s)
<≤ᵣMonotone+ᵣ m n o s m<n o≤s =
  isTrans<≤ᵣ _ _ _ (<ᵣ-+o m n o m<n) (≤ᵣ-o+ o s n o≤s)


ℝ₊+ : (m : ℝ₊) (n : ℝ₊) → 0 <ᵣ fst m +ᵣ fst n
ℝ₊+ (m , 0<m) (n , 0<n) =
  isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
    (<ᵣMonotone+ᵣ 0 m 0 n 0<m 0<n)


a<c+b⇒a-c<b : ∀ a b c → a <ᵣ c +ᵣ b → a -ᵣ c <ᵣ b
a<c+b⇒a-c<b a b c p =
  subst ((a -ᵣ c) <ᵣ_) ℝ! (<ᵣ-+o _ _ (-ᵣ c) p)


<-o+-cancel : ∀ m n o → o +ᵣ m <ᵣ o +ᵣ n → m <ᵣ n
<-o+-cancel m n o p =
  subst2 _<ᵣ_ ℝ! ℝ! (<ᵣ-o+ _ _ (-ᵣ o) p)


0<y-x→x<y : ∀ x y → 0 <ᵣ y -ᵣ x → x <ᵣ y
0<y-x→x<y x y p =
  subst2 _<ᵣ_ (+IdL x) ℝ! (<ᵣ-+o 0 (y -ᵣ x) x p)


x≤y≃0≤y-x : ∀ x y → (x ≤ᵣ y) ≃ (0 ≤ᵣ y -ᵣ x)
x≤y≃0≤y-x x y =
  propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
    (λ p → subst (_≤ᵣ (y -ᵣ x)) (+-ᵣ x) (≤ᵣ-+o x y (-ᵣ x) p))
    λ p → subst2 _≤ᵣ_ (+IdL x) ℝ!
      (≤ᵣ-+o 0 (y -ᵣ x) x p)
