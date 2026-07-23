module Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Unit
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base


opaque
 unfolding _≤ᵣ_ absᵣ
 absᵣ-triangle : (x y : ℝ) → absᵣ (x +ᵣ y) ≤ᵣ (absᵣ x +ᵣ absᵣ y)
 absᵣ-triangle x y =
  let z = IsContinuous∘ _ _ (IsContinuous+ᵣR (absᵣ y)) IsContinuousAbsᵣ

  in ≡Continuous
     (λ x → maxᵣ (absᵣ (x +ᵣ y)) ((absᵣ x +ᵣ absᵣ y)))
     (λ x → (absᵣ x +ᵣ absᵣ y))
     (cont₂maxᵣ _ _
       (IsContinuous∘ _ _ IsContinuousAbsᵣ (IsContinuous+ᵣR y)) z)
     z
     (λ r → let z' = IsContinuous∘ _ _ (IsContinuous+ᵣL (absᵣ (rat r)))
                 IsContinuousAbsᵣ
      in ≡Continuous
     (λ y → maxᵣ (absᵣ ((rat r) +ᵣ y)) ((absᵣ (rat r) +ᵣ absᵣ y)))
     (λ y → (absᵣ (rat r) +ᵣ absᵣ y))
     (cont₂maxᵣ _ _
         ((IsContinuous∘ _ _ IsContinuousAbsᵣ (IsContinuous+ᵣL (rat r))))
           z') z'
     (λ r' → cong rat (ℚ.≤→max _ _
               (subst2 ℚ._≤_ (ℚ.abs'≡abs (r ℚ.+ r'))
                 (cong₂ ℚ._+_ (ℚ.abs'≡abs r) (ℚ.abs'≡abs r'))
                (triangularInequality r r')))) y) x


absᵣ-triangle'' : (x y : ℝ) → absᵣ (x -ᵣ y) ≤ᵣ (absᵣ x +ᵣ absᵣ y)
absᵣ-triangle'' x y =
  isTrans≤≡ᵣ _ _ _ (absᵣ-triangle _ _)
    (cong (absᵣ x +ᵣ_) (sym (-absᵣ y)))


opaque
 unfolding _≤ᵣ_ absᵣ
 abs-max : ∀ x → absᵣ x ≡ maxᵣ x (-ᵣ x)
 abs-max = ≡Continuous _ _
   IsContinuousAbsᵣ
    (cont₂maxᵣ _ _ IsContinuousId IsContinuous-ᵣ)
     λ r → cong rat (sym (ℚ.abs'≡abs r))


ℚabs-min-max : ∀ u v →
      abs (ℚ.max u v ℚ.- ℚ.min u v) ≡ abs (u ℚ.- v)
ℚabs-min-max = ℚ.elimBy≤
  (λ x y X →
    (cong abs (cong₂ ℚ._-_ (ℚ.maxComm y x) (ℚ.minComm y x))
       ∙∙ X ∙∙
      abs-Comm x y))
  λ x y x≤y →
    cong abs
      (cong₂ ℚ._-_
        (ℚ.≤→max _ _ x≤y) (ℚ.≤→min _ _ x≤y))
     ∙ abs-Comm y x


opaque
 unfolding absᵣ
 absᵣ-min-max : ∀ u v →
       absᵣ (maxᵣ u v -ᵣ minᵣ u v) ≡ absᵣ (u -ᵣ v)
 absᵣ-min-max =
  ≡Cont₂
    (cont∘₂ IsContinuousAbsᵣ
     (contNE₂∘ sumR
       (contNE₂ maxR)
       (cont∘₂ IsContinuous-ᵣ (contNE₂ minR))))
    (cont∘₂ IsContinuousAbsᵣ
     (cont₂∘ (contNE₂ sumR)
       IsContinuousId IsContinuous-ᵣ))
    λ u v →
       cong rat (sym (ℚ.abs'≡abs (ℚ.max u v ℚ.- ℚ.min u v))
         ∙∙ ℚabs-min-max u v ∙∙
         ℚ.abs'≡abs (u ℚ.- v))


opaque

 absᵣNonNeg : ∀ x → 0 ≤ᵣ x → absᵣ x ≡ x
 absᵣNonNeg x p = abs-max x ∙∙ maxᵣComm x (-ᵣ x) ∙∙ ≤ᵣ→≡ z
  where
    z : (-ᵣ x) ≤ᵣ x
    z = subst2 _≤ᵣ_
      (+IdL (-ᵣ x))
      (sym (+ᵣAssoc _ _ _) ∙∙ cong (x +ᵣ_) (+-ᵣ x) ∙∙ +IdR x)
      (≤ᵣ-+o 0 (x +ᵣ x) (-ᵣ x)
       (isTrans≡≤ᵣ _ _ _ (sym (+ᵣ-rat 0 0))
         (≤ᵣMonotone+ᵣ 0 x 0 x p p)))


 absᵣ-monotoneOnNonNeg : (x y : ℝ₀₊) →
   fst x ≤ᵣ fst y → absᵣ (fst x) ≤ᵣ absᵣ (fst y)
 absᵣ-monotoneOnNonNeg x y x≤y =
   subst2 _≤ᵣ_
     (sym (absᵣNonNeg (fst x) (snd x)))
     (sym (absᵣNonNeg (fst y) (snd y)))
     x≤y


 absᵣPos : ∀ x → 0 <ᵣ x → absᵣ x ≡ x
 absᵣPos x = absᵣNonNeg x ∘ <ᵣWeaken≤ᵣ _ _


 absᵣ≡0→≡0 : ∀ x → absᵣ x ≡ 0 → x ≡ 0
 absᵣ≡0→≡0 x ∣x∣≡0 =
   invEq (eqℝ≃< x 0) λ ε →
     isTrans≡<ᵣ _ _ _
       (cong absᵣ (cong (x +ᵣ_) (-ᵣ-rat 0) ∙ +IdR x) ∙ ∣x∣≡0)
       (snd (ℚ₊→ℝ₊ ε))


absᵣx=0→x=0 : ∀ x → absᵣ x ≡ 0 → x ≡ 0
absᵣx=0→x=0 = absᵣ≡0→≡0


absᵣ-triangle' : (x y : ℝ) →
  absᵣ x ≤ᵣ absᵣ (x -ᵣ y) +ᵣ absᵣ y
absᵣ-triangle' x y =
  isTrans≡≤ᵣ _ _ _
    (cong absᵣ
      (sym
        (sym (+ᵣAssoc x (-ᵣ y) y)
          ∙ cong (x +ᵣ_) (+ᵣComm (-ᵣ y) y ∙ +-ᵣ y)
          ∙ +IdR x)))
    (absᵣ-triangle (x -ᵣ y) y)


absᵣ-triangle-minus : (x y : ℝ) →
  absᵣ x -ᵣ absᵣ y ≤ᵣ absᵣ (x -ᵣ y)
absᵣ-triangle-minus x y =
  isTrans≤≡ᵣ _ _ _
    (≤ᵣ-+o _ _ (-ᵣ (absᵣ y)) (absᵣ-triangle' x y))
    (sym (+ᵣAssoc (absᵣ (x -ᵣ y)) (absᵣ y) (-ᵣ (absᵣ y)))
      ∙ cong (absᵣ (x -ᵣ y) +ᵣ_) (+-ᵣ (absᵣ y))
      ∙ +IdR (absᵣ (x -ᵣ y)))


absᵣNonPos : ∀ (x : ℝ) → x ≤ᵣ 0 → absᵣ x ≡ -ᵣ x
absᵣNonPos x p = abs-max x ∙ ≤ᵣ→≡ z
  where
  z : x ≤ᵣ -ᵣ x
  z = isTrans≤ᵣ _ _ _ p
    (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat _)) (-ᵣ≤ᵣ _ _ p))


opaque
  unfolding _<ᵣ_ absᵣ -ᵣ_

  absᵣNeg : ∀ (x : ℝ) → x <ᵣ 0 → absᵣ x ≡ -ᵣ x
  absᵣNeg x x<0 = -absᵣ x ∙ absᵣPos _ (-ᵣ<ᵣ x _ x<0)
