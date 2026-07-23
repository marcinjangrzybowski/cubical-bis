module Cubical.HITs.CauchyReals.Analysis.Metric.PNorm.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Embedding

open import Cubical.Data.Nat as ℕ hiding (_·_;_+_;_choose_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order using
  (^ⁿ-StrictMonotone)
open import Cubical.HITs.CauchyReals.Algebra.Inverse hiding (≤ᵣ-o·)
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication using
  (≤ᵣ-o·)
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open NonNegativeReals using (_+₀₊_ ; _·₀₊_ ; _^₀₊_)
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; _/2₊ ; min₊ ; ℚ! ; 0≤²)
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

nth-rootNonNegDist· : ∀ n x y →
 fst (nth-rootNonNeg n x) ·ᵣ fst (nth-rootNonNeg n y)
   ≡ fst (nth-rootNonNeg n (x ·₀₊ y))
nth-rootNonNegDist· (1+ n) x y = cong fst $
 sym (invEq≡→equivFun≡ (invEquiv (nth-pow-root-equiv₀₊ (1+ n)))
   {b = ((nth-rootNonNeg (1+ n)) x) ·₀₊ (nth-rootNonNeg (1+ n)) y}
  (ℝ₀₊≡ (^ⁿ-ldist-· _ _ (suc n)) ∙
   cong₂ _·₀₊_
     (Iso.sec (nth-pow-root-iso₀₊ (1+ n)) x)
     (Iso.sec (nth-pow-root-iso₀₊ (1+ n)) y)))


nth-rootNonNegMonotone : ∀ n x y
  → fst x ≤ᵣ fst y
  → fst (nth-rootNonNeg n x) ≤ᵣ fst (nth-rootNonNeg n y)
nth-rootNonNegMonotone (1+ n) (x , 0≤x) (y , 0≤y) x≤y =
  ≯ᵣ→≤ᵣ _ _
   λ √x<√y →
     ≤ᵣ→≯ᵣ x y x≤y
       (subst2 _<ᵣ_
        (cong fst (Iso.sec (nth-pow-root-iso₀₊ (1+ n)) (y , 0≤y)))
        (cong fst (Iso.sec (nth-pow-root-iso₀₊ (1+ n)) (x , 0≤x)))
         (^ⁿ-StrictMonotone (suc n) ℕ.zero-<-suc
          (nth-rootNonNeg (1+ n) (y , 0≤y) .snd)
          (nth-rootNonNeg (1+ n) (x , 0≤x) .snd) √x<√y))

nth-rootNonNegMonotoneStrict : ∀ n x y
  → fst x <ᵣ fst y
  → fst (nth-rootNonNeg n x) <ᵣ fst (nth-rootNonNeg n y)
nth-rootNonNegMonotoneStrict (1+ n) (x , 0≤x) (y , 0≤y) x<y =
  let (z , x<z , z<y) = denseℝ x y x<y
  in isTrans≤<ᵣ _ _ _
       (nth-rootNonNegMonotone (1+ n) (x , 0≤x)
         (z , <ᵣWeaken≤ᵣ _ _ (isTrans≤<ᵣ _ _ _ 0≤x x<z))
           (<ᵣWeaken≤ᵣ _ _ x<z))
         (subst2 _<ᵣ_
           (sym (snd (fst (snd (nth-rootNonNegDef (1+ n)))) _))
           (sym (snd (fst (snd (nth-rootNonNegDef (1+ n))))
             (y , isTrans≤<ᵣ _ _ _ 0≤x x<y))
            ∙ cong (fst ∘ (nth-rootNonNeg (1+ n)))
              (ℝ₀₊≡ refl))
           (ₙ√-StrictMonotone (1+ n) z<y))


[a+b]^ⁿ2≡[a^ⁿ2+b^ⁿ2]+2ab : ∀ a b →
 ((a +ᵣ b) ^ⁿ 2) ≡
  ((a ^ⁿ 2) +ᵣ (b ^ⁿ 2)) +ᵣ 2 ·ᵣ (a ·ᵣ b)
[a+b]^ⁿ2≡[a^ⁿ2+b^ⁿ2]+2ab _ _ = (x^²=x·x _ ∙ ℝ! ∙
                 cong₂ _+ᵣ_
                  (cong₂ _+ᵣ_ (sym (x^²=x·x _)) (sym (x^²=x·x _)))
                   (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x _))

𝒑-norm×-lem : ∀ n → ℕ₊₁→ℕ n ℕ.≤ 2 → ∀ ab bc a'b' b'c' →
   ((fst ab +ᵣ fst bc) ^ⁿ ℕ₊₁→ℕ n) +ᵣ
      ((fst a'b' +ᵣ fst b'c') ^ⁿ ℕ₊₁→ℕ n)
     ≤ᵣ ((fst (nth-rootNonNeg n ((ab ^₀₊ ℕ₊₁→ℕ n) +₀₊ (a'b' ^₀₊ ℕ₊₁→ℕ n)))
          +ᵣ fst (nth-rootNonNeg n
            ((bc ^₀₊ ℕ₊₁→ℕ n) +₀₊ (b'c' ^₀₊ ℕ₊₁→ℕ n)))) ^ⁿ ℕ₊₁→ℕ n)
𝒑-norm×-lem one x ab bc a'b' b'c' =
  ≡ᵣWeaken≤ᵣ _ _
   (  (cong₂ _+ᵣ_ (Rℝ.·IdR _) (Rℝ.·IdR _)
      ∙ ℝ! ∙ sym (Rℝ.·IdR _))
    ∙ cong (_^ⁿ 1)
      (cong₂ _+ᵣ_
        (cong₂ _+ᵣ_
            (sym (Rℝ.·IdR _))
            (sym (Rℝ.·IdR _))
             ∙ cong fst (sym (1st-rootNonNeg _)))
        (cong₂ _+ᵣ_
            (sym (Rℝ.·IdR _))
            (sym (Rℝ.·IdR _))
            ∙ cong fst (sym (1st-rootNonNeg _)))))
𝒑-norm×-lem (2+ zero) x ab bc a'b' b'c' =
  subst2 _≤ᵣ_
    (cong₂ _+ᵣ_
      (cong₂ _+ᵣ_
        (cong fst (Iso.sec (nth-pow-root-iso₀₊ 2) _))
        (cong fst (Iso.sec (nth-pow-root-iso₀₊ 2) _))
       ∙ Rℝ.+ShufflePairs _ _ _ _)
      (·DistL+ 2 _ _)
     ∙ Rℝ.+ShufflePairs _ _ _ _
     ∙ cong₂ _+ᵣ_ (sym ([a+b]^ⁿ2≡[a^ⁿ2+b^ⁿ2]+2ab _ _))
                (sym ([a+b]^ⁿ2≡[a^ⁿ2+b^ⁿ2]+2ab _ _)))
    (sym ([a+b]^ⁿ2≡[a^ⁿ2+b^ⁿ2]+2ab _ _))
    (≤ᵣ-o+ _ _ _ (≤ᵣ-o· _ _ 2 (ℚ.decℚ≤? {0} {2})
    (isTrans≤≡ᵣ _ _ _
      (isTrans≡≤ᵣ _ _ _
        (sym (cong fst (Iso.ret (nth-pow-root-iso₀₊ 2)
          ((ab ·₀₊ bc) +₀₊ (a'b' ·₀₊ b'c')))))
       (nth-rootNonNegMonotone 2 _ _
        (isTrans≡≤ᵣ _ _ _
         ([a+b]^ⁿ2≡[a^ⁿ2+b^ⁿ2]+2ab _ _ )
         (isTrans≤≡ᵣ _ _ _
           (≤ᵣ-o+ _ _ _
             (invEq (x≤y≃0≤y-x _ _)
              (isTrans≤≡ᵣ 0 (((ab .fst ·ᵣ b'c' .fst)
                           -ᵣ (a'b' .fst ·ᵣ bc .fst)) ^ⁿ 2) _
                (0≤ᵣx² _)
                (x^²=x·x _ ∙ ℝ! ∙
                 cong₂ _-ᵣ_
                  (cong₂ _+ᵣ_ (sym (x^²=x·x _)) (sym (x^²=x·x _)))
                   (Cubical.HITs.CauchyReals.Algebra.Multiplication.x+x≡2x _)))))
           (Rℝ.+ShufflePairs _ _ _ _ ∙  cong₂ _+ᵣ_
              (cong₂ _+ᵣ_
                (^ⁿ-ldist-· _ _ 2)
                (^ⁿ-ldist-· _ _ 2))
              (+ᵣComm _ _ ∙ cong₂ _+ᵣ_
                (^ⁿ-ldist-· _ _ 2)
                (^ⁿ-ldist-· _ _ 2))
           ∙ cong₂ _+ᵣ_ (sym (·DistL+ _ _ _)) (sym (·DistL+ _ _ _))
           ∙ (sym (·DistR+ _ _ _)))))))
      (sym (nth-rootNonNegDist· 2 _ _) ))))
𝒑-norm×-lem (2+ suc n) x ab bc a'b' b'c' =
  ⊥.rec (ℕ.<-asym x (ℕ.≤-k+ {k = 2} ℕ.zero-≤))

0≡ℝ₀₊+ℝ₀₊→both≡0 : ∀ (x y : ℝ₀₊)
   → 0 ≡ fst (x +₀₊ y)
   → (0 ≡ fst x) × (0 ≡ fst y)
0≡ℝ₀₊+ℝ₀₊→both≡0 x y 0≡x+y =
    isAntisym≤ᵣ 0 (fst x) (snd x)
      ((isTrans≡≤ᵣ _ _ _ (Rℝ.implicitInverse _ _ (+ᵣComm _ _ ∙ sym 0≡x+y))
       (isTrans≤≡ᵣ _ _ _  (-ᵣ≤ᵣ _ _ (snd y)) (-ᵣ-rat 0))))
  , isAntisym≤ᵣ 0 (fst y) (snd y)
     (isTrans≡≤ᵣ _ _ _ (Rℝ.implicitInverse _ _ (sym 0≡x+y))
       (isTrans≤≡ᵣ _ _ _  (-ᵣ≤ᵣ _ _ (snd x)) (-ᵣ-rat 0)))

0<ℝ₀₊+ℝ₀₊→atLeastOne>0 : ∀ (x y : ℝ₀₊)
   → 0 <ᵣ fst (x +₀₊ y)
   → ∥ (0 <ᵣ fst x) ⊎ (0 <ᵣ fst y) ∥₁
0<ℝ₀₊+ℝ₀₊→atLeastOne>0 (x , 0≤x) (y , 0≤y) 0<x+y =
  PT.map w (Dichotomyℝ' _ x _ 0<x+y)
 where
 w : (x <ᵣ fst ((x , 0≤x) +₀₊ (y , 0≤y))) ⊎ (0 <ᵣ x)
    → (0 <ᵣ x) ⊎ (0 <ᵣ y)
 w (inl x<x+y) = inr
   (Cubical.HITs.CauchyReals.Algebra.Inverse.<-o+-cancel _ _ x
     (isTrans≡<ᵣ _ _ _ (+IdR _) x<x+y))
 w (inr 0<x) = inl 0<x
