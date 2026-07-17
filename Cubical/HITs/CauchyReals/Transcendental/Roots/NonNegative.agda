module Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (seqΣ ; seqΣ' ; _^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using (invℚ ; _⁻¹₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base hiding (invℚ₊ ; _ℚ^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0<)
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Analysis.Uniform using
  ( IsUContinuousℙ-ᵣ∘
  ; IsUContinuousℙ→pointwise
  ; IsUContinuousℙ→pointwiseℙ
  ; IsUContinuousMaxᵣ
  ; IsUCauchyFSequence
  ; IsUContFSequence
  ; FSeq
  ; fromUCauchyFSequence
  ; isCauchyFSequenceAt
  ; fromCauchySequence'₁≡fromUCauchyFSequence
  ; fromCauchySequence'-at≡fromUCauchyFSequence
  ; maxᵣ-dist
  ; DichotomyRec
  ; byDichotomyMax
  )

open import Cubical.HITs.CauchyReals.Analysis.Continuity.EndpointExtension using (extendℝFnLeft)

opaque
 nth-rootNonNegDef : ∀ (n : ℕ₊₁) → Σ (Σ ℝ (0 ≤ᵣ_) → Σ ℝ (0 ≤ᵣ_))
                                 (λ f' →
                                    ((fst (f' (0 , ≤ᵣ-refl 0)) ≡ 0) ×
                                     ((x : Σ ℝ (0 <ᵣ_)) →
                                      fst (f' (x .fst , <ᵣWeaken≤ᵣ 0 (x .fst) (snd x))) ≡
                                      root (1+ n .ℕ₊₁.n) (x .fst , x .snd) .fst))
                                    × IsUContinuousℙ (pred≥ 0) (curry ((λ r → fst r) ∘ f')))
 nth-rootNonNegDef n@(1+ n') = extendℝFnLeft 0 0
   (λ x → root n x)
    (λ ε → (ℚ._ℚ₊^ⁿ_ ε (suc n')) ,
      λ r r∈ x＃r x →
        isTrans<≡ᵣ _ _ _
         (isTrans≡<ᵣ _ _ _
           ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ (snd (root (1+ n .ℕ₊₁.n) (r , r∈))))
           (ₙ√-StrictMonotone n (subst2 _<ᵣ_
            ((cong absᵣ (+IdL _) ∙ sym (-absᵣ _)) ∙ absᵣPos _ r∈)
            (sym (cong fst (^ℤ-rat ε (pos (suc n')))))
            x)))
           (cong fst (Iso.ret (nth-pow-root-iso n)
            (ℚ₊→ℝ₊ ε))) )
    (uContRoot n) λ x y x≤y → ₙ√-Monotone {x = x} {y = y} n x≤y


nth-rootNonNeg : ℕ₊₁ → Σ ℝ (0 ≤ᵣ_) → Σ ℝ (0 ≤ᵣ_)
nth-rootNonNeg n = fst (nth-rootNonNegDef n)

nth-rootNonNeg0 : (n : ℕ₊₁) (p : 0 ≤ᵣ 0) → 0 ≡ fst (nth-rootNonNeg n (0 , p))
nth-rootNonNeg0 n p = sym (fst (fst (snd (nth-rootNonNegDef n))))
  ∙ cong (λ p → fst (nth-rootNonNeg n (0 , p)))
   (isProp≤ᵣ 0 0 (≤ᵣ-refl 0) p)

_₀₊^ⁿ_ : ℝ₀₊ → ℕ → ℝ₀₊
_₀₊^ⁿ_ = NonNegativeReals._^₀₊_

max-rat₀₊ : (q : ℚ) →
  (maxᵣ 0 (rat q) , ≤maxᵣ 0 (rat q)) ≡
  (rat (ℚ.max 0 q) , ≤ℚ→≤ᵣ 0 (ℚ.max 0 q) (ℚ.≤max 0 q))
max-rat₀₊ q = ℝ₀₊≡ (maxᵣ-rat 0 q)


nth-pow-root-iso₀₊ : ℕ₊₁ → Iso ℝ₀₊ ℝ₀₊
nth-pow-root-iso₀₊ n .Iso.fun = λ x → x ₀₊^ⁿ (ℕ₊₁→ℕ n)
nth-pow-root-iso₀₊ n .Iso.inv = (nth-rootNonNeg n)
nth-pow-root-iso₀₊ n .Iso.sec (x , 0≤x) = ww
 where
 opaque
  unfolding maxᵣ minᵣ
  ww : ((nth-rootNonNeg n (x , 0≤x)) ₀₊^ⁿ (ℕ₊₁→ℕ n)) ≡ (x , 0≤x)
  ww =
   ℝ₀₊≡
       (cong ((_^ⁿ (ℕ₊₁→ℕ n)) ∘ fst ∘  (nth-rootNonNeg n))
         (ℝ₀₊≡ (sym (≤→maxᵣ 0 x 0≤x)))
          ∙∙ ≡Continuous
              (λ x →
                ((_^ⁿ (ℕ₊₁→ℕ n)) ∘ fst ∘  (nth-rootNonNeg n))
                 (maxᵣ 0 x , ≤maxᵣ 0 x))
              (maxᵣ 0)
             (IsContinuous∘
               (_^ⁿ (ℕ₊₁→ℕ n))
               (λ x → fst (nth-rootNonNeg n (maxᵣ 0 x , ≤maxᵣ 0 x)))
               (IsContinuous^ⁿ (ℕ₊₁→ℕ n))
                (IsContinuousWithPred∘IsContinuous
                 (pred≥ 0)
                 (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))

                  (maxᵣ 0)
                   (λ x → ≤maxᵣ 0 x)
                   (IsUContinuousℙ→pointwiseℙ (pred≥ 0)
                     (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))
                     (snd (snd (nth-rootNonNegDef n))))
                   (IsContinuousMaxL 0)))
             (IsContinuousMaxL 0)
            (λ q → subst
              (λ z → (fst (nth-rootNonNeg n z) ^ⁿ (ℕ₊₁→ℕ n)) ≡ fst z)
              (sym (max-rat₀₊ q))
              (byDichotomyMax 0
                {λ r r∈ → (fst (nth-rootNonNeg n (rat r , r∈)) ^ⁿ (ℕ₊₁→ℕ n))
                    ≡ rat r } w q (≤ℚ→≤ᵣ 0 (ℚ.max 0 q) (ℚ.≤max 0 q)))) x ∙∙
         ≤→maxᵣ 0 x 0≤x)
    where
    w : DichotomyRec {ℓ = ℓ-zero} 0 λ m ≤m →
         (fst (nth-rootNonNeg n (rat m , ≤m)) ^ⁿ ℕ₊₁→ℕ n) ≡ rat m
    w .DichotomyRec.eq-case =
      cong (_^ⁿ suc (n .ℕ₊₁.n))
       (fst (fst (snd (nth-rootNonNegDef n))))
      ∙ 0^ⁿ (n .ℕ₊₁.n)
    w .DichotomyRec.gt-case m m>0 =
     cong (_^ⁿ suc (n .ℕ₊₁.n))
       (snd (fst (snd (nth-rootNonNegDef n))) (rat m , m>0))
      ∙ cong fst  (nth-pow-root-iso n .Iso.sec
        (rat m , m>0))

nth-pow-root-iso₀₊ n .Iso.ret (x , 0≤x) = ww
 where
 pow₀₊ : ℝ₀₊ → ℝ₀₊
 pow₀₊ z = z ₀₊^ⁿ (ℕ₊₁→ℕ n)

 opaque
  unfolding maxᵣ
  ww : ((nth-rootNonNeg n ((x , 0≤x)  ₀₊^ⁿ (ℕ₊₁→ℕ n)))) ≡ (x , 0≤x)
  ww = (cong ((nth-rootNonNeg n) ∘ pow₀₊)
        (sym (ℝ₀₊≡ (≤→maxᵣ 0 x 0≤x))) ∙
        ℝ₀₊≡ (≡Continuous
            (λ x →
              (fst (nth-rootNonNeg n
                (pow₀₊ (maxᵣ 0 x , ≤maxᵣ 0 x))))
               )
            (maxᵣ 0)
            (IsContinuousWithPred∘IsContinuous (pred≥ 0)
             (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))
             (λ x → fst (pow₀₊ (maxᵣ 0 x , ≤maxᵣ 0 x)))
             (λ x → snd (pow₀₊ (maxᵣ 0 x , ≤maxᵣ 0 x)))
             (IsUContinuousℙ→pointwiseℙ (pred≥ 0)
               (λ x x∈ → fst (nth-rootNonNeg n (x , x∈)))
                   (snd (snd (nth-rootNonNegDef n))))
             (IsContinuous∘
              (_^ⁿ (ℕ₊₁→ℕ n))
              (maxᵣ 0)
              (IsContinuous^ⁿ (ℕ₊₁→ℕ n))
              (IsContinuousMaxL 0))
              )
            (IsContinuousMaxL 0)
            (λ q → subst
              (λ z → fst (nth-rootNonNeg n (pow₀₊ z)) ≡ fst z)
              (sym (max-rat₀₊ q))
              (byDichotomyMax 0
              {λ r r∈ →
                 fst (nth-rootNonNeg n (pow₀₊ (rat r , r∈))) ≡ rat r }
              w q (≤ℚ→≤ᵣ 0 (ℚ.max 0 q) (ℚ.≤max 0 q))))
            x
        ∙
        (≤→maxᵣ 0 x 0≤x)))
   where
   w : DichotomyRec {ℓ = ℓ-zero} 0 λ m ≤m →
         fst (nth-rootNonNeg n (pow₀₊ (rat m , ≤m))) ≡ rat m
   w .DichotomyRec.eq-case =
       cong (fst ∘ nth-rootNonNeg n)
         (ℝ₀₊≡
          {x = pow₀₊ (0 , ≤ᵣ-refl 0)}
          {y = (0 , ≤ᵣ-refl 0)}
          (0^ⁿ (n .ℕ₊₁.n)))
     ∙ fst (fst (snd (nth-rootNonNegDef n)))
   w .DichotomyRec.gt-case m m>0 =
     let mⁿ = rat m ^ⁿ (ℕ₊₁→ℕ n)
         0<mⁿ : 0 <ᵣ mⁿ
         0<mⁿ = 0<x^ⁿ (rat m) (ℕ₊₁→ℕ n) m>0
     in (cong (fst ∘ nth-rootNonNeg n)
       (ℝ₀₊≡
        {x = pow₀₊ (rat m , <ᵣWeaken≤ᵣ 0 (rat m) m>0)}
        {y = (mⁿ , <ᵣWeaken≤ᵣ 0 mⁿ 0<mⁿ)}
        refl)
    ∙ (snd (fst (snd (nth-rootNonNegDef n))) (mⁿ , 0<mⁿ)))
    ∙ cong (fst ∘ root n)
       (ℝ₊≡
        {x = (mⁿ , 0<mⁿ)}
        {y = (rat m , m>0) ₊^ⁿ (ℕ₊₁→ℕ n)}
        refl)
    ∙ cong fst  (nth-pow-root-iso n .Iso.ret
       (rat m , m>0))


nth-pow-root-equiv₀₊ : ℕ₊₁ → ℝ₀₊ ≃ ℝ₀₊
nth-pow-root-equiv₀₊ n = isoToEquiv (nth-pow-root-iso₀₊ n)

1st-rootNonNeg : (x : ℝ₀₊) → nth-rootNonNeg 1 x ≡ x
1st-rootNonNeg x@(r , 0≤r) =
  cong (nth-rootNonNeg 1) (sym (ℝ₀₊≡ (·IdR r)))
    ∙ Iso.ret (nth-pow-root-iso₀₊ 1) x
