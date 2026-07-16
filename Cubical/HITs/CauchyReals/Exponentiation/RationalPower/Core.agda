module Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( 0<_ )
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ; x·invℚ[x]; x<y·z→x/y<z)

import Cubical.Algebra.OrderedCommRing.Properties as OCRP
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using (ℚOrderedCommRing)

private
  module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Exponentiation.Approximation.Base
  using (ℚApproxℙ''→ℚApproxℙ')

posℙ : ℙ ℝ
posℙ = pred> 0

-- Previous location: IsContinuousWithPred-invℝ₊ now lives in Inverse.

IsContinuous₊^ⁿ : ∀ n → IsContinuousWithPred
         posℙ
         λ x 0<x →  fst ((x , 0<x) ₊^ⁿ n)
IsContinuous₊^ⁿ zero =
 AsContinuousWithPred posℙ (λ _ → 1) (IsContinuousConst 1)
IsContinuous₊^ⁿ (suc n) =
 cont₂·ᵣWP posℙ (λ x _ → x) (λ x 0<x → fst ((x , 0<x) ₊^ⁿ n))
   (AsContinuousWithPred posℙ (λ x → x) IsContinuousId)
   (IsContinuous₊^ⁿ n)


^ℕ-+ : ∀ x a b → ((x ₊^ⁿ a) ₊·ᵣ (x ₊^ⁿ b)) ≡ (x ₊^ⁿ (a ℕ.+ b))
^ℕ-+ x a b =
  ℝ₊≡ (Exponentiationᵣ.·-of-^-is-^-of-+ (fst x) a b)

_^ℤ_ : ℝ₊ → ℤ → ℝ₊
x ^ℤ pos n = x ₊^ⁿ n
x ^ℤ ℤ.negsuc n = invℝ₊ (x ₊^ⁿ (suc n))


_ℚ^ℤ_ : ℚ₊ → ℤ → ℚ₊
x ℚ^ℤ pos n = (fst x ℚ^ⁿ n) , ℚ.0<ℚ^ⁿ (fst x) (snd x) n
x ℚ^ℤ ℤ.negsuc n = invℚ₊ ((fst x ℚ^ⁿ suc n) , ℚ.0<ℚ^ⁿ (fst x) (snd x) (suc n))




^ℤ-rat : ∀ q n → ((ℚ₊→ℝ₊ q) ^ℤ n) ≡ ℚ₊→ℝ₊ (q ℚ^ℤ n)
^ℤ-rat q (pos n) = ℝ₊≡ (^ⁿ-ℚ^ⁿ n (q .fst))
^ℤ-rat q (ℤ.negsuc n) =
  ℝ₊≡
    (cong (fst ∘ invℝ₊) (ℝ₊≡ (^ⁿ-ℚ^ⁿ (suc n) (q .fst)))
    ∙ invℝ₊-rat ((q .fst ℚ^ⁿ suc n) ,
        ℚ.0<ℚ^ⁿ (fst q) (snd q) (suc n)))

^ℤ-ℚApproxℙ'' : ∀ n → ℚApproxℙ''
      (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , isProp<ᵣ _ _)
      (λ x → (rat [ pos 0 / 1+ 0 ] <ᵣ x) , isProp<ᵣ _ _)
      (curry (λ p → ((p .fst , p .snd) ^ℤ n)))
^ℤ-ℚApproxℙ'' n x x∈P ε =
  fst (q₊ ℚ^ℤ n) , snd (ℚ₊→ℝ₊ (q₊ ℚ^ℤ n)) ,
    ≡→∼ (cong fst (sym (^ℤ-rat q₊ n)) ∙
         cong (curry (λ p → (p ^ℤ n) .fst) (rat x))
             (isProp<ᵣ _ _ _ _))

 where
  q₊ : ℚ₊
  q₊ = (x , <ᵣ→<ℚ _ _ x∈P)

IsContinuous^ℤ : ∀ n → IsContinuousWithPred
         posℙ
         λ x 0<x →  fst ((x , 0<x) ^ℤ n)
IsContinuous^ℤ (pos n) = IsContinuous₊^ⁿ n
IsContinuous^ℤ (ℤ.negsuc n) =
  subst (IsContinuousWithPred posℙ)
    (funExt λ x → funExt λ 0<x →
      sym (cong fst (invℝ₊-impl ((x , 0<x) ₊^ⁿ (suc n)))))
    (IsContinuousWP∘ posℙ posℙ (fst invℝ') (λ x 0<x → fst ((x , 0<x) ₊^ⁿ (suc n)))
      (λ x 0<x → snd ((x , 0<x) ₊^ⁿ (suc n)))
      (snd invℝ') (IsContinuous₊^ⁿ (suc n)))


-- TODO : more direct!! (invℝ₊ is more basic than invℝ)

₊^ⁿ-invℝ₊ : ∀ n x  →
            ((invℝ₊ x) ₊^ⁿ n) ≡ (invℝ₊ (x ₊^ⁿ n))
₊^ⁿ-invℝ₊ n x =
    ℝ₊≡ (cong (_^ⁿ n) (invℝ₊≡invℝ _ (inl (snd x))) ∙∙
       ^ⁿ-invℝ n (x .fst) (inl (snd x))  _
       ∙∙ sym (invℝ₊≡invℝ (x .fst ^ⁿ n , 0<x^ⁿ (x .fst) n (x .snd)) (inl (snd (x ₊^ⁿ n)))) )

1₊^ⁿ≡1 : ∀ k → 1 ₊^ⁿ k ≡ 1
1₊^ⁿ≡1 k = ℝ₊≡ (Exponentiationᵣ.1ⁿ≡1 k)

1^ℤ≡1 : ∀ k → 1 ^ℤ k ≡ 1
1^ℤ≡1 (pos n) = 1₊^ⁿ≡1 n
1^ℤ≡1 (ℤ.negsuc n) =
     cong invℝ₊ (1₊^ⁿ≡1 (suc n))
   ∙ invℝ₊1


pos-suc+negsuc0 : ∀ a → pos a ≡ pos (suc a) ℤ.+ ℤ.negsuc 0
pos-suc+negsuc0 zero = refl
pos-suc+negsuc0 (suc a) = refl

pos+negsuc : ∀ a b → pos a ℤ.+ ℤ.negsuc b ≡ pos (suc a) ℤ.+ ℤ.negsuc (suc b)
pos+negsuc a b = ℤ.+Comm (pos a) (ℤ.negsuc b) ∙∙
   cong (ℤ.negsuc b ℤ.+_)
     (pos-suc+negsuc0 a ∙ ℤ.+Comm (pos (suc a)) (ℤ.negsuc 0))
     ∙ ℤ.+Assoc (ℤ.negsuc b) (ℤ.negsuc 0) (pos (suc a))
     ∙∙ ℤ.+Comm (ℤ.negsuc b ℤ.+ ℤ.negsuc 0) (pos (suc a))
      ∙ cong (pos (suc a) ℤ.+_) (cong (ℤ.negsuc ∘ suc) (ℕ.+-zero b))

^ℤ-minus : ∀ x a b → ((x ^ℤ (pos a)) ₊·ᵣ (x ^ℤ (ℤ.negsuc b)))
                   ≡ (x ^ℤ ((pos a) ℤ.+ (ℤ.negsuc b)))
^ℤ-minus x zero b =
    ℝ₊≡ (·IdLᵣ _)
  ∙ cong {x = ℤ.negsuc b} (x ^ℤ_) (ℤ.pos0+ _)
^ℤ-minus x (suc a) zero =
  ℝ₊≡
    (cong (fst (x ₊^ⁿ suc a) ·ᵣ_)
      (cong (fst ∘ invℝ₊) (ℝ₊≡ (·IdR _)))
    ∙ sym (·ᵣAssoc _ _ _)
    ∙ cong (fst x ·ᵣ_) (·ᵣComm _ _)
    ∙ ·ᵣAssoc _ _ _
    ∙ cong (_·ᵣ fst (x ₊^ⁿ a)) (x·invℝ₊[x] x)
    ∙ ·IdLᵣ _)
  ∙ cong (x ^ℤ_) (pos-suc+negsuc0 a)
^ℤ-minus x (suc a) (suc b) =
  let z = ^ℤ-minus x a b
  in ℝ₊≡
       (sym (·ᵣAssoc _ _ _)
       ∙ cong (fst x ·ᵣ_)
           (cong (fst (x ₊^ⁿ a) ·ᵣ_)
             (cong fst (invℝ₊· x (x ₊^ⁿ suc b))))
       ∙ cong (fst x ·ᵣ_)
           (·ᵣAssoc _ _ _
           ∙ cong (_·ᵣ fst (invℝ₊ (x ₊^ⁿ suc b))) (·ᵣComm _ _)
           ∙ sym (·ᵣAssoc _ _ _))
       ∙ ·ᵣAssoc _ _ _
       ∙ cong (_·ᵣ (fst (x ₊^ⁿ a) ·ᵣ fst (invℝ₊ (x ₊^ⁿ suc b))))
           (x·invℝ₊[x] x)
       ∙ ·IdLᵣ _)
       ∙∙ z ∙∙
     cong (x ^ℤ_) (pos+negsuc a b)

^ℤ-+ : ∀ x a b → ((x ^ℤ a) ₊·ᵣ (x ^ℤ b)) ≡ (x ^ℤ (a ℤ.+ b))
^ℤ-+ x (pos n) (pos n₁) = ^ℕ-+ x n n₁ ∙ cong (x ^ℤ_) (ℤ.pos+ n n₁)
^ℤ-+ x (pos n) (ℤ.negsuc n₁) = ^ℤ-minus x n n₁
^ℤ-+ x (ℤ.negsuc n) (pos n₁) =
  ℝ₊≡ (·ᵣComm _ _)
  ∙∙ ^ℤ-minus x n₁ n ∙∙
  cong (x ^ℤ_) (ℤ.+Comm (pos n₁) (ℤ.negsuc n))
^ℤ-+ x (ℤ.negsuc n) (ℤ.negsuc n₁) =
      sym (invℝ₊· _ _)
   ∙∙ cong invℝ₊ (^ℕ-+ x (suc n) (suc n₁))
   ∙∙ cong (x ^ℤ_) (ℤ.negsuc+ n (suc n₁))


^ℕ-· : ∀ x a b → ((x ₊^ⁿ a) ₊^ⁿ b) ≡ (x ₊^ⁿ (a ℕ.· b))
^ℕ-· x a b =
  ℝ₊≡ (sym (Exponentiationᵣ.^-rdist-·ℕ (fst x) a b))


pow-root-+ℕ₊₁ : ∀ (m n : ℕ₊₁) →
         nth-pow-root-iso (m ·₊₁ n)
             ≡ compIso (nth-pow-root-iso m) (nth-pow-root-iso n)
pow-root-+ℕ₊₁ (1+ m) (1+ n) = SetsIso≡fun isSetℝ₊ isSetℝ₊
  (funExt (λ x → sym (^ℕ-· x (suc m) (suc n))))


ₙ√1 : ∀ b → root b 1 ≡ 1
ₙ√1 b = cong (root b) (sym (1₊^ⁿ≡1 (ℕ₊₁→ℕ b))) ∙ Iso.ret (nth-pow-root-iso b) 1



ₙ√-StrictMonotone : ∀ {x y : ℝ₊} (b : ℕ₊₁)
      → fst x <ᵣ fst y → fst (root b x) <ᵣ fst (root b y)
ₙ√-StrictMonotone {x = x} {y = y} (1+ b) x<y =
  ^ⁿStrictMonotone⁻¹  (suc b) (ℕ.suc-≤-suc  ℕ.zero-≤)
    (snd (root (1+ b) x))
    (snd (root (1+ b) y))
    (subst2 _<ᵣ_
      (cong fst $ sym (Iso.sec (nth-pow-root-iso (1+ b)) x))
      (cong fst $ sym (Iso.sec (nth-pow-root-iso (1+ b)) y))
      x<y)


ₙ√-Monotone : ∀ {x y : ℝ₊} (b : ℕ₊₁)
      → fst x ≤ᵣ fst y → fst (root b x) ≤ᵣ fst (root b y)
ₙ√-Monotone {x = x} {y = y} (1+ b) x≤y =
  ^ⁿMonotone⁻¹  (suc b) (ℕ.suc-≤-suc  ℕ.zero-≤)
    (snd (root (1+ b) x))
    (snd (root (1+ b) y))
    (subst2 _≤ᵣ_
      (cong fst $ sym (Iso.sec (nth-pow-root-iso (1+ b)) x))
      (cong fst $ sym (Iso.sec (nth-pow-root-iso (1+ b)) y))
      x≤y)

slopeMonotone^ : (n : ℕ) (a b a' b' : ℝ₊)
  → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
  → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
  (((fst b ^ⁿ n) -ᵣ (fst a ^ⁿ n))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
      ≤ᵣ
  (((fst b' ^ⁿ n) -ᵣ (fst a' ^ⁿ n))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
slopeMonotone^ zero a b a' b' a<b a'<b' a≤a' b≤b' =
  ≡ᵣWeaken≤ᵣ _ _
    ((Rℝ.0LeftAnnihilates' _ _ (+-ᵣ _))
    ∙ sym (Rℝ.0LeftAnnihilates' _ _ (+-ᵣ _)))
slopeMonotone^ (suc zero) a b a' b' a<b a'<b' a≤a' b≤b' =
  ≡ᵣWeaken≤ᵣ _ _
    ((cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a<b )) (cong₂ _-ᵣ_ (Rℝ.·IdR _) (Rℝ.·IdR _))
      ∙ x·invℝ₊[x] _)
     ∙ sym (x·invℝ₊[x] _) ∙ (cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
       (sym ((cong₂ _-ᵣ_ (Rℝ.·IdR _) (Rℝ.·IdR _))))))
slopeMonotone^ (suc (suc N)) a b a' b' a<b a'<b' a≤a' b≤b' =
   subst2 _≤ᵣ_
     (sym ([x·yᵣ]/₊y _ (_ , x<y→0<y-x _ _ a<b ))
       ∙ cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a<b )) (·ᵣComm _ _ ∙ fa.[b-a]·S≡bⁿ-aⁿ))
     (sym ([x·yᵣ]/₊y _ (_ , x<y→0<y-x _ _ a'<b'))
       ∙ cong (_／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' )) (·ᵣComm _ _ ∙ fa'.[b-a]·S≡bⁿ-aⁿ))
     (Seq≤→Σ≤-upto
       (geometricProgression _ fa.r)
       (geometricProgression _ fa'.r)
       (suc (suc N))
       w)
 where
 open bⁿ-aⁿ N
 module fa = factor (fst a) (fst b) (snd a) (snd b)
 module fa' = factor (fst a') (fst b') (snd a') (snd b')

 w : (n₁ : ℕ) → n₁ ℕ.< suc (suc N) →
      geometricProgression (fst b ^ⁿ (suc N)) (fst a ／ᵣ[ fst b , _ ]) n₁ ≤ᵣ
      geometricProgression (fst b' ^ⁿ (suc N)) (fst a' ／ᵣ[ fst b' , _ ]) n₁
 w n x =
  let (m , p) = ℕ.predℕ-≤-predℕ x

      bⁿPos : 0 <ᵣ fst b ^ⁿ n
      bⁿPos = 0<x^ⁿ (fst b) n (snd b)

      b'ⁿPos : 0 <ᵣ fst b' ^ⁿ n
      b'ⁿPos = 0<x^ⁿ (fst b') n (snd b')

      leftPath :
        (fst b ^ⁿ m) ·ᵣ (fst a ^ⁿ n) ≡
        geometricProgression (fst b ^ⁿ suc N) fa.r n
      leftPath =
          (cong₂ _·ᵣ_ refl
            (sym ([x/y]·yᵣ (fst a ^ⁿ n) (fst b ^ⁿ n) (inl bⁿPos))
             ∙ ·ᵣComm
               ((fst a ^ⁿ n) ／ᵣ[ fst b ^ⁿ n , inl bⁿPos ])
               (fst b ^ⁿ n))
           ∙ ·ᵣAssoc
             (fst b ^ⁿ m) (fst b ^ⁿ n)
             ((fst a ^ⁿ n) ／ᵣ[ fst b ^ⁿ n , inl bⁿPos ]))
        ∙ cong₂ _·ᵣ_
            (cong fst (^ℕ-+ b m n) ∙ cong ((fst b) ^ⁿ_) p)
            (／^ⁿ n (fst a) (fst b) fa.0＃b (inl bⁿPos))
        ∙ sym (geometricProgressionClosed (fst b ^ⁿ suc N) fa.r n)

      rightPath :
        (fst b' ^ⁿ m) ·ᵣ (fst a' ^ⁿ n) ≡
        geometricProgression (fst b' ^ⁿ suc N) fa'.r n
      rightPath =
          (cong₂ _·ᵣ_ refl
            (sym ([x/y]·yᵣ (fst a' ^ⁿ n) (fst b' ^ⁿ n) (inl b'ⁿPos))
             ∙ ·ᵣComm
               ((fst a' ^ⁿ n) ／ᵣ[ fst b' ^ⁿ n , inl b'ⁿPos ])
               (fst b' ^ⁿ n))
           ∙ ·ᵣAssoc
             (fst b' ^ⁿ m) (fst b' ^ⁿ n)
             ((fst a' ^ⁿ n) ／ᵣ[ fst b' ^ⁿ n , inl b'ⁿPos ]))
        ∙ cong₂ _·ᵣ_
            (cong fst (^ℕ-+ b' m n) ∙ cong ((fst b') ^ⁿ_) p)
            (／^ⁿ n (fst a') (fst b') fa'.0＃b (inl b'ⁿPos))
        ∙ sym (geometricProgressionClosed (fst b' ^ⁿ suc N) fa'.r n)

      product≤ :
        (fst b ^ⁿ m) ·ᵣ (fst a ^ⁿ n) ≤ᵣ
        (fst b' ^ⁿ m) ·ᵣ (fst a' ^ⁿ n)
      product≤ =
        ≤ᵣ₊Monotone·ᵣ
          (fst b ^ⁿ m) (fst b' ^ⁿ m)
          (fst a ^ⁿ n) (fst a' ^ⁿ n)
          (<ᵣWeaken≤ᵣ 0 (fst b' ^ⁿ m)
            (0<x^ⁿ (fst b') m (snd b')))
          (<ᵣWeaken≤ᵣ 0 (fst a ^ⁿ n)
            (0<x^ⁿ (fst a) n (snd a)))
          (^ⁿ-Monotone m (<ᵣWeaken≤ᵣ 0 (fst b) (snd b)) b≤b')
          (^ⁿ-Monotone n (<ᵣWeaken≤ᵣ 0 (fst a) (snd a)) a≤a')
  in subst2
    {x = (fst b ^ⁿ m) ·ᵣ (fst a ^ⁿ n)}
    {y = geometricProgression (fst b ^ⁿ suc N) fa.r n}
    {z = (fst b' ^ⁿ m) ·ᵣ (fst a' ^ⁿ n)}
    {w = geometricProgression (fst b' ^ⁿ suc N) fa'.r n}
    _≤ᵣ_ leftPath rightPath product≤

slope-monotone-ₙ√ : (n : ℕ) (a b a' b' : ℝ₊)
  → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
  → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
  ((fst (root (1+ n) b') -ᵣ fst (root (1+ n) a'))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
      ≤ᵣ
  ((fst (root (1+ n) b) -ᵣ fst (root (1+ n) a))
    ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
slope-monotone-ₙ√ n a b a' b' a<b a'<b' a≤a' b≤b' =
  fst (x/y≤x'/y'≃y'/x'≤y/x _ _ _ _) $
   subst2 _≤ᵣ_
    ((cong₂ _·ᵣ_ (cong₂ _-ᵣ_
      (cong fst (Iso.sec (nth-pow-root-iso (1+ n)) _))
     (cong fst (Iso.sec (nth-pow-root-iso (1+ n)) _))) refl))
    (cong₂ _·ᵣ_ (cong₂ _-ᵣ_
     (cong fst (Iso.sec (nth-pow-root-iso (1+ n)) _))
     (cong fst (Iso.sec (nth-pow-root-iso (1+ n)) _))) refl)
    $ slopeMonotone^ (suc n)
     ((root (1+ n) a)) ((root (1+ n) b)) ((root (1+ n) a')) ((root (1+ n) b'))
    (ₙ√-StrictMonotone (1+ n) a<b)
      (ₙ√-StrictMonotone (1+ n) a'<b')
       (ₙ√-Monotone {a} {a'} (1+ n) a≤a')
       ((ₙ√-Monotone {b} {b'} (1+ n) b≤b'))



uContRoot0 : ∀ n → ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ (u : ℝ₊) → fst u <ᵣ rat (fst δ)
         → (fst (root n u)) <ᵣ rat (fst ε))
uContRoot0 (1+ n) ε =
    (ε ℚ₊^ⁿ (suc n))
  , λ u u<εⁿ →
    isTrans<≡ᵣ _ _ _ (ₙ√-StrictMonotone
         {y = ℚ₊→ℝ₊ (ε ℚ₊^ⁿ (suc n))} (1+ n) u<εⁿ)
         (cong (fst ∘ root (1+ n)) (
            ℝ₊≡ (sym (^ⁿ-ℚ^ⁿ (suc n) (fst ε))))
          ∙ cong fst (Iso.ret (nth-pow-root-iso (1+ n)) (ℚ₊→ℝ₊ ε)))


·DistRoot : ∀ x y b → root b x ₊·ᵣ root b y ≡ root b (x ₊·ᵣ y)
·DistRoot x y b =
   sym (Iso.ret (nth-pow-root-iso b) _) ∙ cong (root b)
    (ℝ₊≡ (^ⁿ-ldist-·
      (fst (root b x)) (fst (root b y)) (ℕ₊₁→ℕ b))
      ∙ cong₂ _₊·ᵣ_
       (Iso.sec (nth-pow-root-iso b) x)
       (Iso.sec (nth-pow-root-iso b) y))

invCommRoot : ∀ x b → invℝ₊ (root b x) ≡ root b (invℝ₊ x)
invCommRoot x b =
  isoFunInjective (nth-pow-root-iso b) _ _
   (₊^ⁿ-invℝ₊ (ℕ₊₁→ℕ b) (root b x)
     ∙ cong invℝ₊ (Iso.sec (nth-pow-root-iso b) _)
     ∙ sym (Iso.sec (nth-pow-root-iso b) _))

pow-root-comm₊ : ∀ x a b → (root b x) ₊^ⁿ a ≡ root b (x ₊^ⁿ a)
pow-root-comm₊ x zero b = sym (ₙ√1 b)
pow-root-comm₊ x (suc a) b =
    cong (root b x ₊·ᵣ_) (pow-root-comm₊ x a b)
  ∙ ·DistRoot x (x ₊^ⁿ a) b


pow-root-comm : ∀ x a b → (root b x) ^ℤ a ≡ root b (x ^ℤ a)
pow-root-comm x (pos n) b = pow-root-comm₊ x n b
pow-root-comm x (ℤ.negsuc n) b =
   cong invℝ₊ (pow-root-comm₊ x (suc n) b) ∙
     invCommRoot (x ₊^ⁿ suc n) b



ℝ₊→ℝ₀₊ : ℝ₊ → ℝ₀₊
ℝ₊→ℝ₀₊ (x , y) = x , <ᵣWeaken≤ᵣ _ _ y



a/[a+c]<b/[b+c] : ∀ (a b c : ℝ₊) → fst a <ᵣ fst b →
    fst (a ₊·ᵣ invℝ₊ (a ₊+ᵣ c)) <ᵣ fst (b ₊·ᵣ invℝ₊ (b ₊+ᵣ c))
a/[a+c]<b/[b+c] a b c a<b =
  invEq (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)
   (subst2 _<ᵣ_
     (cong (_+ᵣ fst c ·ᵣ fst a) (·ᵣComm _ _) ∙ sym (·DistR+ _ _ _))
      (sym (·DistR+ _ _ _))
     (<ᵣ-o+ _ _ _ (<ᵣ-o·ᵣ _ _ c a<b) ))



_₀₊+ᵣ_ : ℝ₊ → ℝ₀₊ → ℝ₊
(x , 0<x) ₀₊+ᵣ (y , 0≤y) = x +ᵣ y ,
 (isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) $ <≤ᵣMonotone+ᵣ _ _ _ _ 0<x 0≤y)

_₀₊+₀₊ᵣ_ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
_₀₊+₀₊ᵣ_ = NonNegativeReals._+₀₊_

_₀₊·₀₊ᵣ_ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
_₀₊·₀₊ᵣ_ = NonNegativeReals._·₀₊_



module slope-incr-root (n : ℕ) where

 degree : ℕ₊₁
 degree = 2+ n

 help-fn : (a c : ℝ₊) → ℝ
 help-fn a c =
   fst (root degree (a ₊+ᵣ c)) -ᵣ fst (root degree a)

 help-fn-decr : ∀ c a b → fst a <ᵣ fst b
                 →  help-fn b c <ᵣ help-fn a c
 help-fn-decr c a b a<b =
      subst2
        {x = fst c ·ᵣ fst (invℝ₊ (H.fac.S₊ b))}
        {y = help-fn b c}
        {z = fst c ·ᵣ fst (invℝ₊ (H.fac.S₊ a))}
        {w = help-fn a c}
        _<ᵣ_
        (cong (fst c ·ᵣ_)
          (invℝ₊≡invℝ (H.fac.S₊ b) (inl (H.fac.0<S b)))
          ∙ sym (H.h b))
         (cong (fst c ·ᵣ_)
          (invℝ₊≡invℝ (H.fac.S₊ a) (inl (H.fac.0<S a)))
          ∙ sym (H.h a))
        (invEq (z/y'<x/y≃y₊·z<y'₊·x (fst c) (fst c)
           (H.fac.S₊ a) (H.fac.S₊ b ))
          (<ᵣ-·ᵣo (H.fac.S a) (H.fac.S b) c (Seq<→Σ<
            (geometricProgression
              (fst (root degree (a ₊+ᵣ c)) ^ⁿ suc n) (H.fac.r a))
            (geometricProgression
              (fst (root degree (b ₊+ᵣ c)) ^ⁿ suc n) (H.fac.r b))
            (suc n) (λ m m≤n →
              subst2
                {x = (fst (root degree (a ₊+ᵣ c)) ^ⁿ suc n) ·ᵣ
                     (H.fac.r a ^ⁿ m)}
                {y = geometricProgression
                     (fst (root degree (a ₊+ᵣ c)) ^ⁿ suc n)
                     (H.fac.r a) m}
                {z = (fst (root degree (b ₊+ᵣ c)) ^ⁿ suc n) ·ᵣ
                     (H.fac.r b ^ⁿ m)}
                {w = geometricProgression
                     (fst (root degree (b ₊+ᵣ c)) ^ⁿ suc n)
                     (H.fac.r b) m}
                _<ᵣ_
                (sym (geometricProgressionClosed
                  (fst (root degree (a ₊+ᵣ c)) ^ⁿ suc n)
                  (H.fac.r a) m))
                (sym (geometricProgressionClosed
                  (fst (root degree (b ₊+ᵣ c)) ^ⁿ suc n)
                  (H.fac.r b) m))
                (<≤ᵣ₊Monotone·ᵣ
                  (ℝ₊→ℝ₀₊ (root degree (a ₊+ᵣ c)
                    ₊·ᵣ (root degree (a ₊+ᵣ c) ₊^ⁿ n)))
                  (fst (root degree (b ₊+ᵣ c)) ^ⁿ suc n)
                  ((H.fac.r a , H.fac.0<r a) ₊^ⁿ m)
                  (H.fac.r b ^ⁿ m)

                     (^ⁿ-StrictMonotone (suc n)
                      (ℕ.suc-≤-suc ℕ.zero-≤)
                      (<ᵣWeaken≤ᵣ 0 (fst (root degree (a ₊+ᵣ c)))
                        (snd (root degree (a ₊+ᵣ c))))
                      (<ᵣWeaken≤ᵣ 0 (fst (root degree (b ₊+ᵣ c)))
                        (snd (root degree (b ₊+ᵣ c))))
                       (ₙ√-StrictMonotone degree
                         (<ᵣ-+o (fst a) (fst b) (fst c) a<b)))
                     (^ⁿ-Monotone m
                      (<ᵣWeaken≤ᵣ 0 (H.fac.r a) (H.fac.0<r a))
                       (subst2
                         {x = fst (root degree
                           (a ₊·ᵣ invℝ₊ (a ₊+ᵣ c)))}
                         {y = H.fac.r a}
                         {z = fst (root degree
                           (b ₊·ᵣ invℝ₊ (b ₊+ᵣ c)))}
                         {w = H.fac.r b}
                         _≤ᵣ_
                         (sym (cong fst
                            (·DistRoot a (invℝ₊ (a ₊+ᵣ c)) degree))
                            ∙ cong (fst (root degree a) ·ᵣ_)
                              (cong fst
                                (sym (invCommRoot (a ₊+ᵣ c) degree))
                               ∙ invℝ₊≡invℝ (root degree (a ₊+ᵣ c))
                                 (inl (snd (root degree (a ₊+ᵣ c))))))
                         (sym (cong fst
                            (·DistRoot b (invℝ₊ (b ₊+ᵣ c)) degree))
                            ∙ cong (fst (root degree b) ·ᵣ_)
                              (cong fst
                                (sym (invCommRoot (b ₊+ᵣ c) degree))
                               ∙ invℝ₊≡invℝ (root degree (b ₊+ᵣ c))
                                 (inl (snd (root degree (b ₊+ᵣ c))))))
                         (ₙ√-Monotone
                           {x = a ₊·ᵣ invℝ₊ (a ₊+ᵣ c)}
                           {y = b ₊·ᵣ invℝ₊ (b ₊+ᵣ c)} degree
                           (<ᵣWeaken≤ᵣ
                             (fst (a ₊·ᵣ invℝ₊ (a ₊+ᵣ c)))
                             (fst (b ₊·ᵣ invℝ₊ (b ₊+ᵣ c)))
                             (a/[a+c]<b/[b+c] a b c a<b))))))))))

  where
  open bⁿ-aⁿ n hiding (n)

  module H (a : ℝ₊) where
   module fac = factor
     (fst (root degree a)) (fst (root degree (a ₊+ᵣ c)))
     (snd (root degree a)) (snd (root degree (a ₊+ᵣ c)))

   h : fst (root degree (a ₊+ᵣ c)) -ᵣ fst (root degree a) ≡ (c .fst ／ᵣ[
                Sₙ (fst (root degree (a ₊+ᵣ c)) ^ⁿ suc n)
                (r (fst (root degree a)) (fst (root degree (a ₊+ᵣ c)))
                 (snd (root degree a)) (snd (root degree (a ₊+ᵣ c))) )
                (bⁿ-aⁿ.n n)
                , inl fac.0<S ])
   h = x·y≡z→x≡z/y _ _ _ (inl fac.0<S) ((fac.[b-a]·S≡bⁿ-aⁿ

         ∙ cong₂ _-ᵣ_
         (cong fst
          (Iso.sec (nth-pow-root-iso degree) (a ₊+ᵣ c)))
         (cong fst
          (Iso.sec (nth-pow-root-iso degree) a))
           ∙ ℝ!))


opaque
 unfolding -ᵣ_
 -ᵣWeaken<ᵣ : ∀ a b c → 0 ≤ᵣ b → a <ᵣ c  → a -ᵣ b <ᵣ c
 -ᵣWeaken<ᵣ a b c 0≤b a<c =
   isTrans<≡ᵣ _ _ _
     (<≤ᵣMonotone+ᵣ _ _ _ _ a<c (-ᵣ≤ᵣ _ _ 0≤b))
     (+IdR _)

opaque
 unfolding _+ᵣ_ minᵣ
 nth-root-slope-incr : ∀ n (x : ℚ₊) (Δ : ℚ₊)
    → fst (root (1+ n) ((ℚ₊→ℝ₊ x) ₊+ᵣ (ℚ₊→ℝ₊ Δ)))
       -ᵣ fst (root (1+ n) (ℚ₊→ℝ₊ x))
       ≤ᵣ fst (root (1+ n) (ℚ₊→ℝ₊ Δ))
 nth-root-slope-incr zero x Δ =
   ≡ᵣWeaken≤ᵣ _ _
     (cong (_-ᵣ rat (fst x)) (+ᵣ-rat (fst x) (fst Δ))
     ∙ -ᵣ-rat₂ _ _
     ∙ cong rat ℚ!)
 nth-root-slope-incr (suc n) x Δ =
    x<y+δ→x≤y _ _ h

  where

   h : ∀ (ε : ℚ₊) →
             fst (root (1+ (suc n)) ((ℚ₊→ℝ₊ x) ₊+ᵣ (ℚ₊→ℝ₊ Δ)))
       -ᵣ fst (root (1+ (suc n)) (ℚ₊→ℝ₊ x))
          <ᵣ (fst (NthRoot.nth-root n (ℚ₊→ℝ₊ Δ))) +ᵣ rat (fst ε)

   h ε = PT.rec
     (isProp<ᵣ _ _)
     (λ (δ , X)
        --(δ' , X')
      → let δ⊓x = min₊ x δ in
        let δ⊓x≤δ : rat (fst δ⊓x) ≤ᵣ rat (fst δ)
            δ⊓x≤δ =
              isTrans≡≤ᵣ _ _ _
                (sym (minᵣ-rat (fst x) (fst δ)))
                (min≤ᵣ' (rat (fst x)) (rat (fst δ)))

            δ⊓x≤x : rat (fst δ⊓x) ≤ᵣ rat (fst x)
            δ⊓x≤x =
              isTrans≡≤ᵣ _ _ _
                (sym (minᵣ-rat (fst x) (fst δ)))
                (min≤ᵣ (rat (fst x)) (rat (fst δ)))

            δ⊓x/2<δ : rat (fst (δ⊓x /2₊)) <ᵣ rat (fst δ)
            δ⊓x/2<δ =
              isTrans<≤ᵣ _ _ _
                (<ℚ→<ᵣ _ _ (/2₊<id δ⊓x))
                δ⊓x≤δ

            δ⊓x/2<x : rat (fst (δ⊓x /2₊)) <ᵣ rat (fst x)
            δ⊓x/2<x =
              isTrans<≤ᵣ _ _ _
                (<ℚ→<ᵣ _ _ (/2₊<id δ⊓x))
                δ⊓x≤x
        in
        let ineq2 =
                -- isTrans<ᵣ _ _ _
                  -ᵣWeaken<ᵣ _ _ _
                     (<ᵣWeaken≤ᵣ _ _
                      (snd (root (1+ (suc n)) (ℚ₊→ℝ₊ (δ⊓x /2₊)))))
                     (isTrans<≡ᵣ _ _ _
                       (a-b<c⇒a<c+b _ _ _
                         (isTrans≤<ᵣ _ _ _
                          (≤absᵣ _)
                          (fst (∼≃abs<ε _ _ _)
                            (sym∼ _ _ _
                              (X _ _
                                (subst (_∼[ δ ]
                                   (ℚ₊→ℝ₊ (δ⊓x /2₊) .fst +ᵣ rat (fst Δ)))
                                 (+IdL _)
                                 (+ᵣ-∼ 0 (ℚ₊→ℝ₊ (δ⊓x /2₊) .fst)
                                 (rat (fst Δ)) δ
                                    (invEq (∼≃abs<ε _ _ _)
                                      (isTrans≡<ᵣ _ _ _
                                        (minusComm-absᵣ _ _ ∙
                                         cong (absᵣ ∘ (ℚ₊→ℝ₊ (δ⊓x /2₊) .fst +ᵣ_))
                                           (-ᵣ-rat 0) ∙ cong absᵣ (+IdR _)
                                         ∙ absᵣPos _ ((ℚ₊→ℝ₊ (δ⊓x /2₊) .snd)))
                                        δ⊓x/2<δ))))))) ))
                       (+ᵣComm _ _))

        in isTrans<ᵣ _ _ _
             (slope-incr-root.help-fn-decr
               n (ℚ₊→ℝ₊ Δ) (ℚ₊→ℝ₊ (δ⊓x /2₊)) _
                 δ⊓x/2<x)
             ineq2
       )
      (IsContinuousRoot (2+ n) (rat (fst Δ))
        ε (snd (ℚ₊→ℝ₊ Δ)))




 uContRootℚ : ∀ n → IsUContinuousℚℙ posℙ
                    (curry (fst ∘ root n) ∘ rat)
 uContRootℚ (1+ n) ε =
   δ , ℚ.elimBy≡⊎<' {A = A} symCase reflCase stepCase
  where
  δ : ℚ₊
  δ = ε ℚ₊^ⁿ (suc n)

  A : ℚ → ℚ → Type₀
  A u v =
    (u∈ : rat u ∈ posℙ) (v∈ : rat v ∈ posℙ) →
    abs (u ℚ.- v) ℚ.< fst δ →
    fst (root (1+ n) (rat u , u∈)) ∼[ ε ]
    fst (root (1+ n) (rat v , v∈))

  symCase : ∀ x y → A x y → A y x
  symCase x y X u∈ v∈ y-x<δ =
    sym∼
      (fst (root (1+ n) (rat x , v∈)))
      (fst (root (1+ n) (rat y , u∈)))
      ε
      (X v∈ u∈
      (subst (ℚ._< fst δ) (ℚO.abs-Comm y x) y-x<δ))

  reflCase : ∀ x → A x x
  reflCase x u∈ v∈ _ =
    subst (fst (root (1+ n) (rat x , u∈)) ∼[ ε ]_)
      (cong (fst ∘ root (1+ n))
        (Σ≡Prop (∈-isProp posℙ) refl))
      (refl∼ (fst (root (1+ n) (rat x , u∈))) ε)

  stepCase : ∀ x (Δ : ℚ₊) → A x (x ℚ.+ fst Δ)
  stepCase x Δ u∈ v∈ X =
    let v∈+ : (rat x +ᵣ rat (fst Δ)) ∈ posℙ
        v∈+ = subst (_∈ posℙ) (sym (+ᵣ-rat x (fst Δ))) v∈

        cancelStep : (x ℚ.+ fst Δ) ℚ.- x ≡ fst Δ
        cancelStep = ℚ!

        stepDistance : abs (x ℚ.- (x ℚ.+ fst Δ)) ≡ fst Δ
        stepDistance =
            ℚO.abs-Comm x (x ℚ.+ fst Δ)
          ∙ cong abs cancelStep
          ∙ ℚO.0<→abs≡id (fst Δ) (snd Δ)

        X' : fst (root (1+ n) (ℚ₊→ℝ₊ Δ)) <ᵣ rat (fst ε)
        X' = isTrans<≡ᵣ _ _ _
          (ₙ√-StrictMonotone {ℚ₊→ℝ₊ Δ} {ℚ₊→ℝ₊ δ} (1+ n)
          ((<ℚ→<ᵣ _ _ (subst (ℚ._< fst δ) stepDistance X))))
          (cong (fst ∘ root (1+ n))
             (ℝ₊≡ (sym (^ⁿ-ℚ^ⁿ (suc n) (fst ε))))
            ∙ cong fst (Iso.ret (nth-pow-root-iso (1+ n))
              (ℚ₊→ℝ₊ ε)))

        close+ :
          fst (root (1+ n) (rat x +ᵣ rat (fst Δ) , v∈+)) ∼[ ε ]
          fst (root (1+ n) (rat x , u∈))
        close+ =
          invEq
            (∼≃abs<ε
              (fst (root (1+ n) (rat x +ᵣ rat (fst Δ) , v∈+)))
              (fst (root (1+ n) (rat x , u∈)))
              ε)
            (isTrans≡<ᵣ _ _ _ (absᵣPos _
              (fst (x<y≃0<y-x _ _)
                (ₙ√-StrictMonotone (1+ n)
                  (isTrans≡<ᵣ _ _ _
                    (sym (+IdR _)) (<ᵣ-o+ _ _ (rat x) (snd (ℚ₊→ℝ₊ Δ)))))))
             (isTrans≤<ᵣ _ _ _
                 (isTrans≡≤ᵣ _ _ _
                    (cong₂ (λ v∈ u∈ →
                       fst (root (1+ n) (rat x +ᵣ rat (fst Δ) , v∈)) -ᵣ
                        fst (root (1+ n) (rat x , u∈)))
                         (∈-isProp posℙ (rat x +ᵣ rat (fst Δ)) _ _)
                         (∈-isProp posℙ (rat x) _ _))
                     (nth-root-slope-incr n
                       (x , (<ᵣ→<ℚ 0 x u∈)) Δ))
                 X'))
    in subst (fst (root (1+ n) (rat x , u∈)) ∼[ ε ]_)
        (cong (fst ∘ root (1+ n))
          (Σ≡Prop (∈-isProp posℙ) (+ᵣ-rat x (fst Δ))))
        (sym∼
          (fst (root (1+ n) (rat x +ᵣ rat (fst Δ) , v∈+)))
          (fst (root (1+ n) (rat x , u∈)))
          ε
          close+)

uContRoot : ∀ n → IsUContinuousℙ posℙ
                   (curry (fst ∘ root n))
uContRoot n = IsUContinuousℚℙ→IsUContinuousℙ (curry (fst ∘ root n))
  (λ x 0<x y 0<y x≤y →
    ₙ√-Monotone {x = x , 0<x} {y = y , 0<y} n x≤y)
  (uContRootℚ n)


^ℤ-· : ∀ x a b → ((x ^ℤ a) ^ℤ b) ≡  (x ^ℤ (a ℤ.· b))
^ℤ-· x (pos n) (pos n₁) =
  ^ℕ-· x n n₁ ∙ cong (x ^ℤ_) (ℤ.pos·pos n n₁)
^ℤ-· x (pos zero) (ℤ.negsuc n₁) = 1^ℤ≡1 (ℤ.negsuc n₁)
^ℤ-· x (pos (suc n)) (ℤ.negsuc n₁) =
     cong invℝ₊ (^ℕ-· x (suc n) (suc n₁))
   ∙ cong (x ^ℤ_)
       (cong ℤ.-_ (ℤ.pos·pos (suc n) (suc n₁))
       ∙ sym (ℤ.pos·negsuc (suc n) n₁))
^ℤ-· x (ℤ.negsuc n) (pos zero) =
  cong {x = pos zero} {y = ℤ.negsuc n ℤ.· pos zero}
    (x ^ℤ_) (sym (ℤ.·AnnihilR (ℤ.negsuc n)))
^ℤ-· x (ℤ.negsuc n) (pos (suc n₁)) =
      ₊^ⁿ-invℝ₊ (suc n₁) (x ₊^ⁿ suc n)
   ∙∙ cong invℝ₊ (^ℕ-· x (suc n) (suc n₁))
   ∙∙ cong (x ^ℤ_)
     (cong ℤ.-_ (ℤ.pos·pos (suc n) (suc n₁))
     ∙ sym (ℤ.negsuc·pos n (suc n₁)))

^ℤ-· x (ℤ.negsuc n) (ℤ.negsuc n₁) =
        (sym (₊^ⁿ-invℝ₊ (suc n₁) (invℝ₊ (x ₊^ⁿ suc n)))
       ∙ cong (_₊^ⁿ (suc n₁)) (invℝ₊Invol (x ₊^ⁿ suc n)))
   ∙∙ ^ℕ-· x (suc n) (suc n₁)
   ∙∙ cong (x ^ℤ_)
     (ℤ.pos·pos (suc n) (suc n₁) ∙ sym (ℤ.negsuc·negsuc n n₁))



pre^ℚ-aprox : ∀ a b → ℚApproxℙ'' posℙ posℙ
                    λ x 0<x → (root b ((x , 0<x) ^ℤ a))
pre^ℚ-aprox a b =
  ℚApproxℙ∘ posℙ posℙ posℙ
     (curry (root b))
      (curry ((_^ℤ a)))
       (uContRoot b)
      (ℚApproxℙ'→ℚApproxℙ'' posℙ posℙ (curry (root b)) (ℚApproxℙ-root b))
      (^ℤ-ℚApproxℙ'' a)

module _ (x : ℝ) (0<x : 0 <ᵣ x) where
 ^ℚ-coh' : ∀ a a' b b' → pos a ℤ.· pos (suc b') ≡ pos a' ℤ.· pos (suc b) →
   (root (1+ b) (x , 0<x)  ^ℤ (pos a)) ≡ (root (1+ b') (x , 0<x) ^ℤ (pos a'))
 ^ℚ-coh' n n' b b' p =
   let leftBase : ℝ₊
       leftBase = root (1+ b') (root (1+ b) (x , 0<x))

       rightBase : ℝ₊
       rightBase = root (1+ b) (root (1+ b') (x , 0<x))

       baseComm : leftBase ≡ rightBase
       baseComm =
           sym ((cong Iso.inv (pow-root-+ℕ₊₁ (1+ b') (1+ b))) ≡$ (x , 0<x))
         ∙∙ cong (λ degree → root degree (x , 0<x))
              (·₊₁-comm (1+ b') (1+ b))
         ∙∙ ((cong Iso.inv (pow-root-+ℕ₊₁ (1+ b) (1+ b'))) ≡$ (x , 0<x))

       exponentComm :
         pos (suc b') ℤ.· pos n ≡ pos (suc b) ℤ.· pos n'
       exponentComm =
           ℤ.·Comm (pos (suc b')) (pos n)
         ∙∙ p
         ∙∙ ℤ.·Comm (pos n') (pos (suc b))

       commuteCommonPower :
         leftBase ^ℤ (pos (suc b') ℤ.· pos n)
           ≡ rightBase ^ℤ (pos (suc b) ℤ.· pos n')
       commuteCommonPower = cong₂ _^ℤ_ baseComm exponentComm
   in
       (sym (cong (_₊^ⁿ n)
          (Iso.sec (nth-pow-root-iso (1+ b')) (root (1+ b) (x , 0<x))))
       ∙ ^ℤ-· leftBase (pos (suc b')) (pos n))
     ∙∙ commuteCommonPower
     ∙∙ (sym (^ℤ-· rightBase (pos (suc b)) (pos n'))
       ∙ cong (_₊^ⁿ n')
          (Iso.sec (nth-pow-root-iso (1+ b)) (root (1+ b') (x , 0<x))))

 ^ℚ-coh : ∀ a a' b b' → a ℤ.· pos (suc b') ≡ a' ℤ.· pos (suc b) →
   (root (1+ b) (x , 0<x)  ^ℤ a) ≡ (root (1+ b') (x , 0<x) ^ℤ a')
 ^ℚ-coh (pos n) (pos n₁) b b' p = ^ℚ-coh' n n₁ b b' p

 ^ℚ-coh (pos n) (ℤ.negsuc n₁) b b' p =
   ⊥.rec (ℤ.posNotnegsuc
     (n ℕ.· suc b') (b ℕ.+ n₁ ℕ.· suc b)
     (ℤ.pos·pos n (suc b') ∙∙ p ∙∙
       (ℤ.negsuc·pos n₁ (suc b) ∙
        cong (ℤ.-_) (sym (ℤ.pos·pos (suc n₁) (suc b))))))
 ^ℚ-coh (ℤ.negsuc n) (pos n₁) b b' p =
   ⊥.rec (ℤ.negsucNotpos
     (b' ℕ.+ n ℕ.· suc b') (n₁ ℕ.· suc b)
     ((cong (ℤ.-_) (ℤ.pos·pos (suc n) (suc b')) ∙
       sym (ℤ.negsuc·pos n (suc b'))) ∙∙ p ∙∙
       sym (ℤ.pos·pos n₁ (suc b))))
 ^ℚ-coh (ℤ.negsuc n) (ℤ.negsuc n₁) b b' p =
   cong invℝ₊ (^ℚ-coh' (suc n) (suc n₁) b b' (
     sym (ℤ.-DistL· (ℤ.negsuc n) (pos (suc b')))
      ∙∙ cong ℤ.-_ p ∙∙
      ℤ.-DistL· (ℤ.negsuc n₁) (pos (suc b))))

 _^ℚc_ : ℚ → ℝ₊
 _^ℚc_ = SQ.Elim.go w
  where
  w : Elim (λ _ → ℝ₊)
  w .Elim.isSetB _ = isSetℝ₊
  w .Elim.f (a , b) = (root b (x , 0<x)) ^ℤ a
  w .Elim.f∼ (a , (1+ b)) (a' , (1+ b')) r =
    ^ℚ-coh a a' b b' r

_^ℚ_ : ℝ₊ → ℚ →  ℝ₊
_^ℚ_ = uncurry _^ℚc_

opaque
  ^ℚ-zero : ∀ x → x ^ℚ 0 ≡ 1
  ^ℚ-zero x = refl

IsContinuous^ℚ : ∀ q → IsContinuousWithPred posℙ
                          (curry (fst ∘ (_^ℚ q)))
IsContinuous^ℚ = SQ.ElimProp.go w
  where
  w : ElimProp (λ q → IsContinuousWithPred posℙ (curry (fst ∘ (_^ℚ q))))
  w .ElimProp.isPropB _ = isPropΠ3 λ _ _ _ → squash₁
  w .ElimProp.f (a , b) =
    IsContinuousWP∘ posℙ posℙ (curry (fst ∘ _^ℤ a)) (curry (fst ∘ root b))
      (curry (snd ∘ root b))
      (IsContinuous^ℤ a)
      (IsContinuousRoot b)

^ℚ-+ : ∀ x a b → ((x ^ℚ a) ₊·ᵣ (x ^ℚ b)) ≡ (x ^ℚ (a ℚ.+ b))
^ℚ-+ x₊@(x , 0<x) = SQ.ElimProp2.go w
 where
 w : ElimProp2 (λ z z₁ → ((x₊ ^ℚ z) ₊·ᵣ (x₊ ^ℚ z₁)) ≡ (x₊ ^ℚ (z ℚ.+ z₁)))
 w .ElimProp2.isPropB _ _ = isSetℝ₊ _ _
 w .ElimProp2.f (a , 1+ b) (a' , 1+ b') =
  ((root (1+ b) (x , 0<x) ^ℤ a) ₊·ᵣ (root (1+ b') (x , 0<x) ^ℤ a'))
   ≡⟨ cong₂ _₊·ᵣ_
        (cong (_^ℤ a) b√x≡
          ∙ ^ℤ-· bb'√x (pos (suc b')) a)
        (cong (_^ℤ a') b'√x≡
          ∙ ^ℤ-· bb'√x (pos (suc b)) a') ⟩
            ((bb'√x ^ℤ (ℤ.ℕ₊₁→ℤ (1+ b') ℤ.· a))
         ₊·ᵣ (bb'√x ^ℤ (ℤ.ℕ₊₁→ℤ (1+ b) ℤ.· a')))
   ≡⟨ (λ i → ^ℤ-+ bb'√x
       (ℤ.·Comm (pos (suc b')) a i)
       (ℤ.·Comm (pos (suc b)) a' i)
       i) ⟩
   ((bb'√x ^ℤ
      (a ℤ.· ℤ.ℕ₊₁→ℤ (1+ b') ℤ.+ a' ℤ.· ℤ.ℕ₊₁→ℤ (1+ b)))) ∎

  where
   bb'√x : ℝ₊
   bb'√x = root ((1+ b) ·₊₁ (1+ b')) (x , 0<x)

   b√x≡ : root (1+ b) (x , 0<x) ≡ bb'√x ₊^ⁿ (suc b')
   b√x≡ =
     sym (Iso.sec (nth-pow-root-iso (1+ b')) (root (1+ b) x₊)) ∙
      (cong (_₊^ⁿ (suc b')) $ sym (cong Iso.inv (pow-root-+ℕ₊₁ (1+ b') (1+ b)) ≡$ x₊)
        ∙ cong (flip root x₊) (·₊₁-comm (1+ b') (1+ b)))

   b'√x≡ : root (1+ b') (x , 0<x) ≡ bb'√x ₊^ⁿ (suc b)
   b'√x≡ = sym (Iso.sec (nth-pow-root-iso (1+ b)) (root (1+ b') x₊)) ∙
      (cong (_₊^ⁿ (suc b)) $ sym (cong Iso.inv (pow-root-+ℕ₊₁ (1+ b) (1+ b')) ≡$ x₊))


^ℚ-· : ∀ x a b → ((x ^ℚ a) ^ℚ b) ≡ (x ^ℚ (a ℚ.· b))
^ℚ-· x₊@(x , 0<x) = SQ.ElimProp2.go w
 where
 w : ElimProp2 (λ a b → ((x₊ ^ℚ a) ^ℚ b) ≡ (x₊ ^ℚ (a ℚ.· b)))
 w .ElimProp2.isPropB _ _ = isSetℝ₊ _ _
 w .ElimProp2.f (a , 1+ b) (a' , 1+ b') =
   let commonRoot : ℝ₊
       commonRoot = root ((1+ b) ·₊₁ (1+ b')) x₊

       rootComm : root (1+ b') (root (1+ b) x₊) ≡ commonRoot
       rootComm =
           sym ((cong Iso.inv (pow-root-+ℕ₊₁ (1+ b') (1+ b))) ≡$ x₊)
         ∙ cong (flip root x₊) (·₊₁-comm (1+ b') (1+ b))
   in
     cong (_^ℤ a')
       (sym (pow-root-comm (root (1+ b) x₊) a (1+ b'))
       ∙ cong (_^ℤ a) rootComm)
     ∙ ^ℤ-· commonRoot a a'



invℝ₊^ℤ : ∀ x a → (invℝ₊ x) ^ℤ (ℤ.- a) ≡ x ^ℤ a
invℝ₊^ℤ x (pos zero) = refl
invℝ₊^ℤ x (pos (suc n)) = cong invℝ₊ (₊^ⁿ-invℝ₊ (suc n) x)
 ∙ invℝ₊Invol (x ₊^ⁿ suc n)
invℝ₊^ℤ x (ℤ.negsuc n) = ₊^ⁿ-invℝ₊ (suc n) x

invℝ₊[^ℤ] : ∀ x a → (invℝ₊ x ^ℤ a) ≡ invℝ₊ (x ^ℤ a)
invℝ₊[^ℤ] x (pos zero) = ℝ₊≡ (sym (invℝ₊-rat 1))
invℝ₊[^ℤ] x (pos (suc n)) = ₊^ⁿ-invℝ₊ (suc n) x
invℝ₊[^ℤ] x (ℤ.negsuc n) =
  cong invℝ₊ (₊^ⁿ-invℝ₊ (suc n) x)

invℝ₊^ℤ' : ∀ x a → (invℝ₊ x) ^ℤ a ≡ x ^ℤ (ℤ.- a)
invℝ₊^ℤ' x a = cong ((invℝ₊ x) ^ℤ_) (sym (ℤ.-Involutive a)) ∙ invℝ₊^ℤ x (ℤ.- a)



invℝ₊^ℚ : ∀ x a → (invℝ₊ x ^ℚ a) ≡ invℝ₊ (x ^ℚ a)
invℝ₊^ℚ x = SQ.ElimProp.go w

 where
 w : ElimProp (λ a → (invℝ₊ x ^ℚ a) ≡ invℝ₊ (x ^ℚ a))
 w .ElimProp.isPropB _ = isSetℝ₊ _ _
 w .ElimProp.f (a , b) = cong (_^ℤ a) (sym (invCommRoot x b))
   ∙ invℝ₊[^ℤ] (root b x) a

^ℚ-minus : ∀ x a → (x ^ℚ a) ≡ ((invℝ₊ x) ^ℚ (ℚ.- a))
^ℚ-minus x = SQ.ElimProp.go w

 where
 w : ElimProp (λ a → (x ^ℚ a) ≡ ((invℝ₊ x) ^ℚ (ℚ.- a)))
 w .ElimProp.isPropB _ = isSetℝ₊ _ _
 w .ElimProp.f (a , (1+ b)) =
   let degree : ℕ₊₁
       degree = 1 ·₊₁ (1+ b)

       rooted : ℝ₊
       rooted = root degree x
   in
     cong (λ denominator → x ^ℚ [ a , denominator ])
       (sym (·₊₁-identityˡ (1+ b)))
     ∙ sym (invℝ₊^ℤ rooted a)
     ∙ cong (_^ℤ (ℤ.- a)) (invCommRoot x degree)
     ∙ cong (root degree (invℝ₊ x) ^ℤ_)
         (sym (ℤ.-1·x≡-x a))

^ℚ-minus' : ∀ x a → (x ^ℚ (ℚ.- a)) ≡ ((invℝ₊ x) ^ℚ a)
^ℚ-minus' x a = ^ℚ-minus x (ℚ.- a) ∙ cong ((invℝ₊ x) ^ℚ_) (ℚ.-Invol a)



1^ℚ≡1 : ∀ q → 1 ^ℚ q ≡ 1
1^ℚ≡1 = ElimProp.go w
 where
 w : ElimProp (λ q → 1 ^ℚ q ≡ 1)
 w .ElimProp.isPropB _ = isSetℝ₊ _ _
 w .ElimProp.f (a , b) = cong (_^ℤ a) (ₙ√1 b) ∙ 1^ℤ≡1 a

Iso^ₙₒₜ₀ : ∀ q → 0 ℚ.# q  → Iso ℝ₊ ℝ₊
Iso^ₙₒₜ₀ q _ .Iso.fun = _^ℚ q
Iso^ₙₒₜ₀ q 0#q .Iso.inv = _^ℚ (invℚ q 0#q)
Iso^ₙₒₜ₀ q 0#q .Iso.sec x =
 ^ℚ-· x (invℚ q 0#q) q
  ∙∙ cong (x ^ℚ_)
    (ℚ.·Comm (invℚ q 0#q) q ∙ ℚ.x·invℚ[x] q 0#q)
  ∙∙ ℝ₊≡ (·IdR (fst x))
Iso^ₙₒₜ₀ q 0#q .Iso.ret x =
 ^ℚ-· x q (invℚ q 0#q)
  ∙∙ cong (x ^ℚ_) (ℚ.x·invℚ[x] q 0#q)
  ∙∙ ℝ₊≡ (·IdR (fst x))


factor-xᵃ-xᵇ : ∀ x a b → fst (x ^ℚ a) -ᵣ fst (x ^ℚ b) ≡
                        fst (x ^ℚ b) ·ᵣ (fst (x ^ℚ (a ℚ.- b)) -ᵣ 1)
factor-xᵃ-xᵇ x a b =
  let splitExponent : b ℚ.+ (a ℚ.- b) ≡ a
      splitExponent = ℚ!
  in
      cong₂ _-ᵣ_
        (cong (fst ∘ x ^ℚ_) (sym splitExponent)
         ∙ cong fst (sym (^ℚ-+ x b (a ℚ.- b))))
        (sym (·IdR (fst (x ^ℚ b))))
    ∙ sym (·DistL-
        (fst (x ^ℚ b)) (fst (x ^ℚ (a ℚ.- b))) 1)

factor-xᵃ-xᵇ' : ∀ x a b → fst (x ^ℚ a) -ᵣ fst (x ^ℚ b) ≡
                        fst (x ^ℚ a) ·ᵣ (1 -ᵣ fst (x ^ℚ (b ℚ.- a)))
factor-xᵃ-xᵇ' x a b =
  let splitExponent : a ℚ.+ (b ℚ.- a) ≡ b
      splitExponent = ℚ!
  in
    cong₂ _-ᵣ_ (sym (·IdR (fst (x ^ℚ a))))
      (cong fst (cong (x ^ℚ_) (sym splitExponent))
       ∙ cong fst (sym (^ℚ-+ x a (b ℚ.- a))))
    ∙ sym (·DistL-
        (fst (x ^ℚ a)) 1 (fst (x ^ℚ (b ℚ.- a))))

factorOut-xᵃ : ∀ x a b → x ^ℚ a ≡
     ((x ^ℚ b) ₊·ᵣ (x ^ℚ (a ℚ.- b)))
factorOut-xᵃ x a b =
  let splitExponent : b ℚ.+ (a ℚ.- b) ≡ a
      splitExponent = ℚ!
  in
    cong (x ^ℚ_) (sym splitExponent)
    ∙ sym (^ℚ-+ x b (a ℚ.- b))

^ℚ-StrictMonotone : ∀ {x y : ℝ₊} (q : ℚ₊)
    → fst x <ᵣ fst y
    → fst (x ^ℚ (fst q)) <ᵣ fst (y ^ℚ (fst q))
^ℚ-StrictMonotone {x = x} {y = y} = uncurry $ ElimProp.go w
 where
 w : ElimProp (λ q → 0 ℚ.< q → fst x <ᵣ fst y → fst (x ^ℚ q) <ᵣ fst (y ^ℚ q))
 w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → isProp<ᵣ _ _
 w .ElimProp.f (pos zero , 1+ m) 0<q x<y =
   ⊥.rec (ℚ.isIrrefl< 0
     (subst (0 ℚ.<_) (ℚ.[0/n]≡[0/m] m 0) 0<q))
 w .ElimProp.f (pos (suc n) , b) 0<q x<y =
   ^ⁿ-StrictMonotone (suc n) (ℕ.suc-≤-suc  ℕ.zero-≤)
      (<ᵣWeaken≤ᵣ _ _ (snd (root b x)))
      (<ᵣWeaken≤ᵣ _ _ (snd (root b y)))
     (ₙ√-StrictMonotone b x<y)

^ℚ-Monotone : ∀ {x y : ℝ₊} (q : ℚ₊)
    → fst x ≤ᵣ fst y
    → fst (x ^ℚ (fst q)) ≤ᵣ fst (y ^ℚ (fst q))
^ℚ-Monotone {x = x} {y = y} = uncurry $ ElimProp.go w
 where
 w : ElimProp (λ q → 0 ℚ.< q → fst x ≤ᵣ fst y → fst (x ^ℚ q) ≤ᵣ fst (y ^ℚ q))
 w .ElimProp.isPropB _ = isPropΠ2 λ _ _ → isProp≤ᵣ _ _
 w .ElimProp.f (pos zero , 1+ m) 0<q x≤y =
   ⊥.rec (ℚ.isIrrefl< 0
     (subst (0 ℚ.<_) (ℚ.[0/n]≡[0/m] m 0) 0<q))
 w .ElimProp.f (pos (suc n) , b) 0<q x≤y =
   ^ⁿ-Monotone (suc n)
      (<ᵣWeaken≤ᵣ _ _ (snd (root b x)))
     (ₙ√-Monotone b x≤y)


1<^ℚ : ∀ x → (q : ℚ₊) → (1 <ᵣ fst x) → (1 <ᵣ fst (x ^ℚ (fst q)))
1<^ℚ x q₊@(q , 0<q) 1<x =
  subst (_<ᵣ fst (x ^ℚ q))
    (cong fst (1^ℚ≡1 q)) (^ℚ-StrictMonotone q₊ 1<x)


1≤^ℚ : ∀ x → (q : ℚ₊) → (1 ≤ᵣ fst x) → (1 ≤ᵣ fst (x ^ℚ (fst q)))
1≤^ℚ x q₊@(q , 0<q) 1≤x =
  subst (_≤ᵣ fst (x ^ℚ q))
    (cong fst (1^ℚ≡1 q)) (^ℚ-Monotone q₊ 1≤x)


^ℚ-StrictMonotoneR : ∀ {x : ℝ₊} → 1 <ᵣ fst x → (q r : ℚ)
    → q ℚ.< r
    → fst (x ^ℚ q) <ᵣ fst (x ^ℚ r)
^ℚ-StrictMonotoneR {x} 1<x q r q<r =
  isTrans<≡ᵣ _ _ _
    (isTrans≡<ᵣ _ _ _
      (sym (·IdR _ )) (<ᵣ-o·ᵣ _ _ (x ^ℚ q) (1<^ℚ _ (ℚ.<→ℚ₊ _ _ q<r) 1<x)))
   (cong fst $ sym (factorOut-xᵃ x  r q))

^ℚ-StrictMonotoneR' : ∀ {x : ℝ₊} → fst x <ᵣ 1  → (q r : ℚ)
    → q ℚ.< r
    → fst (x ^ℚ r) <ᵣ fst (x ^ℚ q)
^ℚ-StrictMonotoneR' {x} x<1 q r q<r =
   fst (invℝ₊-<-invℝ₊ (x ^ℚ q) (x ^ℚ r))
     (subst2 _<ᵣ_
       (cong fst (invℝ₊^ℚ x q))
       (cong fst (invℝ₊^ℚ x r))
       (^ℚ-StrictMonotoneR {invℝ₊ x}
         1/x<1 q r q<r))
   where
   1/x<1 = isTrans≡<ᵣ _ _ _ (cong fst (sym (invℝ₊1)))
            (invEq (invℝ₊-<-invℝ₊ 1 x) x<1)

^ℚ-MonotoneR : ∀ {x : ℝ₊} → (q r : ℚ) → q ℚ.≤ r
    → 1 ≤ᵣ fst x
    → fst (x ^ℚ q) ≤ᵣ fst (x ^ℚ r)
^ℚ-MonotoneR {x} q r q≤r 1≤x =

  let z = continuousClosedLowerComparison {1}
             (IsContinuousWithPred⊆ posℙ (pred≥ (rat 1))
                (λ x x< → fst ((x , x<) ^ℚ q))
                (λ x → isTrans<≤ᵣ 0 1 x ((decℚ<ᵣ? {0} {1})))
                (IsContinuous^ℚ q))
             (IsContinuousWithPred⊆ posℙ (pred≥ (rat 1))
                (λ x x< → fst ((x , x<) ^ℚ r))
                (λ x → isTrans<≤ᵣ 0 1 x ((decℚ<ᵣ? {0} {1})))
                (IsContinuous^ℚ r))
                (λ u 1≤u → hh (ℚ.≤→<⊎≡ q r q≤r) u 1≤u (ℚ.≤→<⊎≡ 1 u 1≤u))
             (fst x) 1≤x
  in subst (λ 0<x → fst ((fst x , 0<x) ^ℚ q) ≤ᵣ fst ((fst x , 0<x) ^ℚ r))
       (isProp<ᵣ _ _ _ _)
       z


 where
 hh : ((q ≡ r) ⊎ (q ℚ.< r)) → (u : ℚ) (x₀<u : 1 ℚ.≤ u) → (1 ≡ u) ⊎ (1 ℚ.< u) →
        fst
        ((rat u , isTrans<≤ᵣ 0 1 (rat u) decℚ<ᵣ? (≤ℚ→≤ᵣ 1 u x₀<u)) ^ℚ q)
        ≤ᵣ
        fst
        ((rat u , isTrans<≤ᵣ 0 1 (rat u) decℚ<ᵣ? (≤ℚ→≤ᵣ 1 u x₀<u)) ^ℚ r)
 hh _ u x₀<u (inl x) =
   ≡ᵣWeaken≤ᵣ _ _
      (sym ((cong (fst ∘ _^ℚ q) (ℝ₊≡ (cong rat x))))
        ∙∙ cong fst (1^ℚ≡1 q) ∙
           cong fst (sym (1^ℚ≡1 r))
           ∙∙ cong fst (cong (_^ℚ r) (ℝ₊≡ (cong rat x))))
 hh (inr q<r) u 1≤u (inr 1<u) = subst
       (λ uu →
         fst ((rat u , uu) ^ℚ q)
           ≤ᵣ fst ((rat u , uu) ^ℚ r))
            (isProp<ᵣ _ _ _ _)
             (<ᵣWeaken≤ᵣ _ _ ( ^ℚ-StrictMonotoneR
                             {rat u , isTrans<ᵣ 0 1 (rat u)
                                 ((decℚ<ᵣ? {0} {1}))
                                   (<ℚ→<ᵣ _ _ 1<u)}
                              (<ℚ→<ᵣ _ _ 1<u) q r q<r))
 hh (inl q≡r) u 1≤u (inr 1<u) = ≡ᵣWeaken≤ᵣ _ _
   (cong (fst ∘ ((rat u , isTrans<≤ᵣ 0 1 (rat u) decℚ<ᵣ? (≤ℚ→≤ᵣ 1 u 1≤u)) ^ℚ_))
     q≡r)
