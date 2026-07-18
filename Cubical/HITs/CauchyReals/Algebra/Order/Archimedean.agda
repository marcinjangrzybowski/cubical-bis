module Cubical.HITs.CauchyReals.Algebra.Order.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁ using (1+_)
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.ArchimedeanRing.Base
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Base using (OrderedCommRingStr)
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base using (absᵣPos)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance


private
  module ℝOCR = OrderedCommRingStr (snd ℝOrderedCommRing)
  module ℝRing = RingTheory (OrderedCommRing→Ring ℝOrderedCommRing)
  module ℝCanonical = CanonicalEmbeddings ℝOrderedCommRing

  realFromNat : ℕ.ℕ → ℝ
  realFromNat n = ℕ.HasFromNat.fromNat fromNatℝ n {{tt}}


  fromℕ≡fromNat : ∀ n → ℝRing.fromℕ n ≡ realFromNat n
  fromℕ≡fromNat ℕ.zero = refl
  fromℕ≡fromNat (ℕ.suc ℕ.zero) = refl
  fromℕ≡fromNat (ℕ.suc (ℕ.suc n)) =
    cong (realFromNat (ℕ.suc ℕ.zero) +ᵣ_) (fromℕ≡fromNat (ℕ.suc n))
    ∙ fromNat+ᵣ (ℕ.suc ℕ.zero) (ℕ.suc n)


·CancelR<ᵣ : ∀ x y z → realFromNat ℕ.zero <ᵣ z →
  x ·ᵣ z <ᵣ y ·ᵣ z → x <ᵣ y
·CancelR<ᵣ x y z 0<z xz<yz =
  invEq (z<x≃y₊·z<y₊·x y x (z , 0<z))
    (subst2 _<ᵣ_ (·ᵣComm x z) (·ᵣComm y z) xz<yz)


archimedeanPropertyℝ : ∀ x y →
  realFromNat ℕ.zero <ᵣ x → realFromNat ℕ.zero <ᵣ y →
  ∃[ k ∈ ℕ.ℕ ] (x <ᵣ ℝRing.fromℤ (pos (ℕ.suc k)) ·ᵣ y)
archimedeanPropertyℝ x y 0<x 0<y = PT.map
  (λ (1+ k , ∣x/y∣<k+1) →
    let y₊ = y , 0<y
        x/y<k+1 : x ·ᵣ fst (invℝ₊ y₊) <ᵣ ℝRing.fromℕ (ℕ.suc k)
        x/y<k+1 = subst2 _<ᵣ_
          (absᵣPos _ (ℝ₊· (x , 0<x) (invℝ₊ y₊)))
          (sym (fromℕ≡fromNat (ℕ.suc k)))
          ∣x/y∣<k+1
    in k , subst (_<ᵣ ℝRing.fromℕ (ℕ.suc k) ·ᵣ y)
         ([x/₊y]·yᵣ x y₊)
         (<ᵣ-·ᵣo _ _ y₊ x/y<k+1))
  (getClamps (x ·ᵣ fst (invℝ₊ (y , 0<y))))


isArchimedeanRingℝ :
  IsArchimedeanRing
    ℝOCR.0r ℝOCR.1r ℝOCR._+_ ℝOCR._·_ ℝOCR.-_
    ℝOCR._<_ ℝOCR._≤_ ℝRing.fromℤ
isArchimedeanRingℝ .IsArchimedeanRing.isOrderedCommRing =
  isOrderedCommRingℝ
isArchimedeanRingℝ .IsArchimedeanRing.·CancelR< = ·CancelR<ᵣ
isArchimedeanRingℝ .IsArchimedeanRing.isMonomorphism =
  ℝCanonical.isOCRMonoFromℤ
isArchimedeanRingℝ .IsArchimedeanRing.archimedeanProperty =
  archimedeanPropertyℝ


ℝArchimedeanRing : ArchimedeanRing ℓ-zero ℓ-zero
fst ℝArchimedeanRing = ℝ
ArchimedeanRingStr.0r (snd ℝArchimedeanRing) = ℝOCR.0r
ArchimedeanRingStr.1r (snd ℝArchimedeanRing) = ℝOCR.1r
ArchimedeanRingStr._+_ (snd ℝArchimedeanRing) = ℝOCR._+_
ArchimedeanRingStr._·_ (snd ℝArchimedeanRing) = ℝOCR._·_
ArchimedeanRingStr.-_ (snd ℝArchimedeanRing) = ℝOCR.-_
ArchimedeanRingStr._<_ (snd ℝArchimedeanRing) = ℝOCR._<_
ArchimedeanRingStr._≤_ (snd ℝArchimedeanRing) = ℝOCR._≤_
ArchimedeanRingStr.ι (snd ℝArchimedeanRing) = ℝRing.fromℤ
ArchimedeanRingStr.isArchimedeanRing (snd ℝArchimedeanRing) =
  isArchimedeanRingℝ


ι-pos≡fromNatℝ : ∀ n →
  ArchimedeanRingStr.ι (snd ℝArchimedeanRing) (pos n) ≡
    ℕ.HasFromNat.fromNat fromNatℝ n {{tt}}
ι-pos≡fromNatℝ = fromℕ≡fromNat
