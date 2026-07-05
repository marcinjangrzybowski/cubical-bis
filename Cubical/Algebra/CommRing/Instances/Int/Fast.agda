module Cubical.Algebra.CommRing.Instances.Int.Fast where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Int.Fast as Int renaming (_+_ to _+ℤ_; _·_ to _·ℤ_ ; -_ to -ℤ_)

open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_ ; isCommRing)

ℤCommRing : CommRing ℓ-zero
fst ℤCommRing = ℤ
0r (snd ℤCommRing) = pos 0
1r (snd ℤCommRing) = pos 1
_+_ (snd ℤCommRing) = _+ℤ_
_·_ (snd ℤCommRing) = _·ℤ_
- snd ℤCommRing = -ℤ_
isCommRing (snd ℤCommRing) = isCommRingℤ
  where
  abstract
    isCommRingℤ : IsCommRing (pos 0) (pos 1) _+ℤ_ _·ℤ_ -ℤ_
    isCommRingℤ = makeIsCommRing isSetℤ Int.+Assoc +IdR
                                 -Cancel Int.+Comm Int.·Assoc
                                 Int.·IdR ·DistR+ Int.·Comm

open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Nat hiding (_+_; _·_)
import Cubical.Data.Nat as ℕ

open CommRingStr using (0r ; 1r ; _+_ ; _·_ ; -_ ; isCommRing)


private
 variable
  ℓ : Level

module CanonicalHomFromℤ (ring : CommRing ℓ) where

  module R where
    open CommRingStr (snd ring) public
    open RingTheory (CommRing→Ring ring) public

  module 𝐙 = CommRingStr (snd ℤCommRing)

  suc-fromℕ : ∀ x → R.fromℕ (suc x) ≡ R.1r R.+ R.fromℕ x
  suc-fromℕ zero = sym (R.+IdR R.1r)
  suc-fromℕ (suc x) = refl


  fromℕ-pres-+ : (x y : ℕ) → R.fromℕ (x ℕ.+ y) ≡ R.fromℕ x R.+ R.fromℕ y
  fromℕ-pres-+ zero y = sym (R.+IdL _)
  fromℕ-pres-+ (suc zero) y = suc-fromℕ y
  fromℕ-pres-+ (suc (suc x)) y = cong (R.1r R.+_) (fromℕ-pres-+ (suc x) y) ∙ R.+Assoc _ _ _

  fromℤ-pres-minus : (x : ℤ) → R.fromℤ (-ℤ x) ≡ R.- R.fromℤ x
  fromℤ-pres-minus (pos zero) = sym R.0Selfinverse
  fromℤ-pres-minus (pos (suc n)) = refl
  fromℤ-pres-minus (negsuc n) = sym (R.-Idempotent _)

  suc-fromℤ : ∀ z → R.fromℤ (1 +ℤ z) ≡ R.1r R.+ R.fromℤ (z)
  suc-fromℤ (pos n) = suc-fromℕ n
  suc-fromℤ (negsuc zero) = sym (R.+InvR R.1r)
  suc-fromℤ (negsuc (suc n)) =
       sym (R.+IdL' _ _ (R.+InvR _))
    ∙∙ sym (R.+Assoc _ _ _)
    ∙∙ cong (R.1r R.+_) (R.-Dist _ _)

  fromℤ-pres-+' : (n n₁ : ℕ) →
    R.fromℤ (pos n +ℤ negsuc n₁) ≡
    R.fromℤ (pos n) R.+ R.fromℤ (negsuc n₁)
  fromℤ-pres-+' zero n₁ = sym (R.+IdL _)
  fromℤ-pres-+' (suc n) n₁ =
      (cong R.fromℤ (sym (𝐙.+Assoc 1 (pos n) (negsuc n₁)))
    ∙ suc-fromℤ (pos n +ℤ negsuc n₁))
    ∙∙ cong (R.1r R.+_) (fromℤ-pres-+' n n₁)
    ∙∙ R.+Assoc _ _ _
    ∙ cong (R._+ R.fromℤ (negsuc n₁))
     (sym (suc-fromℕ n))

  fromℤ-pres-+ : (x y : ℤ) → R.fromℤ (x +ℤ y) ≡ R.fromℤ x R.+ R.fromℤ y
  fromℤ-pres-+ (pos n)    (pos m)    = fromℕ-pres-+  n m
  fromℤ-pres-+ (pos n)    (negsuc m) = fromℤ-pres-+' n m
  fromℤ-pres-+ (negsuc n) (pos m)    = fromℤ-pres-+' m n ∙ R.+Comm _ _
  fromℤ-pres-+ (negsuc n) (negsuc m) =
      cong (R.-_)
      (cong (R.1r R.+_) (cong R.fromℕ (sym (ℕ.+-suc n m)))
        ∙ sym (suc-fromℕ (n ℕ.+ suc m))
        ∙ fromℕ-pres-+ (suc n) (suc m))
    ∙ sym (R.-Dist _ _)

  fromℕ-pres-· : (x y : ℕ) → R.fromℕ (x ℕ.· y) ≡ R.fromℕ x R.· R.fromℕ y
  fromℕ-pres-· zero y = sym (R.0LeftAnnihilates _)
  fromℕ-pres-· (suc x) y =
      fromℕ-pres-+ y (x ℕ.· y)
    ∙∙ cong₂ (R._+_) (sym (R.·IdL _)) (fromℕ-pres-· x y)
    ∙∙ sym (R.·DistL+ _ _ _)
    ∙ cong (R._· R.fromℕ y) (sym (suc-fromℕ x))
  fromℤ-pres-· : (x y : ℤ) → R.fromℤ (x ·ℤ y) ≡ R.fromℤ x R.· R.fromℤ y
  fromℤ-pres-· (pos n) (pos m) = fromℕ-pres-· n m
  fromℤ-pres-· (pos n) (negsuc m) =
      cong R.fromℤ (sym (-DistR· (pos n) (pos (suc m))))
    ∙∙ (fromℤ-pres-minus (pos (n ℕ.· suc m))
      ∙ cong R.-_ (fromℕ-pres-· n (suc m)))
    ∙∙ sym (R.-DistR· _ _)
  fromℤ-pres-· (negsuc n) (pos m) =
      cong R.fromℤ (sym (-DistL· (pos (suc n)) (pos m)))
    ∙∙ (fromℤ-pres-minus (pos ((suc n) ℕ.· m))
      ∙ cong R.-_ (fromℕ-pres-· (suc n) m))
    ∙∙ sym (R.-DistL· _ _)
  fromℤ-pres-· (negsuc n) (negsuc m) =
       fromℕ-pres-· (suc n) (suc m)
    ∙∙ cong₂ R._·_ (sym (R.-Idempotent _)) refl
    ∙∙ R.-Swap· _ _

  isHomFromℤ : IsCommRingHom (ℤCommRing .snd) R.fromℤ (ring .snd)
  isHomFromℤ .IsCommRingHom.pres0 = refl
  isHomFromℤ .IsCommRingHom.pres1 = refl
  isHomFromℤ .IsCommRingHom.pres+ = fromℤ-pres-+
  isHomFromℤ .IsCommRingHom.pres· = fromℤ-pres-·
  isHomFromℤ .IsCommRingHom.pres- = fromℤ-pres-minus

  fromℤCR : CommRingHom ℤCommRing ring
  fst fromℤCR = R.fromℤ
  snd fromℤCR = isHomFromℤ

  isContrHom[ℤCR,-] : isContr (CommRingHom ℤCommRing ring)
  fst isContrHom[ℤCR,-]   = fromℤCR
  snd isContrHom[ℤCR,-] φ = CommRingHom≡ (funExt fromℤ≡φ)
    where
      open IsCommRingHom (snd φ)

      fromℕ≡φ∘pos : ∀ n → R.fromℕ n ≡ φ $cr pos n
      fromℕ≡φ∘pos zero            = sym pres0
      fromℕ≡φ∘pos (suc zero)      = sym pres1
      fromℕ≡φ∘pos (suc k@(suc n)) =
        R.1r R.+ R.fromℕ k      ≡⟨ cong₂ R._+_ (sym pres1) (fromℕ≡φ∘pos k) ⟩
        φ $cr 1 R.+ φ $cr pos k ≡⟨ sym (pres+ 1 (pos k)) ⟩
        φ $cr pos (suc k)       ∎

      fromℤ≡φ : ∀ n → R.fromℤ n ≡ φ $cr n
      fromℤ≡φ (pos n)    = fromℕ≡φ∘pos n
      fromℤ≡φ (negsuc n) = cong R.-_ (fromℕ≡φ∘pos (suc n)) ∙ sym (pres- (pos (suc n)))

  record HasCanonicalHomFromℤ
    ⦃ fromNatR : HasFromNat (fst ring) ⦄
    ⦃ fromNegR : HasFromNeg (fst ring) ⦄ : Type ℓ where
   field
    fromNatIsCanonical : ∀ x ⦃ constr ⦄ → fromNat ⦃ fromNatR ⦄ x ⦃ constr ⦄ ≡ R.fromℤ (pos x) 
    fromNegIsCanonical : ∀ x ⦃ constr ⦄ → fromNeg ⦃ fromNegR ⦄ x ⦃ constr ⦄ ≡ R.fromℤ (negsuc x) 
