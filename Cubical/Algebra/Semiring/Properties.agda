module Cubical.Algebra.Semiring.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_)

open import Cubical.Algebra.Semiring.Base

private
  variable
    ℓ : Level

module ExponentiationLaws
  (R' : Semiring ℓ)
  (_^_ : fst R' → ℕ → fst R')
  (^zero : (f : fst R') →
    f ^ zero ≡ SemiringStr.1r (snd R'))
  (^suc : (f : fst R') (n : ℕ) →
    f ^ suc n ≡ SemiringStr._·_ (snd R') f (f ^ n))
  where
  open SemiringStr (snd R')

  ·-of-^-is-^-of-+ : (f : fst R') (m n : ℕ) →
    (f ^ m) · (f ^ n) ≡ f ^ (m +ℕ n)
  ·-of-^-is-^-of-+ f zero n =
    cong (_· (f ^ n)) (^zero f) ∙ ·IdL _
  ·-of-^-is-^-of-+ f (suc m) n =
    cong (_· (f ^ n)) (^suc f m)
      ∙ sym (·Assoc _ _ _)
      ∙ cong (f ·_) (·-of-^-is-^-of-+ f m n)
      ∙ sym (^suc f (m +ℕ n))

module Exponentiation (R' : Semiring ℓ) where
  open SemiringStr (snd R')

  private
    R = fst R'

  _^_ : R → ℕ → R
  f ^ zero = 1r
  f ^ suc n = f · (f ^ n)

  infix 9 _^_

  module Laws =
    ExponentiationLaws R' _^_ (λ _ → refl) (λ _ _ → refl)

  open Laws public

  1ⁿ≡1 : (n : ℕ) → 1r ^ n ≡ 1r
  1ⁿ≡1 zero = refl
  1ⁿ≡1 (suc n) = ·IdL _ ∙ 1ⁿ≡1 n
