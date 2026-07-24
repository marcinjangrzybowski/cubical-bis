module Cubical.HITs.CauchyReals.Complex.Algebra.PowerPreservation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ


opaque
  preserves-iterated-powers :
    (A B : Type₀) →
    (oneA : A) → (oneB : B) →
    (_mulA_ : A → A → A) →
    (_mulB_ : B → B → B) →
    (powerA : A → ℕ → A) →
    (powerB : B → ℕ → B) →
    (f : A → B) →
    ((x : A) → powerA x zero ≡ oneA) →
    ((x : A) (n : ℕ) →
      powerA x (suc n) ≡ x mulA powerA x n) →
    ((x : B) → powerB x zero ≡ oneB) →
    ((x : B) (n : ℕ) →
      powerB x (suc n) ≡ x mulB powerB x n) →
    f oneA ≡ oneB →
    ((x y : A) → f (x mulA y) ≡ f x mulB f y) →
    (x : A) → (n : ℕ) →
    f (powerA x n) ≡ powerB (f x) n
  preserves-iterated-powers
    A B oneA oneB _mulA_ _mulB_ powerA powerB f
    powerA-zero powerA-suc powerB-zero powerB-suc
    f-one f-mul x zero =
      cong f (powerA-zero x)
      ∙ f-one
      ∙ sym (powerB-zero (f x))
  preserves-iterated-powers
    A B oneA oneB _mulA_ _mulB_ powerA powerB f
    powerA-zero powerA-suc powerB-zero powerB-suc
    f-one f-mul x (suc n) =
      cong f (powerA-suc x n)
      ∙ f-mul x (powerA x n)
      ∙ cong (f x mulB_)
          (preserves-iterated-powers
            A B oneA oneB _mulA_ _mulB_ powerA powerB f
            powerA-zero powerA-suc powerB-zero powerB-suc
            f-one f-mul x n)
      ∙ sym (powerB-suc (f x) n)
