module Cubical.Analysis.Complex.Algebra.Conjugation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Analysis.Complex.Algebra.Cartesian

module Conjugation {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Cartesian R
  private module Laws = Ring.RingTheory (CommRing→Ring R)

  conjugate : Pair → Pair
  conjugate (a , b) = a , - b

  conjugate-involutive : ∀ z → conjugate (conjugate z) ≡ z
  conjugate-involutive (a , b) = cong₂ _,_ refl (Laws.-Idempotent b)

  conjugate-pres+ : ∀ z w → conjugate (z +ℂ w) ≡ conjugate z +ℂ conjugate w
  conjugate-pres+ (a , b) (c , d) = cong₂ _,_ refl (sym (Laws.-Dist b d))

  conjugate-pres· : ∀ z w → conjugate (z ·ℂ w) ≡ conjugate z ·ℂ conjugate w
  conjugate-pres· (a , b) (c , d) = cong₂ _,_ (solve! R) (solve! R)

  conjugate-pres1 : conjugate 1ℂ ≡ 1ℂ
  conjugate-pres1 = cong₂ _,_ refl Laws.0Selfinverse

  normSq : Pair → fst R
  normSq (a , b) = a · a + b · b

  normSq-zero : normSq 0ℂ ≡ 0r
  normSq-zero = solve! R

  normSq-one : normSq 1ℂ ≡ 1r
  normSq-one = solve! R

  normSq-neg : ∀ z → normSq (-ℂ z) ≡ normSq z
  normSq-neg (a , b) = solve! R

  normSq-conjugate : ∀ z → normSq (conjugate z) ≡ normSq z
  normSq-conjugate (a , b) = solve! R

  normSq-mul : ∀ z w → normSq (z ·ℂ w) ≡ normSq z · normSq w
  normSq-mul (a , b) (c , d) = solve! R

  mul-conjugate : ∀ z → z ·ℂ conjugate z ≡ embed (normSq z)
  mul-conjugate (a , b) = cong₂ _,_ (solve! R) (solve! R)
