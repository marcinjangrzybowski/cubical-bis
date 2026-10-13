module Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData using (toℕ; toℕ<n)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Algebra.Cartesian as Cartesian
import Cubical.Analysis.Complex.Polar.Algebra as Polar
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra as Euler

-- Only finite algebra is generalized here. All factorial arithmetic and
-- infinite-series estimates remain the existing native real theorems.
module BinomialHom {ℓ} {R S : CommRing ℓ} (hom : CommRingHom R S) where
  private
    module RB = BinomialThm R
    module SB = BinomialThm S
  open IsCommRingHom (snd hom)

  opaque
    preservesBinomial : ∀ n k → fst hom (RB._choose_ n k) ≡ SB._choose_ n k
    preservesBinomial n zero = pres1
    preservesBinomial zero (suc k) = pres0
    preservesBinomial (suc n) (suc k) = pres+ (RB._choose_ n (suc k)) (RB._choose_ n k)
      ∙ cong₂ (CommRingStr._+_ (snd S)) (preservesBinomial n (suc k)) (preservesBinomial n k)

module FiniteAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private module S = Sum (CommRing→Ring R)
  private module E = Euler.EulerAlgebra R
  private module B = BinomialThm R
  private module C = CommRingTheory R
  open Exponentiation R

  opaque
    prefixSumToFinSum : (sum : (ℕ → fst R) → ℕ → fst R) →
      (∀ a → sum a zero ≡ 0r) →
      (∀ a n → sum a (suc n) ≡ a zero + sum (a ∘ suc) n) →
      ∀ a n → sum a n ≡ S.∑ {n = n} (a ∘ toℕ)
    prefixSumToFinSum sum base first a zero = base a
    prefixSumToFinSum sum base first a (suc n) = first a n
      ∙ cong (a zero +_) (prefixSumToFinSum sum base first (a ∘ suc) n)

    coefficientRearrange : ∀ c e x y → (c · e) · (x · y) ≡ e · ((c · x) · y)
    coefficientRearrange c e x y = solve! R

    cosPairRightScale : ∀ h a b x → E.cosPair h (a · x) (b · x) ≡ E.cosPair h a b · x
    cosPairRightScale h a b x = solve! R

    sinPairRightScale : ∀ h j a b x → E.sinPair h j (a · x) (b · x) ≡ E.sinPair h j a b · x
    sinPairRightScale h j a b x = solve! R

  opaque
    dividedPowerAddition : (coefficients : ℕ → fst R) →
      (∀ n k → k ℕ.≤ n → coefficients k · coefficients (n ∸ k) ≡ B._choose_ n k · coefficients n) →
      ∀ z w n → S.∑ {n = suc n}
        (λ k → (coefficients (toℕ k) · (z ^ toℕ k)) · (coefficients (n ∸ toℕ k) · (w ^ (n ∸ toℕ k))))
        ≡ coefficients n · ((z + w) ^ n)
    dividedPowerAddition coefficients product z w n = S.∑Ext
      (λ k → C.·CommAssocSwap (coefficients (toℕ k)) (z ^ toℕ k)
        (coefficients (n ∸ toℕ k)) (w ^ (n ∸ toℕ k))
        ∙ cong (_· ((z ^ toℕ k) · (w ^ (n ∸ toℕ k))))
            (product n (toℕ k) (ℕ.pred-≤-pred (toℕ<n k)))
        ∙ coefficientRearrange (B._choose_ n (toℕ k)) (coefficients n) (z ^ toℕ k) (w ^ (n ∸ toℕ k)))
      ∙ sym (S.∑Mulrdist (coefficients n) (B.BinomialVec n z w))
      ∙ cong (coefficients n ·_) (sym (B.BinomialThm n z w))

module ImaginaryPowers {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Cartesian.Cartesian R
  private module P = Exponentiation pairCommRing
  private module A = Polar.PolarAlgebra R

  opaque
    imaginaryPower : (c s : ℕ → fst R) → c zero ≡ 1r → s zero ≡ 0r →
      (∀ n → c (suc n) ≡ - s n) → (∀ n → s (suc n) ≡ c n) →
      ∀ n → P._^_ iℂ n ≡ (c n , s n)
    imaginaryPower c s cz sz cs ss zero = cong₂ _,_ (sym cz) (sym sz)
    imaginaryPower c s cz sz cs ss (suc n) =
      cong (iℂ ·ℂ_) (imaginaryPower c s cz sz cs ss n)
      ∙ A.quarterRotate (c n) (s n) ∙ cong₂ _,_ (sym (cs n)) (sym (ss n))
