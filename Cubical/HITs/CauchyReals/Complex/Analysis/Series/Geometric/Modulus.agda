module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Modulus where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.PowerPreservation


private
  complexPowerForModulus : ℂ → ℕ → ℂ
  complexPowerForModulus z n = z ^ℂ n


  realPowerForModulus : ℝ → ℕ → ℝ
  realPowerForModulus x n = x ^ⁿ n


  complexPowerForModulus-zero : (z : ℂ) →
    complexPowerForModulus z zero ≡ 1ℂ
  complexPowerForModulus-zero z = refl


  complexPowerForModulus-suc : (z : ℂ) → (n : ℕ) →
    complexPowerForModulus z (suc n) ≡
    z ·ℂ complexPowerForModulus z n
  complexPowerForModulus-suc z n = refl


  realPowerForModulus-zero : (x : ℝ) →
    realPowerForModulus x zero ≡ 1
  realPowerForModulus-zero x = refl


  realPowerForModulus-suc : (x : ℝ) → (n : ℕ) →
    realPowerForModulus x (suc n) ≡
    x ·ᵣ realPowerForModulus x n
  realPowerForModulus-suc x n = refl


  modulusPreservesOne : modulus 1ℂ ≡ 1
  modulusPreservesOne = modulus1


  modulusPreservesMultiplication : (z w : ℂ) →
    modulus (z ·ℂ w) ≡ modulus z ·ᵣ modulus w
  modulusPreservesMultiplication = modulus-mul


  modulus-power-raw : (z : ℂ) → (n : ℕ) →
    modulus (complexPowerForModulus z n) ≡
    realPowerForModulus (modulus z) n
  modulus-power-raw =
    preserves-iterated-powers
      ℂ ℝ
      1ℂ 1
      _·ℂ_ _·ᵣ_
      complexPowerForModulus
      realPowerForModulus
      modulus
      complexPowerForModulus-zero
      complexPowerForModulus-suc
      realPowerForModulus-zero
      realPowerForModulus-suc
      modulusPreservesOne
      modulusPreservesMultiplication


  complexPowerForModulus-path : (z : ℂ) → (n : ℕ) →
    complexPowerForModulus z n ≡ z ^ℂ n
  complexPowerForModulus-path z n = refl


  realPowerForModulus-path : (x : ℝ) → (n : ℕ) →
    realPowerForModulus x n ≡ x ^ⁿ n
  realPowerForModulus-path x n = refl


opaque
  modulus-power : (z : ℂ) → (n : ℕ) →
    modulus (z ^ℂ n) ≡ modulus z ^ⁿ n
  modulus-power z n =
    cong modulus (sym (complexPowerForModulus-path z n))
    ∙ modulus-power-raw z n
    ∙ realPowerForModulus-path (modulus z) n
