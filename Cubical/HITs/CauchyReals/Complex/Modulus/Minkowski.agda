module Cubical.HITs.CauchyReals.Complex.Modulus.Minkowski where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative
open NonNegativeReals using (_+₀₊_)

open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle
open import Cubical.HITs.CauchyReals.Complex.Modulus.MinkowskiRaw


opaque
  minkowskiLeftPath : ∀ a b c d →
    modulus ((a , b) +ℂ (c , d)) ^ⁿ 2 ≡
      ((a +ᵣ c) ^ⁿ 2) +ᵣ ((b +ᵣ d) ^ⁿ 2)
  minkowskiLeftPath a b c d =
    x^²=x·x (modulus ((a , b) +ℂ (c , d)))
    ∙ modulusSq ((a , b) +ℂ (c , d))
    ∙ cong₂ _+ᵣ_
        (sym (x^²=x·x (a +ᵣ c)))
        (sym (x^²=x·x (b +ᵣ d)))


opaque
  minkowskiRootsPath : ∀ a b c d
    → (0≤a : 0 ≤ᵣ a) → (0≤b : 0 ≤ᵣ b)
    → (0≤c : 0 ≤ᵣ c) → (0≤d : 0 ≤ᵣ d)
    → modulus (a , b) +ᵣ modulus (c , d) ≡
      fst (nth-rootNonNeg 2
        (powerNorm (asNonNeg a 0≤a) (asNonNeg b 0≤b))) +ᵣ
      fst (nth-rootNonNeg 2
        (powerNorm (asNonNeg c 0≤c) (asNonNeg d 0≤d)))
  minkowskiRootsPath a b c d 0≤a 0≤b 0≤c 0≤d = cong₂ _+ᵣ_
    (modulus-to-power-root a b 0≤a 0≤b)
    (modulus-to-power-root c d 0≤c 0≤d)


opaque
  minkowskiSquare : ∀ a b c d
    → (0≤a : 0 ≤ᵣ a) → (0≤b : 0 ≤ᵣ b)
    → (0≤c : 0 ≤ᵣ c) → (0≤d : 0 ≤ᵣ d)
    → modulus ((a , b) +ℂ (c , d)) ^ⁿ 2 ≤ᵣ
      (modulus (a , b) +ᵣ modulus (c , d)) ^ⁿ 2
  minkowskiSquare a b c d 0≤a 0≤b 0≤c 0≤d =
    isTrans≡≤ᵣ _ _ _
      (minkowskiLeftPath a b c d)
      (isTrans≤≡ᵣ _ _ _
        (minkowskiSquaredRaw a b c d 0≤a 0≤b 0≤c 0≤d)
        (sym (cong (_^ⁿ 2)
          (minkowskiRootsPath a b c d 0≤a 0≤b 0≤c 0≤d))))


opaque
  modulusTriangleNonNeg : ∀ a b c d
    → 0 ≤ᵣ a → 0 ≤ᵣ b → 0 ≤ᵣ c → 0 ≤ᵣ d
    → modulus ((a , b) +ℂ (c , d)) ≤ᵣ modulus (a , b) +ᵣ modulus (c , d)
  modulusTriangleNonNeg a b c d 0≤a 0≤b 0≤c 0≤d =
    ^ⁿ-reflects-≤ 2 ℕ.zero-<-suc
      (modulusNonNeg ((a , b) +ℂ (c , d)))
      (snd ((modulus (a , b) , modulusNonNeg (a , b)) +₀₊
            (modulus (c , d) , modulusNonNeg (c , d))))
      (minkowskiSquare a b c d 0≤a 0≤b 0≤c 0≤d)
