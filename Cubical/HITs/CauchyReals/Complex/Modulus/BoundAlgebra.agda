module Cubical.HITs.CauchyReals.Complex.Modulus.BoundAlgebra where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Modulus.Zero
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality
open import Cubical.HITs.CauchyReals.Complex.Modulus.Power


zeroComplexScalarBound : ComplexScalarBound 0ℂ
zeroComplexScalarBound =
  1 ,
  isTrans≡≤ᵣ _ _ _
    modulus0
    (<ᵣWeaken≤ᵣ _ _
      (snd (ℚ₊→ℝ₊ 1)))


oneComplexScalarBound : ComplexScalarBound 1ℂ
oneComplexScalarBound =
  1 , ≡ᵣWeaken≤ᵣ _ _ modulus1


complexScalarBound-neg :
  ∀ {z} →
  ComplexScalarBound z →
  ComplexScalarBound (-ℂ z)
complexScalarBound-neg {z} (M , |z|≤M) =
  M ,
  isTrans≡≤ᵣ _ _ _
    (modulus-neg z)
    |z|≤M


complexScalarBound-add :
  ∀ {z w} →
  ComplexScalarBound z →
  ComplexScalarBound w →
  ComplexScalarBound (z +ℂ w)
complexScalarBound-add
  {z} {w} (M , |z|≤M) (N , |w|≤N) =
  M +₊ N ,
  isTrans≤≡ᵣ _ _ _
    (isTrans≤ᵣ _ _ _
      (modulus-triangle z w)
      (≤ᵣMonotone+ᵣ _ _ _ _
        |z|≤M |w|≤N))
    (+ᵣ-rat (fst M) (fst N))


complexScalarBound-mul :
  ∀ {z w} →
  ComplexScalarBound z →
  ComplexScalarBound w →
  ComplexScalarBound (z ·ℂ w)
complexScalarBound-mul
  {z} {w} (M , |z|≤M) (N , |w|≤N) =
  M ·₊ N ,
  isTrans≡≤ᵣ _ _ _
    (modulus-mul z w)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣ₊Monotone·ᵣ
        (modulus z) (rat (fst M))
        (modulus w) (rat (fst N))
        (<ᵣWeaken≤ᵣ _ _
          (snd (ℚ₊→ℝ₊ M)))
        (modulusNonNeg w)
        |z|≤M |w|≤N)
      (sym (rat·ᵣrat (fst M) (fst N))))


complexScalarBound-power :
  ∀ z n →
  ComplexScalarBound z →
  ComplexScalarBound (z ^ℂ n)
complexScalarBound-power z n (M , |z|≤M) =
  M ℚ.ℚ₊^ⁿ n ,
  isTrans≡≤ᵣ _ _ _
    (modulus-power z n)
    (isTrans≤≡ᵣ _ _ _
      (^ⁿ-Monotone n
        (modulusNonNeg z)
        |z|≤M)
      (^ⁿ-ℚ^ⁿ n (fst M)))
