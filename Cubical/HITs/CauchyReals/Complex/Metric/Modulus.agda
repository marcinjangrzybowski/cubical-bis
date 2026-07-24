module Cubical.HITs.CauchyReals.Complex.Metric.Modulus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.ReverseTriangle
open import Cubical.HITs.CauchyReals.Complex.Metric.Base

opaque
  modulus-difference-bound : ∀ z w →
    absᵣ (modulus z -ᵣ modulus w) ≤ᵣ modulus (z -ℂ w)
  modulus-difference-bound z w =
    isTrans≡≤ᵣ _ _ _
      (abs-max (modulus z -ᵣ modulus w))
      (max≤-lem
        (modulus z -ᵣ modulus w)
        (-ᵣ (modulus z -ᵣ modulus w))
        (modulus (z -ℂ w))
        (modulus-reverse-triangle z w)
        (isTrans≡≤ᵣ _ _ _
          (-[x-y]≡y-x (modulus z) (modulus w))
          (isTrans≤≡ᵣ _ _ _
            (modulus-reverse-triangle w z)
            (modulus-difference-sym w z))))


opaque
  modulus-pres∼ : ∀ z w ε → z ≈ℂ[ ε ] w →
    modulus z ∼[ ε ] modulus w
  modulus-pres∼ z w ε z≈w =
    invEq (∼≃abs<ε (modulus z) (modulus w) ε)
      (isTrans≤<ᵣ _ _ _
        (modulus-difference-bound z w)
        z≈w)


opaque
  modulus-pres≈ : ∀ z w ε → z ≈ℂ[ ε ] w →
    modulus z ≈ℝ[ ε ] modulus w
  modulus-pres≈ z w ε z≈w =
    ∼→≈ℝ (modulus z) (modulus w) ε
      (modulus-pres∼ z w ε z≈w)


modulusIsNonExpanding :
  IsNonExpanding (snd ℂPremetricSpace) modulus (snd ℝPremetricSpace)
IsNonExpanding.pres≈ modulusIsNonExpanding = modulus-pres≈


modulusℂNE : NE[ ℂPremetricSpace , ℝPremetricSpace ]
modulusℂNE = modulus , modulusIsNonExpanding
