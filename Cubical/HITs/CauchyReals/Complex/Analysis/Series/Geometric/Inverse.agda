module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Inverse where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Positive
open import Cubical.HITs.CauchyReals.Complex.Modulus.ReverseTriangle
open import Cubical.HITs.CauchyReals.Complex.Inverse
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


private
  oneMinusModulusPositive : (z : ℂ) →
    modulus z <ᵣ 1 →
    0 <ᵣ modulus 1ℂ -ᵣ modulus z
  oneMinusModulusPositive z modulus<1 =
    subst (0 <ᵣ_)
      (cong (_-ᵣ modulus z) (sym modulus1))
      (x<y→0<y-x (modulus z) 1 modulus<1)


  oneMinusComplexModulusPositive : (z : ℂ) →
    modulus z <ᵣ 1 →
    0 <ᵣ modulus (1ℂ -ℂ z)
  oneMinusComplexModulusPositive z modulus<1 =
    isTrans<≤ᵣ _ _ _
      (oneMinusModulusPositive z modulus<1)
      (modulus-reverse-triangle 1ℂ z)


  opaque
    oneMinusForApartness : ℂ → ℂ
    oneMinusForApartness z = 1ℂ -ℂ z


    oneMinusForApartness-path : (z : ℂ) →
      oneMinusForApartness z ≡ 1ℂ -ℂ z
    oneMinusForApartness-path z = refl


opaque
  geometricOneMinusApart : (z : ℂ) →
    modulus z <ᵣ 1 →
    0ℂ #ℂ (1ℂ -ℂ z)
  geometricOneMinusApart z modulus<1 =
    let
      termPath =
        oneMinusForApartness-path z

      modulusPositiveForAlias :
        0 <ᵣ modulus (oneMinusForApartness z)
      modulusPositiveForAlias =
        subst (λ w → 0 <ᵣ modulus w)
          (sym termPath)
          (oneMinusComplexModulusPositive z modulus<1)

      apartForAlias :
        0ℂ #ℂ oneMinusForApartness z
      apartForAlias =
        0<modulus→0#ℂ modulusPositiveForAlias
    in
    subst (0ℂ #ℂ_)
      termPath
      apartForAlias


opaque
  geometricPartialSum-inverse-correction :
    (z : ℂ) → (n : ℕ) → (modulus<1 : modulus z <ᵣ 1) →
    partialSumℂ (geometricTerms z) n ≡
    (1ℂ -ℂ (z ^ℂ n)) ·ℂ
      invℂ (1ℂ -ℂ z)
        (geometricOneMinusApart z modulus<1)
  geometricPartialSum-inverse-correction z n modulus<1 =
    let
      difference = 1ℂ -ℂ z
      apart = geometricOneMinusApart z modulus<1
      inverse = invℂ difference apart
      sum = partialSumℂ (geometricTerms z) n
    in
    sym (·ℂIdR sum)
    ∙ cong (sum ·ℂ_)
        (sym (·invℂ difference apart))
    ∙ ·ℂAssoc sum difference inverse
    ∙ cong (_·ℂ inverse)
        (·ℂComm sum difference)
    ∙ cong (_·ℂ inverse)
        (geometricPartialSum z n)


private
  opaque
    inverseCorrectionErrorAlgebra : (power inverse : ℂ) →
      ((1ℂ -ℂ power) ·ℂ inverse) -ℂ inverse ≡
      -ℂ (power ·ℂ inverse)
    inverseCorrectionErrorAlgebra power inverse =
      ℂ≡ ℝ! ℝ!


opaque
  geometricPartialSum-inverse-error :
    (z : ℂ) → (n : ℕ) → (modulus<1 : modulus z <ᵣ 1) →
    partialSumℂ (geometricTerms z) n -ℂ
      invℂ (1ℂ -ℂ z)
        (geometricOneMinusApart z modulus<1) ≡
    -ℂ
      ((z ^ℂ n) ·ℂ
       invℂ (1ℂ -ℂ z)
         (geometricOneMinusApart z modulus<1))
  geometricPartialSum-inverse-error z n modulus<1 =
    cong
      (_-ℂ
        invℂ (1ℂ -ℂ z)
          (geometricOneMinusApart z modulus<1))
      (geometricPartialSum-inverse-correction
        z n modulus<1)
    ∙ inverseCorrectionErrorAlgebra
        (z ^ℂ n)
        (invℂ (1ℂ -ℂ z)
          (geometricOneMinusApart z modulus<1))
