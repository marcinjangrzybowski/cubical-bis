module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Sum where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Positive
open import Cubical.HITs.CauchyReals.Complex.Modulus.ReverseTriangle
open import Cubical.HITs.CauchyReals.Complex.Inverse
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Convergence
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Inverse
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Modulus


private
  contractionGap :
    (q : ℚ₊) → fst q ℚ.< 1 → ℚ₊
  contractionGap q q<1 =
    ℚ.<→ℚ₊ (fst q) 1 q<1


  contractionApart :
    (z : ℂ) → (q : ℚ₊) →
    (modulus<q : modulus z <ᵣ rat (fst q)) →
    (q<1 : fst q ℚ.< 1) →
    0ℂ #ℂ (1ℂ -ℂ z)
  contractionApart z q modulus<q q<1 =
    geometricOneMinusApart z
      (rationalContractionBound→modulus<1
        z (q , modulus<q , q<1))


  opaque
    contractionInverse :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      ℂ
    contractionInverse z q modulus<q q<1 =
      invℂ (1ℂ -ℂ z)
        (contractionApart z q modulus<q q<1)


    contractionInverse-path :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      contractionInverse z q modulus<q q<1 ≡
      invℂ (1ℂ -ℂ z)
        (contractionApart z q modulus<q q<1)
    contractionInverse-path z q modulus<q q<1 =
      refl


  opaque
    contractionPower : ℂ → ℕ → ℂ
    contractionPower z n = z ^ℂ n


    contractionPower-path : (z : ℂ) → (n : ℕ) →
      contractionPower z n ≡ z ^ℂ n
    contractionPower-path z n = refl


  opaque
    contractionPowerTimesInverse :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      ℕ → ℂ
    contractionPowerTimesInverse
      z q modulus<q q<1 n =
      contractionPower z n ·ℂ
      contractionInverse z q modulus<q q<1


    contractionPowerTimesInverse-unfold :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      contractionPowerTimesInverse
        z q modulus<q q<1 n ≡
      contractionPower z n ·ℂ
      contractionInverse z q modulus<q q<1
    contractionPowerTimesInverse-unfold
      z q modulus<q q<1 n =
      refl


    contractionPowerTimesInverse-path :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      contractionPowerTimesInverse
        z q modulus<q q<1 n ≡
      (z ^ℂ n) ·ℂ
      contractionInverse z q modulus<q q<1
    contractionPowerTimesInverse-path
      z q modulus<q q<1 n =
      contractionPowerTimesInverse-unfold
        z q modulus<q q<1 n
      ∙ cong
          (_·ℂ contractionInverse z q modulus<q q<1)
          (contractionPower-path z n)


  opaque
    contractionGapPath :
      (q : ℚ₊) → (q<1 : fst q ℚ.< 1) →
      1 -ᵣ rat (fst q) ≡
      rat (fst (contractionGap q q<1))
    contractionGapPath q q<1 =
      cong₂ _+ᵣ_
        refl
        (-ᵣ-rat (fst q))
      ∙ +ᵣ-rat 1 (ℚ.- fst q)


  opaque
    contractionGapBelowOneMinusModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      rat (fst (contractionGap q q<1)) <ᵣ
      modulus 1ℂ -ᵣ modulus z
    contractionGapBelowOneMinusModulus
      z q modulus<q q<1 =
      let
        beforeModulusOne :
          rat (fst (contractionGap q q<1)) <ᵣ
          1 -ᵣ modulus z
        beforeModulusOne =
          subst
            (_<ᵣ 1 -ᵣ modulus z)
            (contractionGapPath q q<1)
            (<ᵣ-o+
              (-ᵣ rat (fst q))
              (-ᵣ modulus z)
              1
              (-ᵣ<ᵣ
                (modulus z)
                (rat (fst q))
                modulus<q))
      in
      subst
        (rat (fst (contractionGap q q<1)) <ᵣ_)
        (cong (_-ᵣ modulus z) (sym modulus1))
        beforeModulusOne


  opaque
    contractionGapBelowDifferenceModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      rat (fst (contractionGap q q<1)) <ᵣ
      modulus (1ℂ -ℂ z)
    contractionGapBelowDifferenceModulus
      z q modulus<q q<1 =
      isTrans<≤ᵣ _ _ _
        (contractionGapBelowOneMinusModulus
          z q modulus<q q<1)
        (modulus-reverse-triangle 1ℂ z)


  opaque
    contractionDifferenceInverseModulusOne :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      modulus (1ℂ -ℂ z) ·ᵣ
        modulus
          (invℂ (1ℂ -ℂ z)
            (contractionApart z q modulus<q q<1)) ≡
      1
    contractionDifferenceInverseModulusOne
      z q modulus<q q<1 =
      let
        difference = 1ℂ -ℂ z
        apart = contractionApart z q modulus<q q<1
      in
      sym
        (modulus-mul
          difference
          (invℂ difference apart))
      ∙ cong modulus
          (·invℂ difference apart)
      ∙ modulus1


  opaque
    strictTimesPositiveToOne :
      (a b c : ℝ) →
      0 <ᵣ c →
      a <ᵣ b →
      b ·ᵣ c ≡ 1 →
      a ·ᵣ c <ᵣ 1
    strictTimesPositiveToOne a b c 0<c a<b bc≡1 =
      isTrans<≡ᵣ _ _ _
        (<ᵣ-·ᵣo
          a b
          (c , 0<c)
          a<b)
        bc≡1


  opaque
    contractionInverseApart :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      0ℂ #ℂ contractionInverse z q modulus<q q<1
    contractionInverseApart z q modulus<q q<1 =
      subst
        (0ℂ #ℂ_)
        (sym
          (contractionInverse-path
            z q modulus<q q<1))
        (0#invℂ
          (1ℂ -ℂ z)
          (contractionApart z q modulus<q q<1))


  opaque
    contractionInverseModulusPositive :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      0 <ᵣ
        modulus
          (contractionInverse z q modulus<q q<1)
    contractionInverseModulusPositive
      z q modulus<q q<1 =
      0#ℂ→0<modulus
        (contractionInverseApart
          z q modulus<q q<1)


  opaque
    contractionDifferenceTimesInverseModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      modulus (1ℂ -ℂ z) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1) ≡
      1
    contractionDifferenceTimesInverseModulus
      z q modulus<q q<1 =
      subst
        (λ inverse →
          modulus (1ℂ -ℂ z) ·ᵣ modulus inverse ≡ 1)
        (sym
          (contractionInverse-path
            z q modulus<q q<1))
        (contractionDifferenceInverseModulusOne
          z q modulus<q q<1)


  opaque
    contractionGapTimesAliasInverseModulusBelowOne :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      rat (fst (contractionGap q q<1)) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1) <ᵣ
      1
    contractionGapTimesAliasInverseModulusBelowOne
      z q modulus<q q<1 =
      strictTimesPositiveToOne
        (rat (fst (contractionGap q q<1)))
        (modulus (1ℂ -ℂ z))
        (modulus
          (contractionInverse z q modulus<q q<1))
        (contractionInverseModulusPositive
          z q modulus<q q<1)
        (contractionGapBelowDifferenceModulus
          z q modulus<q q<1)
        (contractionDifferenceTimesInverseModulus
          z q modulus<q q<1)


  opaque
    scaledByGapBelow :
      (x c : ℝ) → (ε gap : ℚ₊) →
      0 <ᵣ c →
      x <ᵣ rat (fst (ε ·₊ gap)) →
      rat (fst gap) ·ᵣ c <ᵣ 1 →
      x ·ᵣ c <ᵣ rat (fst ε)
    scaledByGapBelow x c ε gap 0<c x<εgap gapc<1 =
      let
        first :
          x ·ᵣ c <ᵣ
          rat (fst (ε ·₊ gap)) ·ᵣ c
        first =
          <ᵣ-·ᵣo
            x
            (rat (fst (ε ·₊ gap)))
            (c , 0<c)
            x<εgap

        productPath :
          rat (fst (ε ·₊ gap)) ·ᵣ c ≡
          rat (fst ε) ·ᵣ
            (rat (fst gap) ·ᵣ c)
        productPath =
          cong (_·ᵣ c)
            (rat·ᵣrat
              (fst ε)
              (fst gap))
          ∙ sym
              (·ᵣAssoc
                (rat (fst ε))
                (rat (fst gap))
                c)

        second :
          rat (fst (ε ·₊ gap)) ·ᵣ c <ᵣ
          rat (fst ε)
        second =
          isTrans<≡ᵣ _ _ _
            (isTrans≡<ᵣ _ _ _
              productPath
              (<ᵣ-o·ᵣ
                (rat (fst gap) ·ᵣ c)
                1
                (ℚ₊→ℝ₊ ε)
                gapc<1))
            (Rℝ.·IdR (rat (fst ε)))
      in
      isTrans<ᵣ _ _ _
        first
        second


  opaque
    contractionPartialSumInverseActualProductError :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      partialSumℂ (geometricTerms z) n -ℂ
        contractionInverse z q modulus<q q<1 ≡
      -ℂ
        ((z ^ℂ n) ·ℂ
         contractionInverse z q modulus<q q<1)
    contractionPartialSumInverseActualProductError
      z q modulus<q q<1 n =
      subst
        (λ inverse →
          partialSumℂ (geometricTerms z) n -ℂ inverse ≡
          -ℂ ((z ^ℂ n) ·ℂ inverse))
        (sym
          (contractionInverse-path
            z q modulus<q q<1))
        (geometricPartialSum-inverse-error
          z n
          (rationalContractionBound→modulus<1
            z (q , modulus<q , q<1)))


  opaque
    contractionPartialSumInverseError :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      partialSumℂ (geometricTerms z) n -ℂ
        contractionInverse z q modulus<q q<1 ≡
      -ℂ
        (contractionPowerTimesInverse
          z q modulus<q q<1 n)
    contractionPartialSumInverseError
      z q modulus<q q<1 n =
      subst
        (λ product →
          partialSumℂ (geometricTerms z) n -ℂ
            contractionInverse z q modulus<q q<1 ≡
          -ℂ product)
        (sym
          (contractionPowerTimesInverse-path
            z q modulus<q q<1 n))
        (contractionPartialSumInverseActualProductError
          z q modulus<q q<1 n)


  opaque
    contractionErrorModulusToNegatedProduct :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus
        (partialSumℂ (geometricTerms z) n -ℂ
         contractionInverse z q modulus<q q<1) ≡
      modulus
        (-ℂ
          (contractionPowerTimesInverse
            z q modulus<q q<1 n))
    contractionErrorModulusToNegatedProduct
      z q modulus<q q<1 n =
      cong modulus
        (contractionPartialSumInverseError
          z q modulus<q q<1 n)


  opaque
    contractionNegatedProductModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus
        (-ℂ
          (contractionPowerTimesInverse
            z q modulus<q q<1 n)) ≡
      modulus
        (contractionPowerTimesInverse
          z q modulus<q q<1 n)
    contractionNegatedProductModulus
      z q modulus<q q<1 n =
      modulus-neg
        (contractionPowerTimesInverse
          z q modulus<q q<1 n)


  opaque
    contractionProductAliasModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus
        (contractionPowerTimesInverse
          z q modulus<q q<1 n) ≡
      modulus
        (contractionPower z n ·ℂ
         contractionInverse z q modulus<q q<1)
    contractionProductAliasModulus
      z q modulus<q q<1 n =
      cong modulus
        (contractionPowerTimesInverse-unfold
          z q modulus<q q<1 n)


  opaque
    contractionNeutralProductModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus
        (contractionPower z n ·ℂ
         contractionInverse z q modulus<q q<1) ≡
      modulus (contractionPower z n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1)
    contractionNeutralProductModulus
      z q modulus<q q<1 n =
      modulus-mul
        (contractionPower z n)
        (contractionInverse z q modulus<q q<1)


  opaque
    contractionPowerAliasModulus :
      (z : ℂ) → (n : ℕ) →
      modulus (contractionPower z n) ≡
      modulus (z ^ℂ n)
    contractionPowerAliasModulus z n =
      cong modulus
        (contractionPower-path z n)


  opaque
    contractionActualPowerModulus :
      (z : ℂ) → (n : ℕ) →
      modulus (z ^ℂ n) ≡
      modulus z ^ⁿ n
    contractionActualPowerModulus z n =
      modulus-power z n


  opaque
    contractionPowerAliasFactorModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus (contractionPower z n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1) ≡
      modulus (z ^ℂ n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1)
    contractionPowerAliasFactorModulus
      z q modulus<q q<1 n =
      cong
        (_·ᵣ
          modulus
            (contractionInverse z q modulus<q q<1))
        (contractionPowerAliasModulus z n)


  opaque
    contractionPowerFactorModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus (z ^ℂ n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1) ≡
      (modulus z ^ⁿ n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1)
    contractionPowerFactorModulus
      z q modulus<q q<1 n =
      cong
        (_·ᵣ
          modulus
            (contractionInverse z q modulus<q q<1))
        (contractionActualPowerModulus z n)


  opaque
    contractionPartialSumInverseErrorModulus :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (n : ℕ) →
      modulus
        (partialSumℂ (geometricTerms z) n -ℂ
         contractionInverse z q modulus<q q<1) ≡
      (modulus z ^ⁿ n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1)
    contractionPartialSumInverseErrorModulus
      z q modulus<q q<1 n =
      contractionErrorModulusToNegatedProduct
        z q modulus<q q<1 n
      ∙ contractionNegatedProductModulus
          z q modulus<q q<1 n
      ∙ contractionProductAliasModulus
          z q modulus<q q<1 n
      ∙ contractionNeutralProductModulus
          z q modulus<q q<1 n
      ∙ contractionPowerAliasFactorModulus
          z q modulus<q q<1 n
      ∙ contractionPowerFactorModulus
          z q modulus<q q<1 n


  opaque
    contractionScaledPowerErrorBound :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      (ε : ℚ₊) → (n : ℕ) →
      modulus z ^ⁿ n <ᵣ
        rat
          (fst
            (ε ·₊ contractionGap q q<1)) →
      (modulus z ^ⁿ n) ·ᵣ
        modulus
          (contractionInverse z q modulus<q q<1) <ᵣ
      rat (fst ε)
    contractionScaledPowerErrorBound
      z q modulus<q q<1 ε n powerSmall =
      scaledByGapBelow
        (modulus z ^ⁿ n)
        (modulus
          (contractionInverse z q modulus<q q<1))
        ε
        (contractionGap q q<1)
        (contractionInverseModulusPositive
          z q modulus<q q<1)
        powerSmall
        (contractionGapTimesAliasInverseModulusBelowOne
          z q modulus<q q<1)


  opaque
    geometricSeriesConvergesToAliasInverse :
      (z : ℂ) → (q : ℚ₊) →
      (modulus<q : modulus z <ᵣ rat (fst q)) →
      (q<1 : fst q ℚ.< 1) →
      SeriesConvergesToℂ
        (geometricTerms z)
        (contractionInverse z q modulus<q q<1)
    geometricSeriesConvergesToAliasInverse
      z q modulus<q q<1 =
      let
        bound : RationalContractionBound z
        bound = q , modulus<q , q<1

        gap = contractionGap q q<1

        powersSmall :
          (ε : ℚ₊) →
          Σ[ N ∈ ℕ ]
            ((n : ℕ) → N ℕ.< n →
              modulus z ^ⁿ n <ᵣ
              rat (fst (ε ·₊ gap)))
        powersSmall ε =
          geometricPowersEventuallySmall
            z bound (ε ·₊ gap)
      in
      (λ ε → suc (fst (powersSmall ε))) ,
      λ ε n N≤n →
        subst
          (_<ᵣ rat (fst ε))
          (sym
            (contractionPartialSumInverseErrorModulus
              z q modulus<q q<1 n))
          (contractionScaledPowerErrorBound
            z q modulus<q q<1 ε n
            (snd (powersSmall ε) n N≤n))


opaque
  geometricSeriesSum :
    (z : ℂ) →
    RationalContractionBound z →
    ℂ
  geometricSeriesSum
    z (q , modulus<q , q<1) =
    contractionInverse z q modulus<q q<1


  geometricSeriesSum≡inverse :
    (z : ℂ) →
    (bound : RationalContractionBound z) →
    geometricSeriesSum z bound ≡
    invℂ (1ℂ -ℂ z)
      (geometricOneMinusApart z
        (rationalContractionBound→modulus<1
          z bound))
  geometricSeriesSum≡inverse
    z (q , modulus<q , q<1) =
    contractionInverse-path
      z q modulus<q q<1


opaque
  geometricSeriesConvergesToSum :
    (z : ℂ) →
    (bound : RationalContractionBound z) →
    SeriesConvergesToℂ
      (geometricTerms z)
      (geometricSeriesSum z bound)
  geometricSeriesConvergesToSum
    z bound@(q , modulus<q , q<1) =
    let
      aliasToSum :
        contractionInverse z q modulus<q q<1 ≡
        geometricSeriesSum z bound
      aliasToSum =
        contractionInverse-path
          z q modulus<q q<1
        ∙ sym
            (geometricSeriesSum≡inverse
              z bound)
    in
    subst
      (SeriesConvergesToℂ (geometricTerms z))
      aliasToSum
      (geometricSeriesConvergesToAliasInverse
        z q modulus<q q<1)


GeometricSeriesInverseFormula :
  (z : ℂ) →
  modulus z <ᵣ 1 →
  Type₀
GeometricSeriesInverseFormula z modulus<1 =
  Σ[ sum ∈ ℂ ]
    ((SeriesConvergesToℂ
        (geometricTerms z)
        sum)
    ×
    (sum ≡
       invℂ (1ℂ -ℂ z)
         (geometricOneMinusApart z modulus<1)))


geometricSeriesInverseFormulaTruncated :
  (z : ℂ) →
  (modulus<1 : modulus z <ᵣ 1) →
  ∥ GeometricSeriesInverseFormula z modulus<1 ∥₁
geometricSeriesInverseFormulaTruncated z modulus<1 =
  PT.map
    (λ bound →
      geometricSeriesSum z bound ,
      geometricSeriesConvergesToSum z bound ,
      geometricSeriesSum≡inverse z bound
      ∙ invℂ-proof-irrelevant
          (1ℂ -ℂ z)
          (geometricOneMinusApart z
            (rationalContractionBound→modulus<1
              z bound))
          (geometricOneMinusApart z modulus<1))
    (geometricContractionHasRationalBound
      z modulus<1)
