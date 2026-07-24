module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import
  Cubical.HITs.CauchyReals.Algebra.Order.Multiplication.Properties
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  ( Seq
  ; seqΣ
  ; IsCauchySequence'
  ; IsConvSeries'
  ; IsConvSeries'≃IsCauchySequence'Sum
  )

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Modulus
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Real


RationalContractionBound : ℂ → Type₀
RationalContractionBound z =
  Σ[ q ∈ ℚ₊ ]
    ((modulus z <ᵣ rat (fst q)) ×
     (fst q ℚ.< 1))


private
  geometricPowerTermsForConvergence : ℂ → ComplexSequence
  geometricPowerTermsForConvergence z n = z ^ℂ n


  geometricPowerTermsForConvergence-path : (z : ℂ) →
    geometricPowerTermsForConvergence z ≡
    (λ n → z ^ℂ n)
  geometricPowerTermsForConvergence-path z = refl


  geometricModulusPowers : ℂ → Seq
  geometricModulusPowers z n = modulus z ^ⁿ n


  rationalGeometricPowers : ℚ₊ → Seq
  rationalGeometricPowers q n = rat (fst q) ^ⁿ n


opaque
  geometricModulusSeriesConverges :
    (z : ℂ) →
    RationalContractionBound z →
    IsConvSeries' (geometricModulusPowers z)
  geometricModulusSeriesConverges z (q , modulus<q , q<1) =
    let
      modulusNonnegative : 0 ≤ᵣ modulus z
      modulusNonnegative = modulusNonNeg z

      rationalBoundPositive : 0 <ᵣ rat (fst q)
      rationalBoundPositive = snd (ℚ₊→ℝ₊ q)

      rationalBoundNonnegative : 0 ≤ᵣ rat (fst q)
      rationalBoundNonnegative =
        <ᵣWeaken≤ᵣ _ _ rationalBoundPositive
    in
    nonnegativeSeriesComparison
      (geometricModulusPowers z)
      (rationalGeometricPowers q)
      (λ n →
        0≤x^ⁿ (modulus z) n modulusNonnegative)
      (λ n →
        0≤x^ⁿ
          (rat (fst q)) n
          rationalBoundNonnegative)
      (λ n →
        ^ⁿ-Monotone n
          modulusNonnegative
          (<ᵣWeaken≤ᵣ _ _ modulus<q))
      (positiveRationalGeometricConverges q q<1)


private
  geometricPartialSumEqualityZero : Path ℝ 0 0
  geometricPartialSumEqualityZero = refl


  geometricPartialSumEqualityStep : (z : ℂ) → (n : ℕ) →
    seqΣ (λ k → modulus (z ^ℂ k)) n ≡
      seqΣ (λ k → modulus z ^ⁿ k) n →
    seqΣ (λ k → modulus (z ^ℂ k)) n +ᵣ
      modulus (z ^ℂ n) ≡
    seqΣ (λ k → modulus z ^ⁿ k) n +ᵣ
      modulus z ^ⁿ n
  geometricPartialSumEqualityStep z n previous =
    cong₂ _+ᵣ_
      previous
      (modulus-power z n)


  geometricAbsolutePartialSumZero : (z : ℂ) →
    absolutePartialSum (λ k → z ^ℂ k) zero ≡ 0
  geometricAbsolutePartialSumZero z = refl


  geometricPowerPartialSumZero : (z : ℂ) →
    seqΣ (geometricModulusPowers z) zero ≡ 0
  geometricPowerPartialSumZero z = refl


  geometricAbsolutePartialSumStep : (z : ℂ) → (n : ℕ) →
    absolutePartialSum (λ k → z ^ℂ k) (suc n) ≡
    absolutePartialSum (λ k → z ^ℂ k) n +ᵣ
      modulus (z ^ℂ n)
  geometricAbsolutePartialSumStep z n = refl


  geometricPowerPartialSumStep : (z : ℂ) → (n : ℕ) →
    seqΣ (geometricModulusPowers z) (suc n) ≡
    seqΣ (geometricModulusPowers z) n +ᵣ
      modulus z ^ⁿ n
  geometricPowerPartialSumStep z n = refl


  geometricAbsolutePartialSum-at-path : (z : ℂ) → (n : ℕ) →
    absolutePartialSum (λ k → z ^ℂ k) n ≡
    seqΣ (geometricModulusPowers z) n
  geometricAbsolutePartialSum-at-path z zero =
    subst2 _≡_
      (sym (geometricAbsolutePartialSumZero z))
      (sym (geometricPowerPartialSumZero z))
      geometricPartialSumEqualityZero
  geometricAbsolutePartialSum-at-path z (suc n) =
    subst2 _≡_
      (sym (geometricAbsolutePartialSumStep z n))
      (sym (geometricPowerPartialSumStep z n))
      (geometricPartialSumEqualityStep z n
        (geometricAbsolutePartialSum-at-path z n))

opaque
  geometricSeriesAbsolutelyConverges :
    (z : ℂ) →
    RationalContractionBound z →
    IsAbsolutelyConvergentSeriesℂ (λ n → z ^ℂ n)
  geometricSeriesAbsolutelyConverges z bound ε =
    let
      powersCauchy : IsCauchySequence'
        (seqΣ (geometricModulusPowers z))
      powersCauchy =
        fst
        (IsConvSeries'≃IsCauchySequence'Sum
          (geometricModulusPowers z))
        (geometricModulusSeriesConverges z bound)

      N = fst (powersCauchy ε)
    in
    N ,
    λ m n N<n N<m →
      isTrans≡<ᵣ _ _ _
        (cong absᵣ
          (cong₂ _-ᵣ_
            (geometricAbsolutePartialSum-at-path z n)
            (geometricAbsolutePartialSum-at-path z m)))
        (snd (powersCauchy ε) m n N<n N<m)


opaque
  geometricSeriesCauchy :
    (z : ℂ) →
    RationalContractionBound z →
    IsCauchySeriesℂ (λ n → z ^ℂ n)
  geometricSeriesCauchy z bound =
    let
      termsPath =
        geometricPowerTermsForConvergence-path z

      absoluteForAlias :
        IsAbsolutelyConvergentSeriesℂ
          (geometricPowerTermsForConvergence z)
      absoluteForAlias =
        subst IsAbsolutelyConvergentSeriesℂ
          (sym termsPath)
          (geometricSeriesAbsolutelyConverges z bound)

      cauchyForAlias :
        IsCauchySeriesℂ
          (geometricPowerTermsForConvergence z)
      cauchyForAlias =
        absoluteConvergence→cauchy
          (geometricPowerTermsForConvergence z)
          absoluteForAlias
    in
    subst IsCauchySeriesℂ
      termsPath
      cauchyForAlias


opaque
  geometricSeriesHasLimit :
    (z : ℂ) →
    RationalContractionBound z →
    HasComplexLimit (partialSumℂ (λ n → z ^ℂ n))
  geometricSeriesHasLimit z bound =
    let
      termsPath =
        geometricPowerTermsForConvergence-path z

      cauchyForAlias :
        IsCauchySeriesℂ
          (geometricPowerTermsForConvergence z)
      cauchyForAlias =
        subst IsCauchySeriesℂ
          (sym termsPath)
          (geometricSeriesCauchy z bound)

      limitForAlias :
        HasComplexLimit
          (partialSumℂ
            (geometricPowerTermsForConvergence z))
      limitForAlias =
        sumCauchySeries
          (geometricPowerTermsForConvergence z)
          cauchyForAlias
    in
    subst
      (λ terms →
        HasComplexLimit (partialSumℂ terms))
      termsPath
      limitForAlias


geometricContractionHasRationalBound :
  (z : ℂ) →
  modulus z <ᵣ 1 →
  ∥ RationalContractionBound z ∥₁
geometricContractionHasRationalBound z modulus<1 =
  PT.map
    (λ (q , modulus<q , q<1) →
      let
        q₊ : ℚ₊
        q₊ =
          q ,
          <ᵣ→<ℚ 0 q
            (isTrans≤<ᵣ _ _ _
              (modulusNonNeg z)
              modulus<q)
      in
      q₊ ,
      modulus<q ,
      <ᵣ→<ℚ q 1 q<1)
    (denseℚinℝ (modulus z) 1 modulus<1)


geometricSeriesAbsolutelyConvergesTruncated :
  (z : ℂ) →
  modulus z <ᵣ 1 →
  ∥ IsAbsolutelyConvergentSeriesℂ (λ n → z ^ℂ n) ∥₁
geometricSeriesAbsolutelyConvergesTruncated z modulus<1 =
  PT.map
    (geometricSeriesAbsolutelyConverges z)
    (geometricContractionHasRationalBound z modulus<1)


geometricSeriesCauchyTruncated :
  (z : ℂ) →
  modulus z <ᵣ 1 →
  ∥ IsCauchySeriesℂ (λ n → z ^ℂ n) ∥₁
geometricSeriesCauchyTruncated z modulus<1 =
  PT.map
    (geometricSeriesCauchy z)
    (geometricContractionHasRationalBound z modulus<1)


geometricSeriesHasLimitTruncated :
  (z : ℂ) →
  modulus z <ᵣ 1 →
  ∥ HasComplexLimit (partialSumℂ (λ n → z ^ℂ n)) ∥₁
geometricSeriesHasLimitTruncated z modulus<1 =
  PT.map
    (geometricSeriesHasLimit z)
    (geometricContractionHasRationalBound z modulus<1)
