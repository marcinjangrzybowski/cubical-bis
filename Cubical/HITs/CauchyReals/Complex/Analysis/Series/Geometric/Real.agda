module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Geometric.Real where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication.Properties
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  (Seq; IsConvSeries')
open import Cubical.HITs.CauchyReals.Trigonometry.Pi using
  (ratioTest₊≤)


private
  one₊ : ℚ₊
  one₊ = 1


opaque
  positiveRationalGeometricConverges :
    (q : ℚ₊) → fst q ℚ.< 1 →
    IsConvSeries' (λ n → rat (fst q) ^ⁿ n)
  positiveRationalGeometricConverges q q<1 =
    let
      qᵣ = rat (fst q)

      qᵣPositive : 0 <ᵣ qᵣ
      qᵣPositive = snd (ℚ₊→ℝ₊ q)

      qᵣNonNegative : 0 ≤ᵣ qᵣ
      qᵣNonNegative = <ᵣWeaken≤ᵣ _ _ qᵣPositive

      qᵣ≤1 : qᵣ ≤ᵣ 1
      qᵣ≤1 =
        <ᵣWeaken≤ᵣ _ _
          (<ℚ→<ᵣ (fst q) 1 q<1)

      ratio : ℚ₊
      ratio = mean₊ q one₊

      q<ratio : fst q ℚ.< fst ratio
      q<ratio =
        <₊→<₊mean₊ q one₊ q<1

      ratio<1 : fst ratio ℚ.< 1
      ratio<1 =
        <₊→mean₊<₊ q one₊ q<1

      powersBounded :
        Σ[ b ∈ ℚ₊ ]
          ((n : ℕ) →
            absᵣ (qᵣ ^ⁿ n) ≤ᵣ rat (fst b))
      powersBounded =
        one₊ ,
        λ n →
          subst (_≤ᵣ 1)
            (sym
              (absᵣNonNeg
                (qᵣ ^ⁿ n)
                (0≤x^ⁿ qᵣ n qᵣNonNegative)))
            (^≤1 qᵣ qᵣNonNegative n qᵣ≤1)

      powersPositive : (n : ℕ) → 0 <ᵣ qᵣ ^ⁿ n
      powersPositive n = 0<x^ⁿ qᵣ n qᵣPositive

      ratioEventuallyBelow :
        Σ[ N ∈ ℕ ]
          ((n : ℕ) → N ℕ.< n →
            absᵣ
              ((qᵣ ^ⁿ (suc n)) ／ᵣ[
                qᵣ ^ⁿ n , inl (powersPositive n) ])
              <ᵣ rat (fst ratio))
      ratioEventuallyBelow =
        zero ,
        λ n _ →
          let
            quotientPath :
              (qᵣ ^ⁿ (suc n)) ／ᵣ[
                qᵣ ^ⁿ n , inl (powersPositive n) ] ≡ qᵣ
            quotientPath =
              [x·y]/yᵣ qᵣ (qᵣ ^ⁿ n)
                (inl (powersPositive n))

            absoluteQuotientPath :
              absᵣ
                ((qᵣ ^ⁿ (suc n)) ／ᵣ[
                  qᵣ ^ⁿ n , inl (powersPositive n) ]) ≡ qᵣ
            absoluteQuotientPath =
              cong absᵣ quotientPath
              ∙ absᵣPos qᵣ qᵣPositive
          in
          isTrans≡<ᵣ _ _ _
            absoluteQuotientPath
            (<ℚ→<ᵣ (fst q) (fst ratio) q<ratio)
    in
    ratioTest₊≤
      (λ n → qᵣ ^ⁿ n)
      powersBounded
      ratio
      ratio<1
      powersPositive
      ratioEventuallyBelow
