module Cubical.Analysis.Real.Series.Geometric.SignedRational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse as ℚInv
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Scalar
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.Rational


private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  module Pℝ = PremetricStr (ℝPremetricSpace .snd)
  module ℝTheory = PremetricTheory ℝPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


signedRationalQ≤Half : ∀ q →
  ℚOrder.abs q ℚ.≤ halfℚ →
  q ℚ.≤ halfℚ
signedRationalQ≤Half q absq≤half =
  ℚ.isTrans≤ q (ℚOrder.abs q) halfℚ
    (ℚOrder.≤abs q) absq≤half


signedRationalGeometricGapPositive : ∀ q →
  ℚOrder.abs q ℚ.≤ halfℚ →
  0 ℚ.< 1 ℚ.- q
signedRationalGeometricGapPositive q absq≤half =
  rationalGeometricGapPositive q
    (signedRationalQ≤Half q absq≤half)


signedRationalGeometricPositiveDenominator : ∀ q →
  ℚOrder.abs q ℚ.≤ halfℚ →
  0ℝ <ℝ 1ℝ - rat q
signedRationalGeometricPositiveDenominator q absq≤half =
  rationalGeometricPositiveDenominator q
    (signedRationalQ≤Half q absq≤half)


signedRationalGeometricSum : ∀ q →
  ℚOrder.abs q ℚ.≤ halfℚ → ℝ
signedRationalGeometricSum q absq≤half =
  rationalGeometricSum q
    (signedRationalQ≤Half q absq≤half)


signedRationalGeometricSum-rat : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  signedRationalGeometricSum q absq≤half ≡
  rat
    (fst
      (((1 ℚ.- q)
        , signedRationalGeometricGapPositive
            q absq≤half) ⁻¹₊))
signedRationalGeometricSum-rat q absq≤half =
  rationalGeometricSum-rat q
    (signedRationalQ≤Half q absq≤half)


private
  rationalSubZero : ∀ q → q ℚ.- 0 ≡ q
  rationalSubZero q =
    cong (q ℚ.+_)
      (ℚ.·AnnihilR (ℚ.- 1))
    ∙ ℚ.+IdR q


signedRationalAbsPower : ∀ q n →
  ℚOrder.abs (powℚ q n) ≡
  powℚ (ℚOrder.abs q) n
signedRationalAbsPower q ℕ.zero =
  ℚOrder.abs1
signedRationalAbsPower q (ℕ.suc n) =
  sym (ℚ.abs·abs q (powℚ q n))
  ∙ cong (ℚOrder.abs q ℚ.·_)
      (signedRationalAbsPower q n)


signedRationalGeometricPowerSmall : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  ∀ ε n →
  rationalGeometricModulus ε ℕ.≤ n →
  ℚOrder.abs (powℚ q n) ℚ.< fst ε
signedRationalGeometricPowerSmall
    q absq≤half ε n modulus≤n =
  subst (ℚ._< fst ε)
    (sym (signedRationalAbsPower q n))
    (rationalGeometricPowerSmall
      (ℚOrder.abs q)
      (ℚOrder.0≤abs q)
      absq≤half ε n modulus≤n)


signedRationalGeometricPowerCloseZero : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  ∀ ε n →
  rationalGeometricModulus ε ℕ.≤ n →
  geometricTerms (rat q) n ∼[ ε ] 0ℝ
signedRationalGeometricPowerCloseZero
    q absq≤half ε n modulus≤n =
  subst2 (_∼[ ε ]_)
    (sym (pow-rat q n)) refl
    (rat-rat (powℚ q n) 0 ε
      (subst (ℚ._< fst ε)
        (sym absDifferencePath)
        (signedRationalGeometricPowerSmall
          q absq≤half ε n modulus≤n)))
  where
  absDifferencePath :
    ℚOrder.abs (powℚ q n ℚ.- 0) ≡
    ℚOrder.abs (powℚ q n)
  absDifferencePath =
    cong ℚOrder.abs
      (rationalSubZero (powℚ q n))


signedRationalGeometricPowersTendToZero : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  isLimitSequence (geometricTerms (rat q)) 0ℝ
signedRationalGeometricPowersTendToZero
    q absq≤half ε =
  ∣ (rationalGeometricModulus ε
    , λ n modulus≤n →
        signedRationalGeometricPowerCloseZero
          q absq≤half ε n modulus≤n
    ) ∣₁


signedRationalGeometricPowersChosenCauchy : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  ChosenIsCauchySequence (geometricTerms (rat q))
signedRationalGeometricPowersChosenCauchy
    q absq≤half .fst ε =
  rationalGeometricModulus (ε /2₊)
signedRationalGeometricPowersChosenCauchy
    q absq≤half .snd
    ε m n modulus≤m modulus≤n =
  Pℝ.subst≈
    (geometricTerms (rat q) m)
    (geometricTerms (rat q) n)
    (/2+/2≡id (fst ε))
    (triangle∼
      (geometricTerms (rat q) m)
      0ℝ
      (geometricTerms (rat q) n)
      (ε /2₊) (ε /2₊)
      (signedRationalGeometricPowerCloseZero
        q absq≤half (ε /2₊) m modulus≤m)
      (sym∼
        (geometricTerms (rat q) n) 0ℝ (ε /2₊)
        (signedRationalGeometricPowerCloseZero
          q absq≤half (ε /2₊) n modulus≤n)))


signedRationalGeometricPowersSeqWitness : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  SeqWitness (geometricTerms (rat q))
signedRationalGeometricPowersSeqWitness q absq≤half =
  ∣ signedRationalGeometricPowersChosenCauchy
      q absq≤half ∣₁


private
  oneMinusSignedPowersChosenCauchy : ∀ q →
    (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
    ChosenIsCauchySequence
      (λ n → 1ℝ - geometricTerms (rat q) n)
  oneMinusSignedPowersChosenCauchy
      q absq≤half .fst ε =
    signedRationalGeometricPowersChosenCauchy
      q absq≤half .fst (ε /2₊)
  oneMinusSignedPowersChosenCauchy
      q absq≤half .snd
      ε m n modulus≤m modulus≤n =
    Pℝ.subst≈
      (1ℝ - geometricTerms (rat q) m)
      (1ℝ - geometricTerms (rat q) n)
      (/2+/2≡id (fst ε))
      (add-pres∼
        1ℝ 1ℝ
        (- geometricTerms (rat q) m)
        (- geometricTerms (rat q) n)
        (ε /2₊) (ε /2₊)
        (refl∼ 1ℝ (ε /2₊))
        (neg-isNonExpanding .IsNonExpanding.pres≈
          (geometricTerms (rat q) m)
          (geometricTerms (rat q) n)
          (ε /2₊)
          (signedRationalGeometricPowersChosenCauchy
            q absq≤half .snd
            (ε /2₊) m n modulus≤m modulus≤n)))

  scalarPresChosenCauchy : ∀ c sequence →
    ChosenIsCauchySequence sequence →
    ChosenIsCauchySequence ((c ⋆_) ∘ sequence)
  scalarPresChosenCauchy c sequence =
    LWith→presIsCauchySeq
      (rationalScalarBound c) (c ⋆_)
      (scalar-isLipschitzWith c) sequence

  eventuallyEqualPresChosenCauchy : ∀ a b →
    ℝTheory.EventuallyEqualSeq a b →
    ChosenIsCauchySequence a →
    ChosenIsCauchySequence b
  eventuallyEqualPresChosenCauchy a b =
    ℝTheory.eventuallyEqualSeqPresIsCauchySeq a b


signedRationalGeometricSeriesChosenCauchy : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  ChosenIsCauchySequence
    (partialSum (geometricTerms (rat q)))
signedRationalGeometricSeriesChosenCauchy q absq≤half =
  eventuallyEqualPresChosenCauchy
    candidate
    (partialSum (geometricTerms (rat q)))
    (0 , λ n _ → candidateEqualsPartial n)
    candidateChosenCauchy
  where
  q≤half : q ℚ.≤ halfℚ
  q≤half = signedRationalQ≤Half q absq≤half

  gap : ℚ
  gap = 1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap = signedRationalGeometricGapPositive q absq≤half

  gap₊ : ℚ₊
  gap₊ = gap , 0<gap

  positiveDenominator : 0ℝ <ℝ 1ℝ - rat q
  positiveDenominator =
    signedRationalGeometricPositiveDenominator q absq≤half

  reciprocalPath :
    positiveReciprocal
      (1ℝ - rat q) positiveDenominator ≡
    rat (fst (gap₊ ⁻¹₊))
  reciprocalPath =
    signedRationalGeometricSum-rat q absq≤half

  oneMinusPowers : RealSequence
  oneMinusPowers n =
    1ℝ - geometricTerms (rat q) n

  candidate : RealSequence
  candidate n =
    fst (gap₊ ⁻¹₊) ⋆ oneMinusPowers n

  candidateChosenCauchy :
    ChosenIsCauchySequence candidate
  candidateChosenCauchy =
    scalarPresChosenCauchy
      (fst (gap₊ ⁻¹₊)) oneMinusPowers
      (oneMinusSignedPowersChosenCauchy q absq≤half)

  candidateEqualsPartial : ∀ n →
    candidate n ≡
    partialSum (geometricTerms (rat q)) n
  candidateEqualsPartial n =
    scalar-as-mul (fst (gap₊ ⁻¹₊))
      (oneMinusPowers n)
    ∙ cong (_· oneMinusPowers n) (sym reciprocalPath)
    ∙ sym
        (geometricPartialSumByReciprocal
          (rat q) n positiveDenominator)


signedRationalGeometricSeriesIsCauchy : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  IsCauchySeries (geometricTerms (rat q))
signedRationalGeometricSeriesIsCauchy q absq≤half =
  ∣ signedRationalGeometricSeriesChosenCauchy
      q absq≤half ∣₁


signedRationalGeometricSeriesHasSum : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  HasSum (geometricTerms (rat q))
    (signedRationalGeometricSum q absq≤half)
signedRationalGeometricSeriesHasSum q absq≤half =
  subst
    (λ sequence → isLimitSequence sequence reciprocal)
    (funExt candidateEqualsPartial)
    candidateLimit
  where
  positiveDenominator : 0ℝ <ℝ 1ℝ - rat q
  positiveDenominator =
    signedRationalGeometricPositiveDenominator q absq≤half

  reciprocal : ℝ
  reciprocal = signedRationalGeometricSum q absq≤half

  oneMinusPowers : RealSequence
  oneMinusPowers n =
    1ℝ - geometricTerms (rat q) n

  oneMinusPowersLimit :
    isLimitSequence oneMinusPowers 1ℝ
  oneMinusPowersLimit =
    subst (isLimitSequence oneMinusPowers)
      (subZero 1ℝ)
      (subPresIsLimitSequence
        (constantIsLimitSequence 1ℝ)
        (signedRationalGeometricPowersTendToZero
          q absq≤half))

  candidate : RealSequence
  candidate n = reciprocal · oneMinusPowers n

  candidateLimit :
    isLimitSequence candidate reciprocal
  candidateLimit =
    subst (isLimitSequence candidate)
      (mulIdR reciprocal)
      (mulPresIsLimitSequence
        (constantIsLimitSequence reciprocal)
        oneMinusPowersLimit)

  candidateEqualsPartial : ∀ n →
    candidate n ≡
    partialSum (geometricTerms (rat q)) n
  candidateEqualsPartial n =
    sym
      (geometricPartialSumByReciprocal
        (rat q) n positiveDenominator)


signedRationalGeometricSeriesSummable : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  Summable (geometricTerms (rat q))
signedRationalGeometricSeriesSummable q absq≤half =
  signedRationalGeometricSum q absq≤half
  , signedRationalGeometricSeriesHasSum q absq≤half


seriesSum-signedRationalGeometric : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  (summable : Summable (geometricTerms (rat q))) →
  seriesSum (geometricTerms (rat q)) summable ≡
  signedRationalGeometricSum q absq≤half
seriesSum-signedRationalGeometric
    q absq≤half summable =
  seriesSumIndependent
    (geometricTerms (rat q)) summable
    (signedRationalGeometricSeriesSummable
      q absq≤half)


seriesSum-signedRationalGeometric-rat : ∀ q →
  (absq≤half : ℚOrder.abs q ℚ.≤ halfℚ) →
  (summable : Summable (geometricTerms (rat q))) →
  seriesSum (geometricTerms (rat q)) summable ≡
  rat
    (fst
      (((1 ℚ.- q)
        , signedRationalGeometricGapPositive
            q absq≤half) ⁻¹₊))
seriesSum-signedRationalGeometric-rat
    q absq≤half summable =
  seriesSum-signedRationalGeometric
    q absq≤half summable
  ∙ signedRationalGeometricSum-rat q absq≤half
