module Cubical.Analysis.Real.Series.Geometric.Rational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse as ℚInv
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

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
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Base

private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  module Pℝ = PremetricStr (ℝPremetricSpace .snd)
  module ℝTheory = PremetricTheory ℝPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


two₊ : ℚ₊
two₊ = ℚ.fromNat 2 , ℚ.0<sucN 1


halfℚ : ℚ
halfℚ = fst (two₊ ⁻¹₊)


halfℚPath : halfℚ ≡ [ pos 1 / 1+ 1 ]
halfℚPath = ℚInv.invℚ₊-fromNat 1


halfℚ<one : halfℚ ℚ.< 1
halfℚ<one =
  subst (ℚ._< 1) (sym halfℚPath) (ℚ.pos<pos tt)


halfContraction<one : ∀ q →
  q ℚ.≤ halfℚ → q ℚ.< 1
halfContraction<one q q≤half =
  ℚ.isTrans≤< q halfℚ 1 q≤half halfℚ<one


rationalGeometricGapPositive : ∀ q →
  q ℚ.≤ halfℚ → 0 ℚ.< 1 ℚ.- q
rationalGeometricGapPositive q q≤half =
  ℚOrder.<→0<Δ q 1
    (halfContraction<one q q≤half)


rationalGeometricPositiveDenominator : ∀ q →
  q ℚ.≤ halfℚ → 0ℝ <ℝ 1ℝ - rat q
rationalGeometricPositiveDenominator q q≤half =
  subst (0ℝ <ℝ_)
    (sym (sub-rat 1 q))
    (<ℚ→<ℝ 0 (1 ℚ.- q)
      (rationalGeometricGapPositive q q≤half))


rationalGeometricSum : ∀ q →
  q ℚ.≤ halfℚ → ℝ
rationalGeometricSum q q≤half =
  positiveReciprocal (1ℝ - rat q)
    (rationalGeometricPositiveDenominator q q≤half)


rationalGeometricSum-rat : ∀ q →
  (q≤half : q ℚ.≤ halfℚ) →
  rationalGeometricSum q q≤half ≡
  rat
    (fst
      (((1 ℚ.- q)
        , rationalGeometricGapPositive q q≤half) ⁻¹₊))
rationalGeometricSum-rat q q≤half =
  subst
    (λ x →
      (p : 0ℝ <ℝ x) →
      positiveReciprocal x p ≡
      rat (fst (gap₊ ⁻¹₊)))
    (sym (sub-rat 1 q))
    (positiveReciprocal-rat gap 0<gap)
    (rationalGeometricPositiveDenominator q q≤half)
  where
  gap : ℚ
  gap = 1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap = rationalGeometricGapPositive q q≤half

  gap₊ : ℚ₊
  gap₊ = gap , 0<gap


private
  powℚPath : ∀ q n →
    powℚ q n ≡ q ℚ.^ⁿ n
  powℚPath q ℕ.zero = refl
  powℚPath q (ℕ.suc n) =
    cong (q ℚ.·_) (powℚPath q n)

  rationalSubZero : ∀ q → q ℚ.- 0 ≡ q
  rationalSubZero q =
    cong (q ℚ.+_)
      (ℚ.·AnnihilR (ℚ.- 1))
    ∙ ℚ.+IdR q


rationalGeometricModulus : ℚ₊ → ℕ
rationalGeometricModulus ε =
  fst (ℚInv.1/2ⁿ<ε ε)


rationalGeometricPowerNonnegative : ∀ q →
  0 ℚ.≤ q → ∀ n → 0 ℚ.≤ powℚ q n
rationalGeometricPowerNonnegative q 0≤q n =
  subst (0 ℚ.≤_)
    (sym (powℚPath q n))
    (ℚOrder.powNonnegative q n 0≤q)


rationalGeometricPowerSmall : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  ∀ ε n →
  rationalGeometricModulus ε ℕ.≤ n →
  powℚ q n ℚ.< fst ε
rationalGeometricPowerSmall q 0≤q q≤half ε n modulus≤n =
  ℚ.isTrans≤<
    (powℚ q n)
    (powℚ halfℚ n)
    (fst ε)
    qPower≤halfPower
    halfPowerSmall
  where
  qPower≤halfPower :
    powℚ q n ℚ.≤ powℚ halfℚ n
  qPower≤halfPower =
    subst2 ℚ._≤_
      (sym (powℚPath q n))
      (sym (powℚPath halfℚ n))
      (ℚOrder.powMono n 0≤q q≤half)

  halfPowerPath :
    powℚ halfℚ n ≡
    [ pos 1 / 1+ 1 ] ℚ.^ⁿ n
  halfPowerPath =
    powℚPath halfℚ n
    ∙ cong (ℚ._^ⁿ n) halfℚPath

  modulusPowerSmall :
    [ pos 1 / 1+ 1 ] ℚ.^ⁿ
      rationalGeometricModulus ε
      ℚ.< fst ε
  modulusPowerSmall = snd (ℚInv.1/2ⁿ<ε ε)

  halfPowerAtModulusSmall :
    powℚ halfℚ (rationalGeometricModulus ε)
      ℚ.< fst ε
  halfPowerAtModulusSmall =
    subst (ℚ._< fst ε)
      (sym
        (powℚPath halfℚ (rationalGeometricModulus ε)
        ∙ cong (ℚ._^ⁿ rationalGeometricModulus ε)
            halfℚPath))
      modulusPowerSmall

  halfPowerSmall : powℚ halfℚ n ℚ.< fst ε
  halfPowerSmall =
    ℚ.isTrans≤<
      (powℚ halfℚ n)
      (powℚ halfℚ (rationalGeometricModulus ε))
      (fst ε)
      (subst2 ℚ._≤_
        (sym (powℚPath halfℚ n))
        (sym
          (powℚPath halfℚ
            (rationalGeometricModulus ε)))
        (ℚOrder.powExponentAntitone
          halfℚ
          (ℚ.<Weaken≤ 0 halfℚ
            (subst (0 ℚ.<_) (sym halfℚPath) (ℚ.pos<pos tt)))
          (ℚ.<Weaken≤ halfℚ 1 halfℚ<one)
          (rationalGeometricModulus ε) n modulus≤n))
      halfPowerAtModulusSmall


rationalGeometricPowerCloseZero : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  ∀ ε n →
  rationalGeometricModulus ε ℕ.≤ n →
  geometricTerms (rat q) n ∼[ ε ] 0ℝ
rationalGeometricPowerCloseZero
    q 0≤q q≤half ε n modulus≤n =
  subst2 (_∼[ ε ]_)
    (sym (pow-rat q n)) refl
    (rat-rat (powℚ q n) 0 ε
      (subst (ℚ._< fst ε)
        (sym absPowerPath)
        (rationalGeometricPowerSmall
          q 0≤q q≤half ε n modulus≤n)))
  where
  absPowerPath :
    ℚOrder.abs (powℚ q n ℚ.- 0) ≡ powℚ q n
  absPowerPath =
    cong ℚOrder.abs (rationalSubZero (powℚ q n))
    ∙ ℚOrder.0≤→abs≡id
        (powℚ q n)
        (rationalGeometricPowerNonnegative q 0≤q n)


rationalGeometricPowersTendToZero : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  isLimitSequence (geometricTerms (rat q)) 0ℝ
rationalGeometricPowersTendToZero
    q 0≤q q≤half ε =
  ∣ (rationalGeometricModulus ε
    , λ n modulus≤n →
        rationalGeometricPowerCloseZero
          q 0≤q q≤half ε n modulus≤n
    ) ∣₁


rationalGeometricPowersChosenCauchy : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  ChosenIsCauchySequence (geometricTerms (rat q))
rationalGeometricPowersChosenCauchy
    q 0≤q q≤half .fst ε =
  rationalGeometricModulus (ε /2₊)
rationalGeometricPowersChosenCauchy
    q 0≤q q≤half .snd
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
      (rationalGeometricPowerCloseZero
        q 0≤q q≤half (ε /2₊) m modulus≤m)
      (sym∼
        (geometricTerms (rat q) n) 0ℝ (ε /2₊)
        (rationalGeometricPowerCloseZero
          q 0≤q q≤half (ε /2₊) n modulus≤n)))


rationalGeometricPowersSeqWitness : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  SeqWitness (geometricTerms (rat q))
rationalGeometricPowersSeqWitness q 0≤q q≤half =
  ∣ rationalGeometricPowersChosenCauchy
      q 0≤q q≤half ∣₁


private
  oneMinusPowersChosenCauchy : ∀ q →
    (0≤q : 0 ℚ.≤ q) →
    (q≤half : q ℚ.≤ halfℚ) →
    ChosenIsCauchySequence
      (λ n → 1ℝ - geometricTerms (rat q) n)
  oneMinusPowersChosenCauchy
      q 0≤q q≤half .fst ε =
    rationalGeometricPowersChosenCauchy
      q 0≤q q≤half .fst (ε /2₊)
  oneMinusPowersChosenCauchy
      q 0≤q q≤half .snd
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
          (rationalGeometricPowersChosenCauchy
            q 0≤q q≤half .snd
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


rationalGeometricSeriesChosenCauchy : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  ChosenIsCauchySequence
    (partialSum (geometricTerms (rat q)))
rationalGeometricSeriesChosenCauchy q 0≤q q≤half =
  eventuallyEqualPresChosenCauchy
    candidate
    (partialSum (geometricTerms (rat q)))
    (0 , λ n _ → candidateEqualsPartial n)
    candidateChosenCauchy
  where
  gap : ℚ
  gap = 1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap = rationalGeometricGapPositive q q≤half

  gap₊ : ℚ₊
  gap₊ = gap , 0<gap

  positiveDenominator : 0ℝ <ℝ 1ℝ - rat q
  positiveDenominator =
    rationalGeometricPositiveDenominator q q≤half

  reciprocalPath :
    positiveReciprocal
      (1ℝ - rat q) positiveDenominator ≡
    rat (fst (gap₊ ⁻¹₊))
  reciprocalPath =
    rationalGeometricSum-rat q q≤half

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
      (oneMinusPowersChosenCauchy q 0≤q q≤half)

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


rationalGeometricSeriesIsCauchy : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  IsCauchySeries (geometricTerms (rat q))
rationalGeometricSeriesIsCauchy q 0≤q q≤half =
  ∣ rationalGeometricSeriesChosenCauchy
      q 0≤q q≤half ∣₁


rationalGeometricSeriesHasSum : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  HasSum (geometricTerms (rat q))
    (rationalGeometricSum q q≤half)
rationalGeometricSeriesHasSum q 0≤q q≤half =
  subst
    (λ sequence → isLimitSequence sequence reciprocal)
    (funExt candidateEqualsPartial)
    candidateLimit
  where
  positiveDenominator : 0ℝ <ℝ 1ℝ - rat q
  positiveDenominator =
    rationalGeometricPositiveDenominator q q≤half

  reciprocal : ℝ
  reciprocal = rationalGeometricSum q q≤half

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
        (rationalGeometricPowersTendToZero
          q 0≤q q≤half))

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


rationalGeometricSeriesSummable : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  Summable (geometricTerms (rat q))
rationalGeometricSeriesSummable q 0≤q q≤half =
  rationalGeometricSum q q≤half
  , rationalGeometricSeriesHasSum q 0≤q q≤half


seriesSum-rationalGeometric : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  (summable : Summable (geometricTerms (rat q))) →
  seriesSum (geometricTerms (rat q)) summable ≡
  rationalGeometricSum q q≤half
seriesSum-rationalGeometric q 0≤q q≤half summable =
  seriesSumIndependent
    (geometricTerms (rat q)) summable
    (rationalGeometricSeriesSummable q 0≤q q≤half)


seriesSum-rationalGeometric-rat : ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q≤half : q ℚ.≤ halfℚ) →
  (summable : Summable (geometricTerms (rat q))) →
  seriesSum (geometricTerms (rat q)) summable ≡
  rat
    (fst
      (((1 ℚ.- q)
        , rationalGeometricGapPositive q q≤half) ⁻¹₊))
seriesSum-rationalGeometric-rat
    q 0≤q q≤half summable =
  seriesSum-rationalGeometric
    q 0≤q q≤half summable
  ∙ rationalGeometricSum-rat q q≤half
