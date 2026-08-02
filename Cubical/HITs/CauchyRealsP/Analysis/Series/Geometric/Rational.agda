module Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ ; 1+_)
open import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order.Floor as ℚFloor
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
  as PT using (∣_∣₁)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import
  Cubical.HITs.CauchyRealsP.Analysis.Sequence.Cauchy
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  open OrderedCommRingReasoning ℚOrderedCommRing

  rationalNat : ℕ → ℚ
  rationalNat zero = 0
  rationalNat (suc n) =
    1 ℚ.+ rationalNat n

  rationalNatPath : ∀ n →
    rationalNat n ≡ ℚ.fromNat n
  rationalNatPath zero =
    refl
  rationalNatPath (suc n) =
    cong (1 ℚ.+_) (rationalNatPath n)
    ∙ ℚ.ℕ+→ℚ+ 1 n

  twoPositive : 0 ℚ.< 2
  twoPositive =
    ℚ.0<sucN 1

  two₊ : ℚ₊
  two₊ =
    ℚ.fromNat 2 , ℚ.0<sucN 1

  rationalSubZero : ∀ x →
    x ℚ.- 0 ≡ x
  rationalSubZero x =
    cong (x ℚ.+_)
      (ℚ.·AnnihilR (ℚ.- 1))
    ∙ ℚ.+IdR x

  rationalPowerFactorStep :
    ∀ q p coefficient →
    0 ℚ.≤ q →
    q ℚ.≤ 1 →
    0 ℚ.≤ p →
    p ℚ.≤ 1 →
    p ℚ.·
      (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q))
      ℚ.≤ 1 →
    q ℚ.· p
      ℚ.·
        (1 ℚ.+
          (1 ℚ.+ coefficient)
            ℚ.· (1 ℚ.- q))
      ℚ.≤ 1
  rationalPowerFactorStep
    q p coefficient 0≤q q≤1 0≤p p≤1 bound =
      begin≤
        q ℚ.· p
          ℚ.·
            (1 ℚ.+
              (1 ℚ.+ coefficient)
                ℚ.· (1 ℚ.- q))
          ≡→≤⟨ ℚ! ⟩
        q ℚ.·
            (p ℚ.·
              (1 ℚ.+
                coefficient ℚ.· (1 ℚ.- q)))
          ℚ.+
        (q ℚ.· p) ℚ.· (1 ℚ.- q)
          ≤⟨ ℚOrder.+Mono≤
              (q ℚ.·
                (p ℚ.·
                  (1 ℚ.+
                    coefficient
                      ℚ.· (1 ℚ.- q))))
              q
              ((q ℚ.· p) ℚ.· (1 ℚ.- q))
              (1 ℚ.- q)
              firstBound secondBound ⟩
        q ℚ.+ (1 ℚ.- q)
          ≡→≤⟨ ℚ! ⟩
        1
          ◾
    where
    0≤gap : 0 ℚ.≤ 1 ℚ.- q
    0≤gap =
      ℚOrder.≤→0≤Δ q 1 q≤1

    qp≤1 : q ℚ.· p ℚ.≤ 1
    qp≤1 =
      subst
        (q ℚ.· p ℚ.≤_)
        (ℚ.·IdR 1)
        (ℚOrder.·Mono≤
          q 1 p 1
          ℚOrder.0≤1 0≤p q≤1 p≤1)

    firstBound :
      q ℚ.·
        (p ℚ.·
          (1 ℚ.+
            coefficient ℚ.· (1 ℚ.- q)))
        ℚ.≤ q
    firstBound =
      subst
        (q ℚ.·
          (p ℚ.·
            (1 ℚ.+
              coefficient ℚ.· (1 ℚ.- q)))
          ℚ.≤_)
        (ℚ.·IdR q)
        (ℚOrder.·MonoL≤
          (p ℚ.·
            (1 ℚ.+
              coefficient ℚ.· (1 ℚ.- q)))
          1 q 0≤q bound)

    secondBound :
      (q ℚ.· p) ℚ.· (1 ℚ.- q)
        ℚ.≤ 1 ℚ.- q
    secondBound =
      subst
        ((q ℚ.· p) ℚ.· (1 ℚ.- q) ℚ.≤_)
        (ℚ.·IdL (1 ℚ.- q))
        (OrderedCommRingStr.·MonoR≤
          (snd ℚOrderedCommRing)
          (q ℚ.· p) 1 (1 ℚ.- q)
          0≤gap qp≤1)

rationalPowerFactorBound :
  ∀ q →
  0 ℚ.≤ q →
  q ℚ.≤ 1 →
  ∀ n →
  q ℚ.^ⁿ n
    ℚ.· (1 ℚ.+ rationalNat n ℚ.· (1 ℚ.- q))
    ℚ.≤ 1
rationalPowerFactorBound
  q 0≤q q≤1 zero =
    <≤ℚ!
rationalPowerFactorBound
  q 0≤q q≤1 (suc n) =
    rationalPowerFactorStep
      q (q ℚ.^ⁿ n) (rationalNat n)
      0≤q q≤1
      (ℚOrder.powNonnegative
        q n 0≤q)
      (ℚOrder.pow≤one
        q 0≤q n q≤1)
      (rationalPowerFactorBound
        q 0≤q q≤1 n)

rationalPowerFactorBoundFromNat :
  ∀ q →
  0 ℚ.≤ q →
  q ℚ.≤ 1 →
  ∀ n →
  q ℚ.^ⁿ n
    ℚ.·
      (1 ℚ.+ ℚ.fromNat n
        ℚ.· (1 ℚ.- q))
    ℚ.≤ 1
rationalPowerFactorBoundFromNat
  q 0≤q q≤1 n =
    subst
      (λ coefficient →
        q ℚ.^ⁿ n
          ℚ.·
            (1 ℚ.+ coefficient
              ℚ.· (1 ℚ.- q))
          ℚ.≤ 1)
      (rationalNatPath n)
      (rationalPowerFactorBound
        q 0≤q q≤1 n)

rationalPowerHasHalfBlock :
  ∀ q →
  0 ℚ.≤ q →
  q ℚ.< 1 →
  Σ[ block ∈ ℕ ]
    q ℚ.^ⁿ block ℚ.≤ fst (two₊ ⁻¹₊)
rationalPowerHasHalfBlock q 0≤q q<1 =
  block , power≤half
  where
  gap : ℚ
  gap =
    1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap =
    ℚOrder.<→0<Δ q 1 q<1

  gap₊ : ℚ₊
  gap₊ =
    gap , 0<gap

  block : ℕ
  block =
    ℕ₊₁→ℕ
      (fst (ℚFloor.ceilℚ₊ (gap₊ ⁻¹₊)))

  inverseGap<block :
    fst (gap₊ ⁻¹₊) ℚ.<
    ℚ.fromNat block
  inverseGap<block =
    snd (ℚFloor.ceilℚ₊ (gap₊ ⁻¹₊))

  one<blockTimesGap :
    1 ℚ.< ℚ.fromNat block ℚ.· gap
  one<blockTimesGap =
    subst
      (ℚ._< ℚ.fromNat block ℚ.· gap)
      (ℚInv.invℚ₊[x]·x gap₊)
      (OrderedCommRingStr.·MonoR<
        (snd ℚOrderedCommRing)
        (fst (gap₊ ⁻¹₊))
        (ℚ.fromNat block)
        gap 0<gap
        inverseGap<block)

  two≤factor :
    2 ℚ.≤
    1 ℚ.+ ℚ.fromNat block ℚ.· gap
  two≤factor =
    ℚ.<Weaken≤ 2
      (1 ℚ.+ ℚ.fromNat block ℚ.· gap)
      (subst
        (ℚ._<
          (1 ℚ.+
            ℚ.fromNat block ℚ.· gap))
        (ℚ.ℕ+→ℚ+ 1 1)
        (ℚOrder.+MonoL<
          1
          (ℚ.fromNat block ℚ.· gap)
          1 one<blockTimesGap))

  powerNonnegative :
    0 ℚ.≤ q ℚ.^ⁿ block
  powerNonnegative =
    ℚOrder.powNonnegative
      q block 0≤q

  twicePower≤one :
    q ℚ.^ⁿ block ℚ.· 2
      ℚ.≤ 1
  twicePower≤one =
    ℚ.isTrans≤
      (q ℚ.^ⁿ block ℚ.· 2)
      (q ℚ.^ⁿ block
        ℚ.·
          (1 ℚ.+
            ℚ.fromNat block ℚ.· gap))
      1
      (ℚOrder.·MonoL≤
        2
        (1 ℚ.+
          ℚ.fromNat block ℚ.· gap)
        (q ℚ.^ⁿ block)
        powerNonnegative
        two≤factor)
      (rationalPowerFactorBoundFromNat
        q 0≤q
        (ℚ.<Weaken≤ q 1 q<1)
        block)

  power≤half :
    q ℚ.^ⁿ block ℚ.≤ fst (two₊ ⁻¹₊)
  power≤half =
    ℚOrder.·CancelR≤
      (q ℚ.^ⁿ block)
      (fst (two₊ ⁻¹₊))
      2
      (snd two₊)
      (subst
        (q ℚ.^ⁿ block ℚ.· 2 ℚ.≤_)
        (sym (ℚInv.invℚ₊[x]·x two₊))
        twicePower≤one)

rationalPowerModulus :
  ∀ q →
  0 ℚ.≤ q →
  q ℚ.< 1 →
  ℚ₊ → ℕ
rationalPowerModulus q 0≤q q<1 ε =
  block ℕ.· exponent
  where
  block : ℕ
  block =
    fst
      (rationalPowerHasHalfBlock
        q 0≤q q<1)

  exponent : ℕ
  exponent =
    fst (ℚInv.1/2ⁿ<ε ε)

rationalPowerSmall :
  ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q<1 : q ℚ.< 1) →
  ∀ ε n →
  rationalPowerModulus q 0≤q q<1 ε
    ℕ.≤ n →
  q ℚ.^ⁿ n ℚ.< fst ε
rationalPowerSmall
  q 0≤q q<1 ε n modulus≤n =
    ℚ.isTrans≤<
      (q ℚ.^ⁿ n)
      (q ℚ.^ⁿ (block ℕ.· exponent))
      (fst ε)
      (ℚOrder.powExponentAntitone
        q 0≤q
        (ℚ.<Weaken≤ q 1 q<1)
        (block ℕ.· exponent) n
        modulus≤n)
      (ℚ.isTrans≤<
        (q ℚ.^ⁿ (block ℕ.· exponent))
        (fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent)
        (fst ε)
        blockPowerBound
        halfPowerSmall)
  where
  block : ℕ
  block =
    fst
      (rationalPowerHasHalfBlock
        q 0≤q q<1)

  blockBound :
    q ℚ.^ⁿ block ℚ.≤
    fst (two₊ ⁻¹₊)
  blockBound =
    snd
      (rationalPowerHasHalfBlock
        q 0≤q q<1)

  exponent : ℕ
  exponent =
    fst (ℚInv.1/2ⁿ<ε ε)

  halfPath :
    fst (two₊ ⁻¹₊) ≡
    [ pos 1 / 1+ 1 ]
  halfPath =
    ℚInv.invℚ₊-fromNat 1

  blockPowerBound :
    q ℚ.^ⁿ (block ℕ.· exponent)
      ℚ.≤
    fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent
  blockPowerBound =
    subst
      (ℚ._≤
        (fst (two₊ ⁻¹₊)
          ℚ.^ⁿ exponent))
      (sym
        (ℚOrder.^-rdist-·ℕ
          q block exponent))
      (ℚOrder.powMono
        exponent
        (ℚOrder.powNonnegative
          q block 0≤q)
        blockBound)

  halfPowerSmall :
    fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent
      ℚ.< fst ε
  halfPowerSmall =
    subst
      (λ base →
        base ℚ.^ⁿ exponent
          ℚ.< fst ε)
      (sym halfPath)
      (snd (ℚInv.1/2ⁿ<ε ε))

rationalGeometricPowerCloseZero :
  ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q<1 : q ℚ.< 1) →
  ∀ ε n →
  rationalPowerModulus q 0≤q q<1 ε
    ℕ.≤ n →
  geometricTerms (rat q) n ∼[ ε ] 0
rationalGeometricPowerCloseZero
  q 0≤q q<1 ε n modulus≤n =
    subst2
      (_∼[ ε ]_)
      (sym (pow-rat n q))
      refl
      (rat-rat-fromAbs
        (q ℚ.^ⁿ n) 0 ε
        (subst
          (ℚ._< fst ε)
          (sym absPowerPath)
          (rationalPowerSmall
            q 0≤q q<1 ε n modulus≤n)))
  where
  powerNonnegative :
    0 ℚ.≤ q ℚ.^ⁿ n
  powerNonnegative =
    ℚOrder.powNonnegative q n 0≤q

  absPowerPath :
    abs ((q ℚ.^ⁿ n) ℚ.- 0) ≡
    q ℚ.^ⁿ n
  absPowerPath =
    cong abs
      (rationalSubZero (q ℚ.^ⁿ n))
    ∙ ℚOrder.0≤→abs≡id
        (q ℚ.^ⁿ n)
        powerNonnegative

rationalGeometricPowersTendToZero :
  ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q<1 : q ℚ.< 1) →
  isLimitSeq (geometricTerms (rat q)) 0
rationalGeometricPowersTendToZero
  q 0≤q q<1 ε =
    ∣
      ( rationalPowerModulus q 0≤q q<1 ε
      , λ n modulus≤n →
          rationalGeometricPowerCloseZero
            q 0≤q q<1 ε n modulus≤n
      )
    ∣₁

rationalGeometricPowersAreCauchy :
  ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q<1 : q ℚ.< 1) →
  isCauchySeq (geometricTerms (rat q))
rationalGeometricPowersAreCauchy
  q 0≤q q<1 .fst ε =
    rationalPowerModulus
      q 0≤q q<1 (ε /2₊)
rationalGeometricPowersAreCauchy
  q 0≤q q<1 .snd
  ε m n modulus≤m modulus≤n =
    subst∼
      (geometricTerms (rat q) m)
      (geometricTerms (rat q) n)
      {ε = (ε /2₊) +₊ (ε /2₊)}
      {ε' = ε}
      (1/2∈ℚ./2+/2≡id (fst ε))
      (triangle∼
        (geometricTerms (rat q) m)
        0
        (geometricTerms (rat q) n)
        (ε /2₊) (ε /2₊)
        (rationalGeometricPowerCloseZero
          q 0≤q q<1 (ε /2₊)
          m modulus≤m)
        (sym∼
          (geometricTerms (rat q) n)
          0 (ε /2₊)
          (rationalGeometricPowerCloseZero
            q 0≤q q<1 (ε /2₊)
            n modulus≤n)))

rationalGeometricSeriesIsCauchy :
  ∀ q →
  (0≤q : 0 ℚ.≤ q) →
  (q<1 : q ℚ.< 1) →
  IsCauchySeries (geometricTerms (rat q))
rationalGeometricSeriesIsCauchy
  q 0≤q q<1 =
    eventuallyEqualSeqPresIsCauchySeq
      rationalCandidate
      (partialSum (geometricTerms (rat q)))
      ( 0
      , λ n _ →
          cong
            (_·
              (1 - geometricTerms (rat q) n))
            (sym reciprocalPath)
          ∙ sym
              (geometricPartialSumByReciprocal
                (rat q) n positiveDenominator)
      )
      rationalCandidateCauchy
  where
  gap : ℚ
  gap =
    1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap =
    ℚOrder.<→0<Δ q 1 q<1

  gap₊ : ℚ₊
  gap₊ =
    gap , 0<gap

  denominatorPath :
    1 - rat q ≡ rat gap
  denominatorPath =
    sub-rat 1 q

  positiveRationalGap :
    0 <ℝ rat gap
  positiveRationalGap =
    <ℚ→<ℝ 0 gap 0<gap

  positiveDenominator :
    0 <ℝ 1 - rat q
  positiveDenominator =
    subst
      (0 <ℝ_)
      (sym denominatorPath)
      positiveRationalGap

  reciprocalPath :
    positiveReciprocal
      (1 - rat q) positiveDenominator
      ≡
    rat (fst (gap₊ ⁻¹₊))
  reciprocalPath =
    subst
      (λ x →
        (p : 0 <ℝ x) →
        positiveReciprocal x p ≡
        rat (fst (gap₊ ⁻¹₊)))
      (sym denominatorPath)
      (positiveReciprocal-rat
        gap 0<gap)
      positiveDenominator

  oneMinusPowers : RealSequence
  oneMinusPowers n =
    1 - geometricTerms (rat q) n

  oneMinusPowersCauchy :
    isCauchySeq oneMinusPowers
  oneMinusPowersCauchy =
    subPresIsCauchySeq
      (λ _ → 1)
      (geometricTerms (rat q))
      (constantIsCauchySeq 1)
      (rationalGeometricPowersAreCauchy
        q 0≤q q<1)

  rationalCandidate : RealSequence
  rationalCandidate n =
    rat (fst (gap₊ ⁻¹₊))
      · oneMinusPowers n

  rationalCandidateCauchy :
    isCauchySeq rationalCandidate
  rationalCandidateCauchy =
    rationalScalePresIsCauchySeq
      (fst (gap₊ ⁻¹₊))
      oneMinusPowers
      oneMinusPowersCauchy
