module Cubical.Analysis.Real.Series.Geometric.StrictRational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ; 1+_)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse as ℚInv
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚFloor

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
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Series.Geometric.SignedRational


private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  module Pℝ = PremetricStr (ℝPremetricSpace .snd)
  module ℝTheory = PremetricTheory ℝPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


private
  rationalNat : ℕ → ℚ
  rationalNat zero = 0
  rationalNat (suc n) = 1 ℚ.+ rationalNat n

  rationalNatPath : ∀ n →
    rationalNat n ≡ ℚ.fromNat n
  rationalNatPath zero = refl
  rationalNatPath (suc n) =
    cong (1 ℚ.+_) (rationalNatPath n)
    ∙ ℚ.ℕ+→ℚ+ 1 n

  strictTwo₊ : ℚ₊
  strictTwo₊ = ℚ.fromNat 2 , ℚ.0<sucN 1

  rationalSubZero : ∀ q → q ℚ.- 0 ≡ q
  rationalSubZero q =
    cong (q ℚ.+_)
      (ℚ.·AnnihilR (ℚ.- 1))
    ∙ ℚ.+IdR q

  qPlusGap : ∀ q →
    q ℚ.+ (1 ℚ.- q) ≡ 1
  qPlusGap q =
    ℚ.+Assoc q 1 (ℚ.- q)
    ∙ cong (λ x → x ℚ.+ (ℚ.- q)) (ℚ.+Comm q 1)
    ∙ sym (ℚ.+Assoc 1 q (ℚ.- q))
    ∙ cong (1 ℚ.+_) (ℚ.+InvR q)
    ∙ ℚ.+IdR 1

  factorExpansion : ∀ q p coefficient →
    q ℚ.· p ℚ.·
      (1 ℚ.+
        (1 ℚ.+ coefficient) ℚ.· (1 ℚ.- q))
      ≡
    ( q ℚ.· p
      ℚ.+ (q ℚ.· p)
        ℚ.· (coefficient ℚ.· (1 ℚ.- q))
    ) ℚ.+ (q ℚ.· p) ℚ.· (1 ℚ.- q)
  factorExpansion q p coefficient =
    ℚ.·DistL+
      (q ℚ.· p) 1
      ((1 ℚ.+ coefficient) ℚ.· (1 ℚ.- q))
    ∙ cong₂ ℚ._+_
        (ℚ.·IdR (q ℚ.· p))
        (cong ((q ℚ.· p) ℚ.·_)
          (ℚ.·DistR+ 1 coefficient (1 ℚ.- q)
          ∙ cong₂ ℚ._+_
              (ℚ.·IdL (1 ℚ.- q)) refl)
        ∙ ℚ.·DistL+
            (q ℚ.· p) (1 ℚ.- q)
            (coefficient ℚ.· (1 ℚ.- q)))
    ∙ cong (q ℚ.· p ℚ.+_)
        (ℚ.+Comm
          ((q ℚ.· p) ℚ.· (1 ℚ.- q))
          ((q ℚ.· p)
            ℚ.· (coefficient ℚ.· (1 ℚ.- q))))
    ∙ ℚ.+Assoc
        (q ℚ.· p)
        ((q ℚ.· p)
          ℚ.· (coefficient ℚ.· (1 ℚ.- q)))
        ((q ℚ.· p) ℚ.· (1 ℚ.- q))

  candidateExpansion : ∀ q p coefficient →
    q ℚ.·
      (p ℚ.·
        (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q)))
      ℚ.+ (q ℚ.· p) ℚ.· (1 ℚ.- q)
      ≡
    ( q ℚ.· p
      ℚ.+ (q ℚ.· p)
        ℚ.· (coefficient ℚ.· (1 ℚ.- q))
    ) ℚ.+ (q ℚ.· p) ℚ.· (1 ℚ.- q)
  candidateExpansion q p coefficient =
    cong
      (λ x → x ℚ.+ ((q ℚ.· p) ℚ.· (1 ℚ.- q)))
      ( cong (q ℚ.·_)
          (ℚ.·DistL+ p 1
            (coefficient ℚ.· (1 ℚ.- q))
          ∙ cong₂ ℚ._+_ (ℚ.·IdR p) refl)
      ∙ ℚ.·DistL+ q p
          (p ℚ.· (coefficient ℚ.· (1 ℚ.- q)))
      ∙ cong (q ℚ.· p ℚ.+_)
          (ℚ.·Assoc q p
            (coefficient ℚ.· (1 ℚ.- q)))
      )

  rationalPowerFactorStep :
    ∀ q p coefficient →
    0 ℚ.≤ q → q ℚ.≤ 1 →
    0 ℚ.≤ p → p ℚ.≤ 1 →
    p ℚ.·
      (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q))
      ℚ.≤ 1 →
    q ℚ.· p ℚ.·
      (1 ℚ.+
        (1 ℚ.+ coefficient) ℚ.· (1 ℚ.- q))
      ℚ.≤ 1
  rationalPowerFactorStep
      q p coefficient 0≤q q≤1 0≤p p≤1 bound =
    subst2 ℚ._≤_
      (candidateExpansion q p coefficient
      ∙ sym (factorExpansion q p coefficient))
      (qPlusGap q)
      (ℚOrder.+Mono≤
        (q ℚ.·
          (p ℚ.·
            (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q))))
        q
        ((q ℚ.· p) ℚ.· (1 ℚ.- q))
        (1 ℚ.- q)
        firstBound secondBound)
    where
    0≤gap : 0 ℚ.≤ 1 ℚ.- q
    0≤gap = ℚOrder.≤→0≤Δ q 1 q≤1

    qp≤1 : q ℚ.· p ℚ.≤ 1
    qp≤1 =
      subst (q ℚ.· p ℚ.≤_)
        (ℚ.·IdR 1)
        (ℚOrder.·Mono≤
          q 1 p 1 ℚOrder.0≤1 0≤p q≤1 p≤1)

    firstBound :
      q ℚ.·
        (p ℚ.·
          (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q)))
        ℚ.≤ q
    firstBound =
      subst
        (q ℚ.·
          (p ℚ.·
            (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q)))
          ℚ.≤_)
        (ℚ.·IdR q)
        (ℚOrder.·MonoL≤
          (p ℚ.·
            (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q)))
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


strictRationalPowerFactorBound :
  ∀ q → 0 ℚ.≤ q → q ℚ.≤ 1 → ∀ n →
  q ℚ.^ⁿ n ℚ.·
    (1 ℚ.+ rationalNat n ℚ.· (1 ℚ.- q))
    ℚ.≤ 1
strictRationalPowerFactorBound q 0≤q q≤1 zero =
  subst (ℚ._≤ 1) (sym basePath) (ℚ.isRefl≤ 1)
  where
  basePath :
    1 ℚ.· (1 ℚ.+ 0 ℚ.· (1 ℚ.- q)) ≡ 1
  basePath =
    cong (1 ℚ.·_)
      (cong (1 ℚ.+_) (ℚ.·AnnihilL (1 ℚ.- q))
      ∙ ℚ.+IdR 1)
    ∙ ℚ.·IdL 1
strictRationalPowerFactorBound q 0≤q q≤1 (suc n) =
  rationalPowerFactorStep
    q (q ℚ.^ⁿ n) (rationalNat n)
    0≤q q≤1
    (ℚOrder.powNonnegative q n 0≤q)
    (ℚOrder.pow≤one q 0≤q n q≤1)
    (strictRationalPowerFactorBound q 0≤q q≤1 n)


strictRationalPowerFactorBoundFromNat :
  ∀ q → 0 ℚ.≤ q → q ℚ.≤ 1 → ∀ n →
  q ℚ.^ⁿ n ℚ.·
    (1 ℚ.+ ℚ.fromNat n ℚ.· (1 ℚ.- q))
    ℚ.≤ 1
strictRationalPowerFactorBoundFromNat q 0≤q q≤1 n =
  subst
    (λ coefficient →
      q ℚ.^ⁿ n ℚ.·
        (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q))
        ℚ.≤ 1)
    (rationalNatPath n)
    (strictRationalPowerFactorBound q 0≤q q≤1 n)


strictRationalPowerHasHalfBlock :
  ∀ q → 0 ℚ.≤ q → q ℚ.< 1 →
  Σ[ block ∈ ℕ ]
    q ℚ.^ⁿ block ℚ.≤ halfℚ
strictRationalPowerHasHalfBlock q 0≤q q<1 =
  block , power≤half
  where
  gap : ℚ
  gap = 1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap = ℚOrder.<→0<Δ q 1 q<1

  gap₊ : ℚ₊
  gap₊ = gap , 0<gap

  block : ℕ
  block = ℕ₊₁→ℕ (fst (ℚFloor.ceilℚ₊ (gap₊ ⁻¹₊)))

  inverseGap<block :
    fst (gap₊ ⁻¹₊) ℚ.< ℚ.fromNat block
  inverseGap<block = snd (ℚFloor.ceilℚ₊ (gap₊ ⁻¹₊))

  one<blockTimesGap :
    1 ℚ.< ℚ.fromNat block ℚ.· gap
  one<blockTimesGap =
    subst (ℚ._< ℚ.fromNat block ℚ.· gap)
      (ℚInv.invℚ₊[x]·x gap₊)
      (OrderedCommRingStr.·MonoR<
        (snd ℚOrderedCommRing)
        (fst (gap₊ ⁻¹₊)) (ℚ.fromNat block)
        gap 0<gap inverseGap<block)

  two≤factor :
    2 ℚ.≤ 1 ℚ.+ ℚ.fromNat block ℚ.· gap
  two≤factor =
    ℚ.<Weaken≤ 2
      (1 ℚ.+ ℚ.fromNat block ℚ.· gap)
      (subst
        (ℚ._< (1 ℚ.+ ℚ.fromNat block ℚ.· gap))
        (ℚ.ℕ+→ℚ+ 1 1)
        (ℚOrder.+MonoL<
          1 (ℚ.fromNat block ℚ.· gap)
          1 one<blockTimesGap))

  powerNonnegative : 0 ℚ.≤ q ℚ.^ⁿ block
  powerNonnegative = ℚOrder.powNonnegative q block 0≤q

  twicePower≤one :
    q ℚ.^ⁿ block ℚ.· 2 ℚ.≤ 1
  twicePower≤one =
    ℚ.isTrans≤
      (q ℚ.^ⁿ block ℚ.· 2)
      (q ℚ.^ⁿ block ℚ.·
        (1 ℚ.+ ℚ.fromNat block ℚ.· gap))
      1
      (ℚOrder.·MonoL≤
        2 (1 ℚ.+ ℚ.fromNat block ℚ.· gap)
        (q ℚ.^ⁿ block) powerNonnegative two≤factor)
      (strictRationalPowerFactorBoundFromNat
        q 0≤q (ℚ.<Weaken≤ q 1 q<1) block)

  power≤half : q ℚ.^ⁿ block ℚ.≤ halfℚ
  power≤half =
    ℚOrder.·CancelR≤
      (q ℚ.^ⁿ block) halfℚ 2
      (snd strictTwo₊)
      (subst
        (q ℚ.^ⁿ block ℚ.· 2 ℚ.≤_)
        (sym (ℚInv.invℚ₊[x]·x strictTwo₊))
        twicePower≤one)


strictRationalPowerModulus :
  ∀ q → 0 ℚ.≤ q → q ℚ.< 1 →
  ℚ₊ → ℕ
strictRationalPowerModulus q 0≤q q<1 ε =
  block ℕ.· exponent
  where
  block : ℕ
  block = fst (strictRationalPowerHasHalfBlock q 0≤q q<1)

  exponent : ℕ
  exponent = fst (ℚInv.1/2ⁿ<ε ε)


strictRationalPowerSmall :
  ∀ q → (0≤q : 0 ℚ.≤ q) → (q<1 : q ℚ.< 1) →
  ∀ ε n →
  strictRationalPowerModulus q 0≤q q<1 ε ℕ.≤ n →
  q ℚ.^ⁿ n ℚ.< fst ε
strictRationalPowerSmall q 0≤q q<1 ε n modulus≤n =
  ℚ.isTrans≤<
    (q ℚ.^ⁿ n)
    (q ℚ.^ⁿ (block ℕ.· exponent))
    (fst ε)
    (ℚOrder.powExponentAntitone
      q 0≤q (ℚ.<Weaken≤ q 1 q<1)
      (block ℕ.· exponent) n modulus≤n)
    (ℚ.isTrans≤<
      (q ℚ.^ⁿ (block ℕ.· exponent))
      (halfℚ ℚ.^ⁿ exponent)
      (fst ε)
      blockPowerBound halfPowerSmall)
  where
  block : ℕ
  block = fst (strictRationalPowerHasHalfBlock q 0≤q q<1)

  blockBound : q ℚ.^ⁿ block ℚ.≤ halfℚ
  blockBound = snd (strictRationalPowerHasHalfBlock q 0≤q q<1)

  exponent : ℕ
  exponent = fst (ℚInv.1/2ⁿ<ε ε)

  blockPowerBound :
    q ℚ.^ⁿ (block ℕ.· exponent) ℚ.≤
    halfℚ ℚ.^ⁿ exponent
  blockPowerBound =
    subst
      (ℚ._≤ (halfℚ ℚ.^ⁿ exponent))
      (sym (ℚOrder.^-rdist-·ℕ q block exponent))
      (ℚOrder.powMono exponent
        (ℚOrder.powNonnegative q block 0≤q)
        blockBound)

  halfPowerSmall :
    halfℚ ℚ.^ⁿ exponent ℚ.< fst ε
  halfPowerSmall =
    subst
      (λ base → base ℚ.^ⁿ exponent ℚ.< fst ε)
      (sym halfℚPath)
      (snd (ℚInv.1/2ⁿ<ε ε))


strictSignedRationalPowerModulus :
  ∀ q → ℚOrder.abs q ℚ.< 1 → ℚ₊ → ℕ
strictSignedRationalPowerModulus q absq<1 =
  strictRationalPowerModulus
    (ℚOrder.abs q) (ℚOrder.0≤abs q) absq<1


strictSignedRationalGeometricPowerSmall : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  ∀ ε n →
  strictSignedRationalPowerModulus q absq<1 ε ℕ.≤ n →
  ℚOrder.abs (powℚ q n) ℚ.< fst ε
strictSignedRationalGeometricPowerSmall
    q absq<1 ε n modulus≤n =
  subst (ℚ._< fst ε)
    (sym absPowerPath)
    (strictRationalPowerSmall
      (ℚOrder.abs q) (ℚOrder.0≤abs q) absq<1
      ε n modulus≤n)
  where
  powℚPath : ∀ r k →
    powℚ r k ≡ r ℚ.^ⁿ k
  powℚPath r zero = refl
  powℚPath r (suc k) =
    cong (r ℚ.·_) (powℚPath r k)

  absPowerPath :
    ℚOrder.abs (powℚ q n) ≡
    ℚOrder.abs q ℚ.^ⁿ n
  absPowerPath =
    signedRationalAbsPower q n
    ∙ powℚPath (ℚOrder.abs q) n


strictSignedRationalGeometricPowerCloseZero : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  ∀ ε n →
  strictSignedRationalPowerModulus q absq<1 ε ℕ.≤ n →
  geometricTerms (rat q) n ∼[ ε ] 0ℝ
strictSignedRationalGeometricPowerCloseZero
    q absq<1 ε n modulus≤n =
  subst2 (_∼[ ε ]_)
    (sym (pow-rat q n)) refl
    (rat-rat (powℚ q n) 0 ε
      (subst (ℚ._< fst ε)
        (sym absDifferencePath)
        (strictSignedRationalGeometricPowerSmall
          q absq<1 ε n modulus≤n)))
  where
  absDifferencePath :
    ℚOrder.abs (powℚ q n ℚ.- 0) ≡
    ℚOrder.abs (powℚ q n)
  absDifferencePath =
    cong ℚOrder.abs
      (rationalSubZero (powℚ q n))


strictSignedRationalGeometricPowersTendToZero : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  isLimitSequence (geometricTerms (rat q)) 0ℝ
strictSignedRationalGeometricPowersTendToZero q absq<1 ε =
  ∣ (strictSignedRationalPowerModulus q absq<1 ε
    , λ n modulus≤n →
        strictSignedRationalGeometricPowerCloseZero
          q absq<1 ε n modulus≤n
    ) ∣₁


strictSignedRationalGeometricPowersChosenCauchy : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  ChosenIsCauchySequence (geometricTerms (rat q))
strictSignedRationalGeometricPowersChosenCauchy
    q absq<1 .fst ε =
  strictSignedRationalPowerModulus q absq<1 (ε /2₊)
strictSignedRationalGeometricPowersChosenCauchy
    q absq<1 .snd ε m n modulus≤m modulus≤n =
  Pℝ.subst≈
    (geometricTerms (rat q) m)
    (geometricTerms (rat q) n)
    (/2+/2≡id (fst ε))
    (triangle∼
      (geometricTerms (rat q) m) 0ℝ
      (geometricTerms (rat q) n)
      (ε /2₊) (ε /2₊)
      (strictSignedRationalGeometricPowerCloseZero
        q absq<1 (ε /2₊) m modulus≤m)
      (sym∼
        (geometricTerms (rat q) n) 0ℝ (ε /2₊)
        (strictSignedRationalGeometricPowerCloseZero
          q absq<1 (ε /2₊) n modulus≤n)))


strictSignedRationalGeometricPowersSeqWitness : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  SeqWitness (geometricTerms (rat q))
strictSignedRationalGeometricPowersSeqWitness q absq<1 =
  ∣ strictSignedRationalGeometricPowersChosenCauchy
      q absq<1 ∣₁


strictSignedRationalQ<One : ∀ q →
  ℚOrder.abs q ℚ.< 1 →
  q ℚ.< 1
strictSignedRationalQ<One q absq<1 =
  ℚ.isTrans≤< q (ℚOrder.abs q) 1
    (ℚOrder.≤abs q) absq<1


strictSignedRationalGeometricGapPositive : ∀ q →
  ℚOrder.abs q ℚ.< 1 →
  0 ℚ.< 1 ℚ.- q
strictSignedRationalGeometricGapPositive q absq<1 =
  ℚOrder.<→0<Δ q 1
    (strictSignedRationalQ<One q absq<1)


strictSignedRationalGeometricPositiveDenominator : ∀ q →
  ℚOrder.abs q ℚ.< 1 →
  0ℝ <ℝ 1ℝ - rat q
strictSignedRationalGeometricPositiveDenominator q absq<1 =
  subst (0ℝ <ℝ_)
    (sym (sub-rat 1 q))
    (<ℚ→<ℝ 0 (1 ℚ.- q)
      (strictSignedRationalGeometricGapPositive q absq<1))


strictSignedRationalGeometricSum : ∀ q →
  ℚOrder.abs q ℚ.< 1 → ℝ
strictSignedRationalGeometricSum q absq<1 =
  positiveReciprocal (1ℝ - rat q)
    (strictSignedRationalGeometricPositiveDenominator
      q absq<1)


strictSignedRationalGeometricSum-rat : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  strictSignedRationalGeometricSum q absq<1 ≡
  rat
    (fst
      (((1 ℚ.- q)
        , strictSignedRationalGeometricGapPositive
            q absq<1) ⁻¹₊))
strictSignedRationalGeometricSum-rat q absq<1 =
  subst
    (λ x →
      (p : 0ℝ <ℝ x) →
      positiveReciprocal x p ≡
      rat (fst (gap₊ ⁻¹₊)))
    (sym (sub-rat 1 q))
    (positiveReciprocal-rat gap 0<gap)
    (strictSignedRationalGeometricPositiveDenominator
      q absq<1)
  where
  gap : ℚ
  gap = 1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap =
    strictSignedRationalGeometricGapPositive q absq<1

  gap₊ : ℚ₊
  gap₊ = gap , 0<gap


private
  oneMinusStrictSignedPowersChosenCauchy : ∀ q →
    (absq<1 : ℚOrder.abs q ℚ.< 1) →
    ChosenIsCauchySequence
      (λ n → 1ℝ - geometricTerms (rat q) n)
  oneMinusStrictSignedPowersChosenCauchy
      q absq<1 .fst ε =
    strictSignedRationalGeometricPowersChosenCauchy
      q absq<1 .fst (ε /2₊)
  oneMinusStrictSignedPowersChosenCauchy
      q absq<1 .snd
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
          (strictSignedRationalGeometricPowersChosenCauchy
            q absq<1 .snd
            (ε /2₊) m n modulus≤m modulus≤n)))

  strictScalarPresChosenCauchy : ∀ c sequence →
    ChosenIsCauchySequence sequence →
    ChosenIsCauchySequence ((c ⋆_) ∘ sequence)
  strictScalarPresChosenCauchy c sequence =
    LWith→presIsCauchySeq
      (rationalScalarBound c) (c ⋆_)
      (scalar-isLipschitzWith c) sequence

  strictEventuallyEqualPresChosenCauchy : ∀ a b →
    ℝTheory.EventuallyEqualSeq a b →
    ChosenIsCauchySequence a →
    ChosenIsCauchySequence b
  strictEventuallyEqualPresChosenCauchy a b =
    ℝTheory.eventuallyEqualSeqPresIsCauchySeq a b


strictSignedRationalGeometricSeriesChosenCauchy : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  ChosenIsCauchySequence
    (partialSum (geometricTerms (rat q)))
strictSignedRationalGeometricSeriesChosenCauchy q absq<1 =
  strictEventuallyEqualPresChosenCauchy
    candidate
    (partialSum (geometricTerms (rat q)))
    (0 , λ n _ → candidateEqualsPartial n)
    candidateChosenCauchy
  where
  gap : ℚ
  gap = 1 ℚ.- q

  0<gap : 0 ℚ.< gap
  0<gap =
    strictSignedRationalGeometricGapPositive q absq<1

  gap₊ : ℚ₊
  gap₊ = gap , 0<gap

  positiveDenominator : 0ℝ <ℝ 1ℝ - rat q
  positiveDenominator =
    strictSignedRationalGeometricPositiveDenominator
      q absq<1

  reciprocalPath :
    positiveReciprocal
      (1ℝ - rat q) positiveDenominator ≡
    rat (fst (gap₊ ⁻¹₊))
  reciprocalPath =
    strictSignedRationalGeometricSum-rat q absq<1

  oneMinusPowers : RealSequence
  oneMinusPowers n =
    1ℝ - geometricTerms (rat q) n

  candidate : RealSequence
  candidate n =
    fst (gap₊ ⁻¹₊) ⋆ oneMinusPowers n

  candidateChosenCauchy :
    ChosenIsCauchySequence candidate
  candidateChosenCauchy =
    strictScalarPresChosenCauchy
      (fst (gap₊ ⁻¹₊)) oneMinusPowers
      (oneMinusStrictSignedPowersChosenCauchy
        q absq<1)

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


strictSignedRationalGeometricSeriesIsCauchy : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  IsCauchySeries (geometricTerms (rat q))
strictSignedRationalGeometricSeriesIsCauchy q absq<1 =
  ∣ strictSignedRationalGeometricSeriesChosenCauchy
      q absq<1 ∣₁


strictSignedRationalGeometricSeriesHasSum : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  HasSum (geometricTerms (rat q))
    (strictSignedRationalGeometricSum q absq<1)
strictSignedRationalGeometricSeriesHasSum q absq<1 =
  subst
    (λ sequence → isLimitSequence sequence reciprocal)
    (funExt candidateEqualsPartial)
    candidateLimit
  where
  positiveDenominator : 0ℝ <ℝ 1ℝ - rat q
  positiveDenominator =
    strictSignedRationalGeometricPositiveDenominator
      q absq<1

  reciprocal : ℝ
  reciprocal = strictSignedRationalGeometricSum q absq<1

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
        (strictSignedRationalGeometricPowersTendToZero
          q absq<1))

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


strictSignedRationalGeometricSeriesSummable : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  Summable (geometricTerms (rat q))
strictSignedRationalGeometricSeriesSummable q absq<1 =
  strictSignedRationalGeometricSum q absq<1
  , strictSignedRationalGeometricSeriesHasSum q absq<1


seriesSum-strictSignedRationalGeometric : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  (summable : Summable (geometricTerms (rat q))) →
  seriesSum (geometricTerms (rat q)) summable ≡
  strictSignedRationalGeometricSum q absq<1
seriesSum-strictSignedRationalGeometric
    q absq<1 summable =
  seriesSumIndependent
    (geometricTerms (rat q)) summable
    (strictSignedRationalGeometricSeriesSummable
      q absq<1)


seriesSum-strictSignedRationalGeometric-rat : ∀ q →
  (absq<1 : ℚOrder.abs q ℚ.< 1) →
  (summable : Summable (geometricTerms (rat q))) →
  seriesSum (geometricTerms (rat q)) summable ≡
  rat
    (fst
      (((1 ℚ.- q)
        , strictSignedRationalGeometricGapPositive
            q absq<1) ⁻¹₊))
seriesSum-strictSignedRationalGeometric-rat
    q absq<1 summable =
  seriesSum-strictSignedRationalGeometric
    q absq<1 summable
  ∙ strictSignedRationalGeometricSum-rat q absq<1
