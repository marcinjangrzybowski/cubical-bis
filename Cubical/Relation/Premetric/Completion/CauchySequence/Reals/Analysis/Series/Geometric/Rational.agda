module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ ; 1+_)
open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order.Floor as ℚFloor
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
  as PT using (∣_∣₁)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Convergence


-- Keep rational algebra qualified: this module simultaneously uses the
-- real operations inherited by the geometric-series interface.
module ℚ where
  open import Cubical.Data.Rationals.Base hiding (isProp∼) public
  open import Cubical.Data.Rationals.Properties public
  open import Cubical.Data.Rationals.Order public
  open import Cubical.Data.Rationals.Order.AbsoluteValue public
  open import Cubical.Data.Rationals.Order.Algebra public


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
  rationalNatPath zero = refl
  rationalNatPath (suc n) =
    cong (1 ℚ.+_) (rationalNatPath n)
    ∙ ℚ.ℕ+→ℚ+ 1 n

  two₊ : ℚ₊
  two₊ = ℚ.fromNat 2 , ℚ.0<sucN 1

  rationalSubZero : ∀ x →
    x ℚ.- 0 ≡ x
  rationalSubZero x =
    cong (x ℚ.+_)
      (ℚ.·AnnihilR (ℚ.- 1))
    ∙ ℚ.+IdR x

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
    begin≤
      q ℚ.· p ℚ.·
          (1 ℚ.+
            (1 ℚ.+ coefficient) ℚ.· (1 ℚ.- q))
        ≡→≤⟨ ℚ! ⟩
      q ℚ.·
          (p ℚ.·
            (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q)))
        ℚ.+
      (q ℚ.· p) ℚ.· (1 ℚ.- q)
        ≤⟨ ℚOrder.+Mono≤
            (q ℚ.·
              (p ℚ.·
                (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q))))
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


rationalPowerFactorBound :
  ∀ q → 0 ℚ.≤ q → q ℚ.≤ 1 → ∀ n →
  q ℚ.^ⁿ n ℚ.·
    (1 ℚ.+ rationalNat n ℚ.· (1 ℚ.- q))
    ℚ.≤ 1
rationalPowerFactorBound q 0≤q q≤1 zero = <≤ℚ!
rationalPowerFactorBound q 0≤q q≤1 (suc n) =
  rationalPowerFactorStep
    q (q ℚ.^ⁿ n) (rationalNat n)
    0≤q q≤1
    (ℚOrder.powNonnegative q n 0≤q)
    (ℚOrder.pow≤one q 0≤q n q≤1)
    (rationalPowerFactorBound q 0≤q q≤1 n)


rationalPowerFactorBoundFromNat :
  ∀ q → 0 ℚ.≤ q → q ℚ.≤ 1 → ∀ n →
  q ℚ.^ⁿ n ℚ.·
    (1 ℚ.+ ℚ.fromNat n ℚ.· (1 ℚ.- q))
    ℚ.≤ 1
rationalPowerFactorBoundFromNat q 0≤q q≤1 n =
  subst
    (λ coefficient →
      q ℚ.^ⁿ n ℚ.·
        (1 ℚ.+ coefficient ℚ.· (1 ℚ.- q))
        ℚ.≤ 1)
    (rationalNatPath n)
    (rationalPowerFactorBound q 0≤q q≤1 n)


rationalPowerHasHalfBlock :
  ∀ q → 0 ℚ.≤ q → q ℚ.< 1 →
  Σ[ block ∈ ℕ ]
    q ℚ.^ⁿ block ℚ.≤ fst (two₊ ⁻¹₊)
rationalPowerHasHalfBlock q 0≤q q<1 =
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

  twicePower≤one : q ℚ.^ⁿ block ℚ.· 2 ℚ.≤ 1
  twicePower≤one =
    ℚ.isTrans≤
      (q ℚ.^ⁿ block ℚ.· 2)
      (q ℚ.^ⁿ block ℚ.·
        (1 ℚ.+ ℚ.fromNat block ℚ.· gap))
      1
      (ℚOrder.·MonoL≤
        2 (1 ℚ.+ ℚ.fromNat block ℚ.· gap)
        (q ℚ.^ⁿ block) powerNonnegative two≤factor)
      (rationalPowerFactorBoundFromNat
        q 0≤q (ℚ.<Weaken≤ q 1 q<1) block)

  power≤half :
    q ℚ.^ⁿ block ℚ.≤ fst (two₊ ⁻¹₊)
  power≤half =
    ℚOrder.·CancelR≤
      (q ℚ.^ⁿ block) (fst (two₊ ⁻¹₊)) 2
      (snd two₊)
      (subst
        (q ℚ.^ⁿ block ℚ.· 2 ℚ.≤_)
        (sym (ℚInv.invℚ₊[x]·x two₊))
        twicePower≤one)


rationalPowerModulus :
  ∀ q → 0 ℚ.≤ q → q ℚ.< 1 → ℚ₊ → ℕ
rationalPowerModulus q 0≤q q<1 ε =
  block ℕ.· exponent
  where
  block : ℕ
  block = fst (rationalPowerHasHalfBlock q 0≤q q<1)

  exponent : ℕ
  exponent = fst (ℚInv.1/2ⁿ<ε ε)


rationalPowerSmall :
  ∀ q → (0≤q : 0 ℚ.≤ q) → (q<1 : q ℚ.< 1) →
  ∀ ε n →
  rationalPowerModulus q 0≤q q<1 ε ℕ.≤ n →
  q ℚ.^ⁿ n ℚ.< fst ε
rationalPowerSmall q 0≤q q<1 ε n modulus≤n =
  ℚ.isTrans≤<
    (q ℚ.^ⁿ n)
    (q ℚ.^ⁿ (block ℕ.· exponent))
    (fst ε)
    (ℚOrder.powExponentAntitone
      q 0≤q (ℚ.<Weaken≤ q 1 q<1)
      (block ℕ.· exponent) n modulus≤n)
    (ℚ.isTrans≤<
      (q ℚ.^ⁿ (block ℕ.· exponent))
      (fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent)
      (fst ε)
      blockPowerBound halfPowerSmall)
  where
  block : ℕ
  block = fst (rationalPowerHasHalfBlock q 0≤q q<1)

  blockBound :
    q ℚ.^ⁿ block ℚ.≤ fst (two₊ ⁻¹₊)
  blockBound = snd (rationalPowerHasHalfBlock q 0≤q q<1)

  exponent : ℕ
  exponent = fst (ℚInv.1/2ⁿ<ε ε)

  halfPath :
    fst (two₊ ⁻¹₊) ≡ [ pos 1 / 1+ 1 ]
  halfPath = ℚInv.invℚ₊-fromNat 1

  blockPowerBound :
    q ℚ.^ⁿ (block ℕ.· exponent) ℚ.≤
    fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent
  blockPowerBound =
    subst
      (ℚ._≤ (fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent))
      (sym (ℚOrder.^-rdist-·ℕ q block exponent))
      (ℚOrder.powMono exponent
        (ℚOrder.powNonnegative q block 0≤q)
        blockBound)

  halfPowerSmall :
    fst (two₊ ⁻¹₊) ℚ.^ⁿ exponent ℚ.< fst ε
  halfPowerSmall =
    subst
      (λ base → base ℚ.^ⁿ exponent ℚ.< fst ε)
      (sym halfPath)
      (snd (ℚInv.1/2ⁿ<ε ε))


rationalGeometricPowerCloseZero :
  ∀ q → (0≤q : 0 ℚ.≤ q) → (q<1 : q ℚ.< 1) →
  ∀ ε n →
  rationalPowerModulus q 0≤q q<1 ε ℕ.≤ n →
  geometricTerms (Real.ιℚ q) n
    Real.Base.≈ᶜ[ ε ] Real.ιℚ 0
rationalGeometricPowerCloseZero
    q 0≤q q<1 ε n modulus≤n =
  subst
    (λ z → z Real.Base.≈ᶜ[ ε ] Real.ιℚ 0)
    (sym (pow-ι n q))
    (Real.Base.ι-ι (q ℚ.^ⁿ n) 0 ε
      (subst
        (ℚ._< fst ε)
        (sym absPowerPath)
        (rationalPowerSmall q 0≤q q<1 ε n modulus≤n)))
  where
  powerNonnegative : 0 ℚ.≤ q ℚ.^ⁿ n
  powerNonnegative = ℚOrder.powNonnegative q n 0≤q

  absPowerPath :
    ℚOrder.abs ((q ℚ.^ⁿ n) ℚ.- 0) ≡ q ℚ.^ⁿ n
  absPowerPath =
    cong ℚOrder.abs (rationalSubZero (q ℚ.^ⁿ n))
    ∙ ℚOrder.0≤→abs≡id
        (q ℚ.^ⁿ n) powerNonnegative


-- The chosen arithmetic modulus remains internal to a single radius.  The
-- public convergence statement returns only its propositional truncation,
-- exactly matching the native sequence API.

rationalGeometricPowersTendToZero :
  ∀ q → 0 ℚ.≤ q → q ℚ.< 1 →
  GeometricPowersTendToZero (Real.ιℚ q)
rationalGeometricPowersTendToZero q 0≤q q<1 ε =
  ∣ rationalPowerModulus q 0≤q q<1 ε
  , (λ n modulus≤n →
      rationalGeometricPowerCloseZero
        q 0≤q q<1 ε n modulus≤n) ∣₁


rationalGeometricSeriesSummable :
  ∀ q → 0 ℚ.≤ q → q ℚ.< 1 →
  Summable (geometricTerms (Real.ιℚ q))
rationalGeometricSeriesSummable q 0≤q q<1 =
  geometricSeriesSummable
    (Real.ιℚ q)
    (<ℚ→<ℝ q 1 q<1)
    (rationalGeometricPowersTendToZero q 0≤q q<1)


-- The direct rational argument does not actually need the ratio itself to
-- be nonnegative.  Applying its modulus to `abs q` and using the rational
-- power law gives the usual sharp hypothesis `abs q < 1`, still without
-- invoking a general absolute-convergence theorem for real series.

rationalAbsPow : ∀ n q →
  ℚOrder.abs (q ℚ.^ⁿ n) ≡
  ℚOrder.abs q ℚ.^ⁿ n
rationalAbsPow n q =
  ℚExponentiation.dist·→dist^
    ℚOrder.abs ℚOrder.abs1
    (λ x y → sym (ℚ.abs·abs x y)) n q


rationalGeometricPowerCloseZeroByAbs :
  ∀ q → (absq<1 : ℚOrder.abs q ℚ.< 1) →
  ∀ ε n →
  rationalPowerModulus
    (ℚOrder.abs q) (ℚOrder.0≤abs q) absq<1 ε ℕ.≤ n →
  geometricTerms (Real.ιℚ q) n
    Real.Base.≈ᶜ[ ε ] Real.ιℚ 0
rationalGeometricPowerCloseZeroByAbs
    q absq<1 ε n modulus≤n =
  subst
    (λ z → z Real.Base.≈ᶜ[ ε ] Real.ιℚ 0)
    (sym (pow-ι n q))
    (Real.Base.ι-ι (q ℚ.^ⁿ n) 0 ε
      (subst
        (ℚ._< fst ε)
        (sym absPowerPath)
        (rationalPowerSmall
          (ℚOrder.abs q) (ℚOrder.0≤abs q) absq<1
          ε n modulus≤n)))
  where
  absPowerPath :
    ℚOrder.abs ((q ℚ.^ⁿ n) ℚ.- 0) ≡
    ℚOrder.abs q ℚ.^ⁿ n
  absPowerPath =
    cong ℚOrder.abs (rationalSubZero (q ℚ.^ⁿ n))
    ∙ rationalAbsPow n q


rationalGeometricPowersTendToZeroByAbs :
  ∀ q → ℚOrder.abs q ℚ.< 1 →
  GeometricPowersTendToZero (Real.ιℚ q)
rationalGeometricPowersTendToZeroByAbs q absq<1 ε =
  ∣ rationalPowerModulus
      (ℚOrder.abs q) (ℚOrder.0≤abs q) absq<1 ε
  , (λ n modulus≤n →
      rationalGeometricPowerCloseZeroByAbs
        q absq<1 ε n modulus≤n) ∣₁


rationalGeometricSeriesSummableByAbs :
  ∀ q → ℚOrder.abs q ℚ.< 1 →
  Summable (geometricTerms (Real.ιℚ q))
rationalGeometricSeriesSummableByAbs q absq<1 =
  geometricSeriesSummable
    (Real.ιℚ q)
    (<ℚ→<ℝ q 1
      (ℚ.isTrans≤< q (ℚOrder.abs q) 1
        (ℚOrder.≤abs q) absq<1))
    (rationalGeometricPowersTendToZeroByAbs q absq<1)
