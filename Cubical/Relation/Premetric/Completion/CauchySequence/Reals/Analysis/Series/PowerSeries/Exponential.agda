module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; _!)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (ℕ₊₁ ; 1+_ ; ℕ₊₁→ℕ)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ ; fromNatℚ)
import Cubical.Data.Rationals.Properties as ℚP
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
open import Cubical.Data.Rationals.Order.Floor using (ceilℚ₊)
open import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (nonnegative→abs-self ; mul-nonnegative ; mul-monotone-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative


-- The coefficients are kept in the positive-rational fragment before being
-- embedded.  Besides avoiding a proof argument in every coefficient, this
-- exposes exactly the order structure needed by geometric majorants later.

naturalRational : ℕ → ℚ
naturalRational n =
  ℕ.HasFromNat.fromNat ℚ.fromNatℚ n {{tt}}


naturalRational-nonnegative : ∀ n →
  0 ℚ.≤ naturalRational n
naturalRational-nonnegative n = ℚAbs.0≤pos n _


naturalRational-mono : ∀ {m n} →
  m ℕ.≤ n → naturalRational m ℚ.≤ naturalRational n
naturalRational-mono {m} {n} (difference , difference+m≡n) =
  subst2 ℚ._≤_
    ℚ!
    (ℚAbs.ℕ+→ℚ+ difference m
      ∙ cong naturalRational difference+m≡n)
    (ℚ.≤-+o
      0 (naturalRational difference) (naturalRational m)
      (naturalRational-nonnegative difference))


factorialPositiveRational : ℕ → ℚ₊
factorialPositiveRational n =
  naturalRational (n !) , factorial-positive
  where
  factorial-nonzero : (n ! ≡ zero) → ⊥.⊥
  factorial-nonzero = (ℕ.<→≢ (ℕ.0<! n)) ∘ sym

  factorial-as-suc : suc (ℕ.predℕ (n !)) ≡ n !
  factorial-as-suc = sym (ℕ.suc-predℕ (n !) factorial-nonzero)

  factorial-positive : 0 ℚ.< naturalRational (n !)
  factorial-positive =
    subst (0 ℚ.<_)
      (cong naturalRational factorial-as-suc)
      (ℚAbs.0<sucN (ℕ.predℕ (n !)))


factorialPositiveRational-suc : ∀ n →
  factorialPositiveRational (suc n) ≡
  ((naturalRational (suc n) , ℚAbs.0<sucN n) ·₊
    factorialPositiveRational n)
factorialPositiveRational-suc n =
  ℚ₊≡ (sym (ℚAbs.ℕ·→ℚ· (suc n) (n !)))


rationalExponentialCoefficient : ℕ → ℚ
rationalExponentialCoefficient n =
  fst ((factorialPositiveRational n) ⁻¹₊)


exponentialCoefficients : RealSequence
exponentialCoefficients n =
  Real.ιℚ (rationalExponentialCoefficient n)


rationalExponentialCoefficient-suc : ∀ n →
  rationalExponentialCoefficient (suc n) ≡
  fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊)
    ℚR.· rationalExponentialCoefficient n
rationalExponentialCoefficient-suc n =
    cong (fst ∘ _⁻¹₊)
      (factorialPositiveRational-suc n)
  ∙ cong fst
      (sym
        (ℚInv.invℚ₊Dist·
          (naturalRational (suc n) , ℚAbs.0<sucN n)
          (factorialPositiveRational n)))


rationalExponentialCoefficient-zero :
  rationalExponentialCoefficient zero ≡ 1
rationalExponentialCoefficient-zero =
  ℚInv.invℚ₊-fromNat zero


rationalExponentialTerm : ℚ → ℕ → ℚ
rationalExponentialTerm radius n =
  rationalExponentialCoefficient n ℚR.·
    ℚExponentiation._^_ radius n


rationalExponentialTerm-suc : ∀ radius n →
  rationalExponentialTerm radius (suc n) ≡
  (radius ℚR.·
    fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊))
    ℚR.· rationalExponentialTerm radius n
rationalExponentialTerm-suc radius n =
    cong
      (ℚR._· ℚExponentiation._^_ radius (suc n))
      (rationalExponentialCoefficient-suc n)
  ∙ rearrange
      (fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊))
      (rationalExponentialCoefficient n)
      radius
      (ℚExponentiation._^_ radius n)
  where
  rearrange : ∀ a b c d →
    (a ℚR.· b) ℚR.· (c ℚR.· d) ≡
    (c ℚR.· a) ℚR.· (b ℚR.· d)
  rearrange a b c d =
      sym (ℚP.·Assoc a b (c ℚR.· d))
    ∙ cong (a ℚR.·_) (ℚP.·Assoc b c d)
    ∙ cong (λ value → a ℚR.· (value ℚR.· d))
        (ℚP.·Comm b c)
    ∙ cong (a ℚR.·_) (sym (ℚP.·Assoc c b d))
    ∙ ℚP.·Assoc a c (b ℚR.· d)
    ∙ cong (ℚR._· (b ℚR.· d)) (ℚP.·Comm a c)


powerSeriesTerms-exponential-rational : ∀ radius n →
  powerSeriesTerms exponentialCoefficients (Real.ιℚ radius) n ≡
  Real.ιℚ (rationalExponentialTerm radius n)
powerSeriesTerms-exponential-rational radius n =
    cong (exponentialCoefficients n Mul.·_)
      (pow-ι n radius)
  ∙ Mul.mul-ι-ι
      (rationalExponentialCoefficient n)
      (ℚExponentiation._^_ radius n)


powerSeriesTerms-exponential-rational-suc : ∀ radius n →
  powerSeriesTerms exponentialCoefficients (Real.ιℚ radius) (suc n)
    ≡
  Real.ιℚ
      (radius ℚR.·
        fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊))
    Mul.·
  powerSeriesTerms exponentialCoefficients (Real.ιℚ radius) n
powerSeriesTerms-exponential-rational-suc radius n =
    powerSeriesTerms-exponential-rational radius (suc n)
  ∙ cong Real.ιℚ (rationalExponentialTerm-suc radius n)
  ∙ sym
      (Mul.mul-ι-ι
        (radius ℚR.·
          fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊))
        (rationalExponentialTerm radius n))
  ∙ cong
      (Real.ιℚ
          (radius ℚR.·
            fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊))
        Mul.·_)
      (sym (powerSeriesTerms-exponential-rational radius n))


rationalExponentialStepFactor : ℚ → ℕ → ℚ
rationalExponentialStepFactor radius n =
  radius ℚR.·
    fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊)


rationalExponentialStepFactor-nonnegative : ∀ radius →
  0 ℚ.≤ radius → ∀ n →
  0 ℚ.≤ rationalExponentialStepFactor radius n
rationalExponentialStepFactor-nonnegative radius 0≤radius n =
  subst (λ left → left ℚ.≤ rationalExponentialStepFactor radius n)
    (ℚP.·AnnihilL
      (fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊)))
    (ℚ.≤-·o
      0 radius
      (fst ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊))
      (ℚ.<Weaken≤ _ _
        (snd ((naturalRational (suc n) , ℚAbs.0<sucN n) ⁻¹₊)))
      0≤radius)


rationalExponentialStepFactor-antitone : ∀ radius →
  0 ℚ.≤ radius →
  ∀ {m n} → m ℕ.≤ n →
  rationalExponentialStepFactor radius n ℚ.≤
  rationalExponentialStepFactor radius m
rationalExponentialStepFactor-antitone radius 0≤radius {m} {n} m≤n =
  ℚ.≤-o·
    (fst (n-positive ⁻¹₊))
    (fst (m-positive ⁻¹₊))
    radius 0≤radius
    (ℚInv.invℚ≤invℚ n-positive m-positive
      (naturalRational-mono (ℕ.suc-≤-suc m≤n)))
  where
  m-positive : ℚ₊
  m-positive = naturalRational (suc m) , ℚAbs.0<sucN m

  n-positive : ℚ₊
  n-positive = naturalRational (suc n) , ℚAbs.0<sucN n


realExponentialStepFactor : ℚ → ℕ → Real.ℝ
realExponentialStepFactor radius n =
  Real.ιℚ (rationalExponentialStepFactor radius n)


realExponentialStepFactor-nonnegative : ∀ radius →
  0 ℚ.≤ radius → ∀ n →
  zeroℝ ≤ℝ realExponentialStepFactor radius n
realExponentialStepFactor-nonnegative radius 0≤radius n =
  ≤ℚ→≤ℝ 0 (rationalExponentialStepFactor radius n)
    (rationalExponentialStepFactor-nonnegative radius 0≤radius n)


realExponentialStepFactor-antitone : ∀ radius →
  0 ℚ.≤ radius →
  ∀ {m n} → m ℕ.≤ n →
  realExponentialStepFactor radius n ≤ℝ
  realExponentialStepFactor radius m
realExponentialStepFactor-antitone radius 0≤radius {m} {n} m≤n =
  ≤ℚ→≤ℝ
    (rationalExponentialStepFactor radius n)
    (rationalExponentialStepFactor radius m)
    (rationalExponentialStepFactor-antitone radius 0≤radius m≤n)


exponentialCoefficient-suc : ∀ n →
  realNatural (suc n) Mul.· exponentialCoefficients (suc n) ≡
  exponentialCoefficients n
exponentialCoefficient-suc n =
    Mul.mul-ι-ι
      (naturalRational (suc n))
      (rationalExponentialCoefficient (suc n))
  ∙ cong Real.ιℚ
      (cong (naturalRational (suc n) ℚR.·_)
        (rationalExponentialCoefficient-suc n)
      ∙ ℚInv.y·[x/y]
          suc-positive (rationalExponentialCoefficient n))
  where
  suc-positive : ℚ₊
  suc-positive = naturalRational (suc n) , ℚAbs.0<sucN n


formalDerivative-exponentialCoefficients-pointwise : ∀ n →
  formalDerivative exponentialCoefficients n ≡
  exponentialCoefficients n
formalDerivative-exponentialCoefficients-pointwise =
  exponentialCoefficient-suc


formalDerivative-exponentialCoefficients :
  formalDerivative exponentialCoefficients ≡ exponentialCoefficients
formalDerivative-exponentialCoefficients =
  funExt formalDerivative-exponentialCoefficients-pointwise


exponentialCoefficients-positive : ∀ n →
  zeroℝ <ℝ exponentialCoefficients n
exponentialCoefficients-positive n =
  <ℚ→<ℝ 0
    (fst ((factorialPositiveRational n) ⁻¹₊))
    (snd ((factorialPositiveRational n) ⁻¹₊))


exponentialCoefficients-nonnegative : ∀ n →
  zeroℝ ≤ℝ exponentialCoefficients n
exponentialCoefficients-nonnegative n =
  <ℝ-weaken zeroℝ (exponentialCoefficients n)
    (exponentialCoefficients-positive n)


exponentialCoefficient-zero :
  exponentialCoefficients zero ≡ Real.ιℚ 1
exponentialCoefficient-zero =
  cong Real.ιℚ rationalExponentialCoefficient-zero


exponentialPowerSeriesTerm-nonnegativeAt : ∀ x →
  zeroℝ ≤ℝ x → ∀ n →
  zeroℝ ≤ℝ powerSeriesTerms exponentialCoefficients x n
exponentialPowerSeriesTerm-nonnegativeAt x 0≤x n =
  mul-nonnegative
    (exponentialCoefficients n) (x ^ⁿ n)
    (exponentialCoefficients-nonnegative n)
    (powNonnegative x n 0≤x)


exponentialPowerSeriesTerm-nonnegative : ∀ radius →
  0 ℚ.≤ radius → ∀ n →
  zeroℝ ≤ℝ
    powerSeriesTerms exponentialCoefficients (Real.ιℚ radius) n
exponentialPowerSeriesTerm-nonnegative radius 0≤radius n =
  mul-nonnegative
    (exponentialCoefficients n)
    (Real.ιℚ radius ^ⁿ n)
    (exponentialCoefficients-nonnegative n)
    (powNonnegative (Real.ιℚ radius) n
      (≤ℚ→≤ℝ 0 radius 0≤radius))


exponentialTailGeometricMajorant :
  ℚ → ℕ → RealSequence
exponentialTailGeometricMajorant radius start =
  scaledGeometricTerms
    (powerSeriesTerms exponentialCoefficients
      (Real.ιℚ radius) (suc start))
    (realExponentialStepFactor radius start)


exponentialTailGeometricRawBound : ∀ radius →
  0 ℚ.≤ radius → ∀ start n →
  dropSeries (suc start)
      (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius)) n
    ≤ℝ
  exponentialTailGeometricMajorant radius start n
exponentialTailGeometricRawBound radius 0≤radius start zero =
  subst
    (dropSeries (suc start)
        (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius)) zero
      ≤ℝ_)
    (sym (mul-one-right
      (powerSeriesTerms exponentialCoefficients
        (Real.ιℚ radius) (suc start))))
    (≤ℝ-refl
      (powerSeriesTerms exponentialCoefficients
        (Real.ιℚ radius) (suc start)))
exponentialTailGeometricRawBound radius 0≤radius start (suc n) =
  subst2 _≤ℝ_ (sym left-path) (sym right-path) product-bound
  where
  terms : RealSequence
  terms = powerSeriesTerms exponentialCoefficients (Real.ιℚ radius)

  tail : RealSequence
  tail = dropSeries (suc start) terms

  ratio : Real.ℝ
  ratio = realExponentialStepFactor radius start

  coefficient : Real.ℝ
  coefficient = terms (suc start)

  global-index : ℕ
  global-index = n ℕ.+ suc start

  start≤global : start ℕ.≤ global-index
  start≤global =
    ℕ.≤-trans
      (ℕ.<-weaken (ℕ.≤-refl {m = suc start}))
      (ℕ.≤SumRight {n = suc start} {k = n})

  factor≤ratio :
    realExponentialStepFactor radius global-index ≤ℝ ratio
  factor≤ratio =
    realExponentialStepFactor-antitone
      radius 0≤radius start≤global

  factor-nonnegative :
    zeroℝ ≤ℝ realExponentialStepFactor radius global-index
  factor-nonnegative =
    realExponentialStepFactor-nonnegative radius 0≤radius global-index

  tail-nonnegative : zeroℝ ≤ℝ tail n
  tail-nonnegative =
    exponentialPowerSeriesTerm-nonnegative
      radius 0≤radius global-index

  induction-bound :
    tail n ≤ℝ scaledGeometricTerms coefficient ratio n
  induction-bound =
    exponentialTailGeometricRawBound radius 0≤radius start n

  product-bound :
    realExponentialStepFactor radius global-index Mul.· tail n
      ≤ℝ
    ratio Mul.· scaledGeometricTerms coefficient ratio n
  product-bound =
    mul-monotone-nonnegative
      (realExponentialStepFactor radius global-index) ratio
      (tail n) (scaledGeometricTerms coefficient ratio n)
      factor≤ratio induction-bound factor-nonnegative tail-nonnegative

  left-path :
    tail (suc n) ≡
    realExponentialStepFactor radius global-index Mul.· tail n
  left-path =
    powerSeriesTerms-exponential-rational-suc radius global-index

  right-path :
    scaledGeometricTerms coefficient ratio (suc n) ≡
    ratio Mul.· scaledGeometricTerms coefficient ratio n
  right-path =
      mul-assoc coefficient ratio (ratio ^ⁿ n)
    ∙ cong (Mul._· ratio ^ⁿ n) (mul-comm coefficient ratio)
    ∙ sym (mul-assoc ratio coefficient (ratio ^ⁿ n))


exponentialTailGeometricBound : ∀ radius →
  0 ℚ.≤ radius → ∀ start n →
  Abs.absℝ
    (dropSeries (suc start)
      (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius)) n)
    ≤ℝ
  exponentialTailGeometricMajorant radius start n
exponentialTailGeometricBound radius 0≤radius start n =
  subst
    (_≤ℝ exponentialTailGeometricMajorant radius start n)
    (sym (nonnegative→abs-self (tail n) tail-nonnegative))
    (exponentialTailGeometricRawBound radius 0≤radius start n)
  where
  tail : RealSequence
  tail =
    dropSeries (suc start)
      (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius))

  tail-nonnegative : zeroℝ ≤ℝ tail n
  tail-nonnegative =
    exponentialPowerSeriesTerm-nonnegative
      radius 0≤radius (n ℕ.+ suc start)


exponentialTailGeometricMajorantIsCauchy : ∀ radius →
  0 ℚ.≤ radius → ∀ start →
  radius ℚ.< naturalRational (suc start) →
  IsCauchySeries (exponentialTailGeometricMajorant radius start)
exponentialTailGeometricMajorantIsCauchy
  radius 0≤radius start radius<start =
  scaleSeriesIsCauchy coefficient (geometricTerms ratio)
    (geometricSeriesIsCauchyOfAbs<1 ratio abs-ratio<1)
  where
  start-positive : ℚ₊
  start-positive =
    naturalRational (suc start) , ℚAbs.0<sucN start

  rational-ratio : ℚ
  rational-ratio = rationalExponentialStepFactor radius start

  ratio : Real.ℝ
  ratio = Real.ιℚ rational-ratio

  coefficient : Real.ℝ
  coefficient =
    powerSeriesTerms exponentialCoefficients
      (Real.ιℚ radius) (suc start)

  ratio-nonnegative : zeroℝ ≤ℝ ratio
  ratio-nonnegative =
    realExponentialStepFactor-nonnegative radius 0≤radius start

  rational-ratio<1 : rational-ratio ℚ.< 1
  rational-ratio<1 =
    fst (ℚInv.x<y≃x/y<1 radius start-positive) radius<start

  ratio<1 : ratio <ℝ Real.ιℚ 1
  ratio<1 = <ℚ→<ℝ rational-ratio 1 rational-ratio<1

  abs-ratio<1 : Abs.absℝ ratio <ℝ Real.ιℚ 1
  abs-ratio<1 =
    subst (_<ℝ Real.ιℚ 1)
      (sym (nonnegative→abs-self ratio ratio-nonnegative))
      ratio<1


exponentialPowerSeriesIsAbsolutelyCauchyAtRationalWithin : ∀ radius →
  0 ℚ.≤ radius → ∀ start →
  radius ℚ.< naturalRational (suc start) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius))
exponentialPowerSeriesIsAbsolutelyCauchyAtRationalWithin
  radius 0≤radius start radius<start =
  summableIsCauchySeries absolute-terms absolute-summable
  where
  terms : RealSequence
  terms =
    powerSeriesTerms exponentialCoefficients (Real.ιℚ radius)

  absolute-terms : RealSequence
  absolute-terms = Abs.absℝ ∘ terms

  tail : RealSequence
  tail = dropSeries (suc start) terms

  majorant : RealSequence
  majorant = exponentialTailGeometricMajorant radius start

  absolute-tail-cauchy : IsCauchySeries (Abs.absℝ ∘ tail)
  absolute-tail-cauchy =
    dominatedCauchySeriesIsCauchy
      (Abs.absℝ ∘ tail) majorant
      (λ n →
        subst (_≤ℝ majorant n)
          (sym (Abs.absℝ-idempotent (tail n)))
          (exponentialTailGeometricBound radius 0≤radius start n))
      (exponentialTailGeometricMajorantIsCauchy
        radius 0≤radius start radius<start)

  absolute-tail-summable : Summable (dropSeries (suc start) absolute-terms)
  absolute-tail-summable =
    cauchySeriesIsSummable (Abs.absℝ ∘ tail) absolute-tail-cauchy

  absolute-summable : Summable absolute-terms
  absolute-summable =
    dropSeriesReflectsSummable
      (suc start) absolute-terms absolute-tail-summable


naturalCutoffAboveNonnegativeRational : ∀ radius →
  0 ℚ.≤ radius →
  Σ[ start ∈ ℕ ] radius ℚ.< naturalRational (suc start)
naturalCutoffAboveNonnegativeRational radius 0≤radius =
  fst ceiling .ℕ₊₁.n
  , ℚ.isTrans< radius successor-radius
      (naturalRational (ℕ₊₁→ℕ (fst ceiling)))
      radius<successor (snd ceiling)
  where
  successor-radius : ℚ
  successor-radius = radius ℚR.+ 1

  radius<successor : radius ℚ.< successor-radius
  radius<successor =
    subst2 ℚ._<_
      (ℚP.+IdL radius)
      (ℚP.+Comm 1 radius)
      (ℚ.<-+o 0 1 radius (ℚAbs.0<sucN zero))

  successor-positive : 0 ℚ.< successor-radius
  successor-positive =
    ℚ.isTrans≤< 0 radius successor-radius
      0≤radius radius<successor

  ceiling : Σ[ k ∈ ℕ₊₁ ]
    successor-radius ℚ.< naturalRational (ℕ₊₁→ℕ k)
  ceiling = ceilℚ₊ (successor-radius , successor-positive)


exponentialPowerSeriesIsAbsolutelyCauchyAtNonnegativeRational :
  ∀ radius → 0 ℚ.≤ radius →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius))
exponentialPowerSeriesIsAbsolutelyCauchyAtNonnegativeRational
  radius 0≤radius =
  exponentialPowerSeriesIsAbsolutelyCauchyAtRationalWithin
    radius 0≤radius (fst cutoff) (snd cutoff)
  where
  cutoff : Σ[ start ∈ ℕ ]
    radius ℚ.< naturalRational (suc start)
  cutoff = naturalCutoffAboveNonnegativeRational radius 0≤radius


exponentialPowerSeriesUniformlyAbsolutelyCauchyAtNonnegativeRational :
  ∀ radius → 0 ℚ.≤ radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    exponentialCoefficients (Real.ιℚ radius)
exponentialPowerSeriesUniformlyAbsolutelyCauchyAtNonnegativeRational
  radius 0≤radius =
  powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
    exponentialCoefficients exponentialCoefficients (Real.ιℚ radius)
    (nonnegativeCoefficientsSelfMajorized
      exponentialCoefficients exponentialCoefficients-nonnegative)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius))
      (exponentialPowerSeriesIsAbsolutelyCauchyAtNonnegativeRational
        radius 0≤radius))


exponentialPowerSeriesUniformlyCauchyAtNonnegativeRational :
  ∀ radius → 0 ℚ.≤ radius →
  PowerSeriesUniformlyCauchyOnRadius
    exponentialCoefficients (Real.ιℚ radius)
exponentialPowerSeriesUniformlyCauchyAtNonnegativeRational radius 0≤radius =
  powerSeriesUniformlyCauchyByCoefficientMajorant
    exponentialCoefficients exponentialCoefficients (Real.ιℚ radius)
    (nonnegativeCoefficientsSelfMajorized
      exponentialCoefficients exponentialCoefficients-nonnegative)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms exponentialCoefficients (Real.ιℚ radius))
      (exponentialPowerSeriesIsAbsolutelyCauchyAtNonnegativeRational
        radius 0≤radius))


exponentialPowerSeriesIsAbsolutelyCauchyAtPositiveRational : ∀ radius →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients (Real.ιℚ (fst radius)))
exponentialPowerSeriesIsAbsolutelyCauchyAtPositiveRational radius =
  exponentialPowerSeriesIsAbsolutelyCauchyAtRationalWithin
    (fst radius)
    (ℚ.<Weaken≤ 0 (fst radius) (snd radius))
    start
    radius<start
  where
  ceiling : Σ[ k ∈ ℕ₊₁ ]
    fst radius ℚ.< naturalRational (ℕ₊₁→ℕ k)
  ceiling = ceilℚ₊ radius

  start : ℕ
  start = fst ceiling .ℕ₊₁.n

  radius<start :
    fst radius ℚ.< naturalRational (suc start)
  radius<start = snd ceiling


exponentialPowerSeriesIsCauchyAtPositiveRational : ∀ radius →
  IsCauchySeries
    (powerSeriesTerms exponentialCoefficients (Real.ιℚ (fst radius)))
exponentialPowerSeriesIsCauchyAtPositiveRational radius =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms exponentialCoefficients (Real.ιℚ (fst radius)))
    (exponentialPowerSeriesIsAbsolutelyCauchyAtPositiveRational radius)


exponentialPowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational :
  ∀ radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    exponentialCoefficients (Real.ιℚ (fst radius))
exponentialPowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational radius =
  powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
    exponentialCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius))
    (nonnegativeCoefficientsSelfMajorized
      exponentialCoefficients exponentialCoefficients-nonnegative)
    (exponentialPowerSeriesIsCauchyAtPositiveRational radius)


exponentialPowerSeriesUniformlyCauchyAtPositiveRational :
  ∀ radius →
  PowerSeriesUniformlyCauchyOnRadius
    exponentialCoefficients (Real.ιℚ (fst radius))
exponentialPowerSeriesUniformlyCauchyAtPositiveRational radius =
  powerSeriesUniformlyCauchyByCoefficientMajorant
    exponentialCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius))
    (nonnegativeCoefficientsSelfMajorized
      exponentialCoefficients exponentialCoefficients-nonnegative)
    (exponentialPowerSeriesIsCauchyAtPositiveRational radius)


-- Every real point merely has a positive rational absolute-value bound.
-- Since Cauchyness is a proposition, the bound stays truncated: defining
-- the global exponential does not select a radius for each real input.

exponentialPowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsAbsolutelyCauchy x =
  PT.rec
    (isPropIsCauchySeries
      (Abs.absℝ ∘ powerSeriesTerms exponentialCoefficients x))
    from-bound
    (∃rationalBound x)
  where
  from-bound : RationalBound x →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms exponentialCoefficients x)
  from-bound (radius , absx≤radius) =
    powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
      exponentialCoefficients exponentialCoefficients
      x (Real.ιℚ (fst radius))
      (nonnegativeCoefficientsSelfMajorized
        exponentialCoefficients exponentialCoefficients-nonnegative)
      absx≤radius
      (exponentialPowerSeriesIsCauchyAtPositiveRational radius)


exponentialPowerSeriesIsCauchy : ∀ x →
  IsCauchySeries (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsCauchy x =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchy x)


exponentialPowerSeriesIsSummable : ∀ x →
  PowerSeriesSummableAt exponentialCoefficients x
exponentialPowerSeriesIsSummable x =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchy x)


expℝ : Real.ℝ → Real.ℝ
expℝ x =
  powerSeriesValue exponentialCoefficients x
    (exponentialPowerSeriesIsSummable x)


one≤expℝOfNonnegative : ∀ x →
  zeroℝ ≤ℝ x → Real.ιℚ 1 ≤ℝ expℝ x
one≤expℝOfNonnegative x 0≤x =
  subst
    (_≤ℝ expℝ x)
    partial-sum-one
    (partialSumLeSeriesSum terms summable nonnegative (suc zero))
  where
  terms : RealSequence
  terms = powerSeriesTerms exponentialCoefficients x

  summable : Summable terms
  summable = exponentialPowerSeriesIsSummable x

  nonnegative : ∀ n → zeroℝ ≤ℝ terms n
  nonnegative = exponentialPowerSeriesTerm-nonnegativeAt x 0≤x

  partial-sum-one :
    partialSum terms (suc zero) ≡ Real.ιℚ 1
  partial-sum-one =
      add-zero-left (terms zero)
    ∙ mul-one-right (exponentialCoefficients zero)
    ∙ exponentialCoefficient-zero


expℝPositiveOfNonnegative : ∀ x →
  zeroℝ ≤ℝ x → zeroℝ <ℝ expℝ x
expℝPositiveOfNonnegative x 0≤x =
  ≪≤ℝ-trans zeroℝ (Real.ιℚ 1) (expℝ x)
    (<ℚ→<ℝ 0 1 (ℚAbs.0<sucN zero))
    (one≤expℝOfNonnegative x 0≤x)


expℝOnClosedPositiveRationalRadius : ∀ radius →
  ClosedAbsRadius (Real.ιℚ (fst radius)) → Real.ℝ
expℝOnClosedPositiveRationalRadius radius =
  powerSeriesUniformValueOnClosedRadius
    exponentialCoefficients (Real.ιℚ (fst radius))
    (exponentialPowerSeriesUniformlyCauchyAtPositiveRational radius)


expℝOnClosedPositiveRationalRadius-agrees : ∀ radius point →
  expℝOnClosedPositiveRationalRadius radius point ≡
  expℝ (fst point)
expℝOnClosedPositiveRationalRadius-agrees radius point =
  seriesSumIndependent
    (powerSeriesTerms exponentialCoefficients (fst point))
    (cauchySeriesIsSummable
      (powerSeriesTerms exponentialCoefficients (fst point))
      (powerSeriesUniformlyCauchyAt
        exponentialCoefficients (Real.ιℚ (fst radius))
        (exponentialPowerSeriesUniformlyCauchyAtPositiveRational radius)
        point))
    (exponentialPowerSeriesIsSummable (fst point))


expℝOnClosedPositiveRationalRadiusIsContinuous : ∀ radius →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace (Real.ιℚ (fst radius))))
    (expℝOnClosedPositiveRationalRadius radius)
    (snd Real.ℝPremetricSpace)
expℝOnClosedPositiveRationalRadiusIsContinuous radius =
  powerSeriesUniformValueOnClosedRadiusIsContinuous
    exponentialCoefficients (Real.ιℚ (fst radius))
    (exponentialPowerSeriesUniformlyCauchyAtPositiveRational radius)


exponentialPowerSeriesUniformlyConvergesAtPositiveRational :
  ∀ radius →
  PowerSeriesUniformlyConvergesOnRadius
    exponentialCoefficients (Real.ιℚ (fst radius))
    (exponentialPowerSeriesUniformlyCauchyAtPositiveRational radius)
exponentialPowerSeriesUniformlyConvergesAtPositiveRational radius =
  powerSeriesUniformPartialSumsConverge
    exponentialCoefficients (Real.ιℚ (fst radius))
    (exponentialPowerSeriesUniformlyCauchyAtPositiveRational radius)


-- Retaining the uniform tail proof at every positive rational radius gives
-- strictly more reusable data than pointwise summability.  In particular,
-- the whole-line evaluator and its derivative can be built without choosing
-- a radius for each real input.

exponentialLocallyUniform :
  LocallyUniformPowerSeries exponentialCoefficients
exponentialLocallyUniform =
  exponentialPowerSeriesUniformlyCauchyAtPositiveRational


exponentialFormalDerivativeLocallyUniform :
  LocallyUniformPowerSeries
    (formalDerivative exponentialCoefficients)
exponentialFormalDerivativeLocallyUniform =
  subst LocallyUniformPowerSeries
    (sym formalDerivative-exponentialCoefficients)
    exponentialLocallyUniform


-- Nonnegativity makes the exponential coefficient sequence its own
-- coefficient majorant.  Its formal-derivative majorant is definitionally
-- the formal derivative, hence the coefficient recurrence transports the
-- already established Cauchy proof to the derivative majorant.

exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational :
  ∀ radius →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant exponentialCoefficients)
      (Real.ιℚ (fst radius)))
exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational radius =
  subst IsCauchySeries
    (sym (cong
      (λ coefficients →
        powerSeriesTerms coefficients (Real.ιℚ (fst radius)))
      formalDerivative-exponentialCoefficients))
    (exponentialPowerSeriesIsCauchyAtPositiveRational radius)


exponentialLocallyUniformDifferenceFactor :
  LocallyUniformPowerSeriesDifferenceFactor exponentialCoefficients
exponentialLocallyUniformDifferenceFactor radius =
  powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
    exponentialCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius))
    (nonnegativeCoefficientsSelfMajorized
      exponentialCoefficients exponentialCoefficients-nonnegative)
    (exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational radius)


expℝLocallyUniformValue : Real.ℝ → Real.ℝ
expℝLocallyUniformValue =
  locallyUniformPowerSeriesValue
    exponentialCoefficients exponentialLocallyUniform


-- The earlier pointwise definition and the locally-uniform evaluator use
-- different proofs of summability, but completeness makes a series limit
-- unique.  No compatibility choice between local radii is needed.

expℝ-agreesLocallyUniformValue : ∀ x →
  expℝ x ≡ expℝLocallyUniformValue x
expℝ-agreesLocallyUniformValue x =
  seriesSumIndependent
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsSummable x)
    ( expℝLocallyUniformValue x
    , locallyUniformPowerSeriesValueHasSum
        exponentialCoefficients exponentialLocallyUniform x
    )


expℝ≡expℝLocallyUniformValue : expℝ ≡ expℝLocallyUniformValue
expℝ≡expℝLocallyUniformValue =
  funExt expℝ-agreesLocallyUniformValue


exponentialFormalDerivativeLocallyUniformValue : Real.ℝ → Real.ℝ
exponentialFormalDerivativeLocallyUniformValue =
  locallyUniformPowerSeriesValue
    (formalDerivative exponentialCoefficients)
    exponentialFormalDerivativeLocallyUniform


exponentialFormalDerivativeLocallyUniformValue-agreesExpℝ : ∀ x →
  exponentialFormalDerivativeLocallyUniformValue x ≡ expℝ x
exponentialFormalDerivativeLocallyUniformValue-agreesExpℝ x =
  seriesSumIndependent
    (powerSeriesTerms exponentialCoefficients x)
    ( exponentialFormalDerivativeLocallyUniformValue x
    , derivative-value-has-exponential-sum
    )
    (exponentialPowerSeriesIsSummable x)
  where
  derivative-terms≡exponential-terms :
    powerSeriesTerms
      (formalDerivative exponentialCoefficients) x
      ≡
    powerSeriesTerms exponentialCoefficients x
  derivative-terms≡exponential-terms =
    cong (λ coefficients → powerSeriesTerms coefficients x)
      formalDerivative-exponentialCoefficients

  derivative-value-has-exponential-sum :
    HasSum
      (powerSeriesTerms exponentialCoefficients x)
      (exponentialFormalDerivativeLocallyUniformValue x)
  derivative-value-has-exponential-sum =
    subst
      (λ terms →
        HasSum terms
          (exponentialFormalDerivativeLocallyUniformValue x))
      derivative-terms≡exponential-terms
      (locallyUniformPowerSeriesValueHasSum
        (formalDerivative exponentialCoefficients)
        exponentialFormalDerivativeLocallyUniform x)


exponentialFormalDerivativeLocallyUniformValue≡expℝ :
  exponentialFormalDerivativeLocallyUniformValue ≡ expℝ
exponentialFormalDerivativeLocallyUniformValue≡expℝ =
  funExt exponentialFormalDerivativeLocallyUniformValue-agreesExpℝ


exponentialLocallyUniformHasFormalDerivative :
  IsDerivative
    expℝLocallyUniformValue
    exponentialFormalDerivativeLocallyUniformValue
exponentialLocallyUniformHasFormalDerivative =
  locallyUniformPowerSeriesHasFormalDerivative
    exponentialCoefficients
    exponentialLocallyUniform
    exponentialFormalDerivativeLocallyUniform
    exponentialLocallyUniformDifferenceFactor


-- Transporting both the function and its formal-derivative sum across the
-- canonical limit equalities yields the global differential equation.

expℝHasDerivativeSelf : IsDerivative expℝ expℝ
expℝHasDerivativeSelf =
  subst2 IsDerivative
    (sym expℝ≡expℝLocallyUniformValue)
    exponentialFormalDerivativeLocallyUniformValue≡expℝ
    exponentialLocallyUniformHasFormalDerivative
