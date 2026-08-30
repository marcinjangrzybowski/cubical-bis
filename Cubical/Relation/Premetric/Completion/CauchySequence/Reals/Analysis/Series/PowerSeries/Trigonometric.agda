module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing using (CommRing→Ring)
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; doubleℕ ; _+_)
open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
  using (neg-zero)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using
    ( mul-nonnegative
    ; nonnegative→abs-self
    ; mul-preserves≤-left-nonnegative
    ; mul-preserves≤-right-nonnegative
    )
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative


private
  module ℝRing = Ring.RingTheory (CommRing→Ring ℝCommRing)

  oneℝ : Real.ℝ
  oneℝ = Real.ιℚ 1


-- Coefficientwise alternation is useful independently of parity masking.
-- Formal differentiation reverses its sign, exactly as substitution
-- x ↦ -x does for a convergent power series.

alternateCoefficients : RealSequence → RealSequence
alternateCoefficients coefficients n =
  ℝRing.alternate n (coefficients n)


abs-alternate : ∀ n value →
  Abs.absℝ (ℝRing.alternate n value) ≡ Abs.absℝ value
abs-alternate zero value = refl
abs-alternate (suc n) value =
    cong Abs.absℝ (ℝRing.alternate-suc n value)
  ∙ Abs.absℝ-neg (ℝRing.alternate n value)
  ∙ abs-alternate n value


alternateCoefficientsPresMajorant : ∀ coefficients majorant →
  CoefficientMajorizedBy coefficients majorant →
  CoefficientMajorizedBy
    (alternateCoefficients coefficients) majorant
alternateCoefficientsPresMajorant coefficients majorant majorized n =
  subst
    (_≤ℝ majorant n)
    (sym (abs-alternate n (coefficients n)))
    (majorized n)


-- Parity transforms -----------------------------------------------------
--
-- These transformations do more than select a subsequence.  They retain
-- the original degree and put zero in the other parity, while changing the
-- sign every two degrees.  Thus they turn any formal-derivative fixed point
-- into the sine/cosine four-cycle.

alternatingEvenCoefficients : RealSequence → RealSequence
alternatingEvenCoefficients coefficients zero = coefficients zero
alternatingEvenCoefficients coefficients (suc zero) = zeroℝ
alternatingEvenCoefficients coefficients (suc (suc n)) =
  Neg.- alternatingEvenCoefficients
    (coefficients ∘ suc ∘ suc) n


alternatingOddCoefficients : RealSequence → RealSequence
alternatingOddCoefficients coefficients zero = zeroℝ
alternatingOddCoefficients coefficients (suc zero) = coefficients (suc zero)
alternatingOddCoefficients coefficients (suc (suc n)) =
  Neg.- alternatingOddCoefficients
    (coefficients ∘ suc ∘ suc) n


alternatingEvenCoefficients-even : ∀ coefficients n →
  alternatingEvenCoefficients coefficients (doubleℕ n)
  ≡ ℝRing.alternate n (coefficients (doubleℕ n))
alternatingEvenCoefficients-even coefficients zero = refl
alternatingEvenCoefficients-even coefficients (suc n) =
    cong Neg.-_
      (alternatingEvenCoefficients-even
        (coefficients ∘ suc ∘ suc) n)
  ∙ sym
      (ℝRing.alternate-suc n
        (coefficients (suc (suc (doubleℕ n)))))


alternatingEvenCoefficients-odd : ∀ coefficients n →
  alternatingEvenCoefficients coefficients (suc (doubleℕ n))
  ≡ zeroℝ
alternatingEvenCoefficients-odd coefficients zero = refl
alternatingEvenCoefficients-odd coefficients (suc n) =
  cong Neg.-_
    (alternatingEvenCoefficients-odd
      (coefficients ∘ suc ∘ suc) n)
  ∙ neg-zero


alternatingOddCoefficients-even : ∀ coefficients n →
  alternatingOddCoefficients coefficients (doubleℕ n)
  ≡ zeroℝ
alternatingOddCoefficients-even coefficients zero = refl
alternatingOddCoefficients-even coefficients (suc n) =
  cong Neg.-_
    (alternatingOddCoefficients-even
      (coefficients ∘ suc ∘ suc) n)
  ∙ neg-zero


alternatingOddCoefficients-odd : ∀ coefficients n →
  alternatingOddCoefficients coefficients (suc (doubleℕ n))
  ≡ ℝRing.alternate n (coefficients (suc (doubleℕ n)))
alternatingOddCoefficients-odd coefficients zero = refl
alternatingOddCoefficients-odd coefficients (suc n) =
    cong Neg.-_
      (alternatingOddCoefficients-odd
        (coefficients ∘ suc ∘ suc) n)
  ∙ sym
      (ℝRing.alternate-suc n
        (coefficients (suc (suc (suc (doubleℕ n))))))


mul-alternate-right : ∀ scalar n value →
  scalar Mul.· ℝRing.alternate n value
  ≡ ℝRing.alternate n (scalar Mul.· value)
mul-alternate-right scalar zero value = refl
mul-alternate-right scalar (suc n) value =
    cong (scalar Mul.·_) (ℝRing.alternate-suc n value)
  ∙ ℝRing.-DistR· scalar (ℝRing.alternate n value)
  ∙ cong Neg.-_ (mul-alternate-right scalar n value)
  ∙ sym (ℝRing.alternate-suc n (scalar Mul.· value))


formalDerivative-alternateCoefficients : ∀ coefficients →
  formalDerivative (alternateCoefficients coefficients)
  ≡ (Neg.-_ ∘ alternateCoefficients
      (formalDerivative coefficients))
formalDerivative-alternateCoefficients coefficients =
  funExt λ n →
      cong
        (realNatural (suc n) Mul.·_)
        (ℝRing.alternate-suc n (coefficients (suc n)))
    ∙ ℝRing.-DistR·
        (realNatural (suc n))
        (ℝRing.alternate n (coefficients (suc n)))
    ∙ cong Neg.-_
        (mul-alternate-right
          (realNatural (suc n)) n (coefficients (suc n)))


data Parity : ℕ → Type₀ where
  even : ∀ n → Parity (doubleℕ n)
  odd  : ∀ n → Parity (suc (doubleℕ n))


parity : ∀ n → Parity n
parity zero = even zero
parity (suc zero) = odd zero
parity (suc (suc n)) with parity n
... | even k = even (suc k)
... | odd k = odd (suc k)


-- The coefficient-level derivative cycle is independent of convergence.
-- This separation is useful later: one convergence proof for a
-- derivative-fixed majorant supplies both trigonometric functions.

formalDerivative-alternatingOdd : ∀ coefficients →
  formalDerivative coefficients ≡ coefficients →
  formalDerivative (alternatingOddCoefficients coefficients)
  ≡ alternatingEvenCoefficients coefficients
formalDerivative-alternatingOdd coefficients fixed =
  funExt pointwise
  where
  at-even : ∀ k →
    formalDerivative
        (alternatingOddCoefficients coefficients) (doubleℕ k)
      ≡
    alternatingEvenCoefficients coefficients (doubleℕ k)
  at-even k =
      cong
        (realNatural (suc (doubleℕ k)) Mul.·_)
        (alternatingOddCoefficients-odd coefficients k)
    ∙ mul-alternate-right
        (realNatural (suc (doubleℕ k))) k
        (coefficients (suc (doubleℕ k)))
    ∙ cong (ℝRing.alternate k)
        (funExt⁻ fixed (doubleℕ k))
    ∙ sym (alternatingEvenCoefficients-even coefficients k)

  at-odd : ∀ k →
    formalDerivative
        (alternatingOddCoefficients coefficients) (suc (doubleℕ k))
      ≡
    alternatingEvenCoefficients coefficients (suc (doubleℕ k))
  at-odd k =
      cong
        (realNatural (suc (suc (doubleℕ k))) Mul.·_)
        (alternatingOddCoefficients-even coefficients (suc k))
    ∙ mul-zero-right (realNatural (suc (suc (doubleℕ k))))
    ∙ sym (alternatingEvenCoefficients-odd coefficients k)

  pointwise : ∀ n →
    formalDerivative (alternatingOddCoefficients coefficients) n
    ≡ alternatingEvenCoefficients coefficients n
  pointwise n with parity n
  ... | even k = at-even k
  ... | odd k = at-odd k


formalDerivative-alternatingEven : ∀ coefficients →
  formalDerivative coefficients ≡ coefficients →
  formalDerivative (alternatingEvenCoefficients coefficients)
  ≡ (Neg.-_ ∘ alternatingOddCoefficients coefficients)
formalDerivative-alternatingEven coefficients fixed =
  funExt pointwise
  where
  at-even : ∀ k →
    formalDerivative
        (alternatingEvenCoefficients coefficients) (doubleℕ k)
      ≡
    Neg.- alternatingOddCoefficients coefficients (doubleℕ k)
  at-even k =
      cong
        (realNatural (suc (doubleℕ k)) Mul.·_)
        (alternatingEvenCoefficients-odd coefficients k)
    ∙ mul-zero-right (realNatural (suc (doubleℕ k)))
    ∙ sym neg-zero
    ∙ cong Neg.-_
        (sym (alternatingOddCoefficients-even coefficients k))

  at-odd : ∀ k →
    formalDerivative
        (alternatingEvenCoefficients coefficients) (suc (doubleℕ k))
      ≡
    Neg.- alternatingOddCoefficients coefficients (suc (doubleℕ k))
  at-odd k =
      cong
        (realNatural (suc (suc (doubleℕ k))) Mul.·_)
        (alternatingEvenCoefficients-even coefficients (suc k))
    ∙ mul-alternate-right
        (realNatural (suc (suc (doubleℕ k)))) (suc k)
        (coefficients (suc (suc (doubleℕ k))))
    ∙ cong (ℝRing.alternate (suc k))
        (funExt⁻ fixed (suc (doubleℕ k)))
    ∙ ℝRing.alternate-suc k
        (coefficients (suc (doubleℕ k)))
    ∙ cong Neg.-_
        (sym (alternatingOddCoefficients-odd coefficients k))

  pointwise : ∀ n →
    formalDerivative (alternatingEvenCoefficients coefficients) n
    ≡ Neg.- alternatingOddCoefficients coefficients n
  pointwise n with parity n
  ... | even k = at-even k
  ... | odd k = at-odd k


sineCoefficients cosineCoefficients : RealSequence
sineCoefficients =
  alternatingOddCoefficients exponentialCoefficients
cosineCoefficients =
  alternatingEvenCoefficients exponentialCoefficients


formalDerivative-sineCoefficients :
  formalDerivative sineCoefficients ≡ cosineCoefficients
formalDerivative-sineCoefficients =
  formalDerivative-alternatingOdd
    exponentialCoefficients
    formalDerivative-exponentialCoefficients


formalDerivative-cosineCoefficients :
  formalDerivative cosineCoefficients ≡ (Neg.-_ ∘ sineCoefficients)
formalDerivative-cosineCoefficients =
  formalDerivative-alternatingEven
    exponentialCoefficients
    formalDerivative-exponentialCoefficients


negateCoefficients : RealSequence → RealSequence
negateCoefficients coefficients = Neg.-_ ∘ coefficients


formalDerivative-negateCoefficients : ∀ coefficients →
  formalDerivative (negateCoefficients coefficients)
  ≡ negateCoefficients (formalDerivative coefficients)
formalDerivative-negateCoefficients coefficients =
  funExt λ n →
    ℝRing.-DistR·
      (realNatural (suc n)) (coefficients (suc n))


formalSecondDerivative : RealSequence → RealSequence
formalSecondDerivative coefficients =
  formalDerivative (formalDerivative coefficients)


formalSecondDerivative-sineCoefficients :
  formalSecondDerivative sineCoefficients
  ≡ negateCoefficients sineCoefficients
formalSecondDerivative-sineCoefficients =
    cong formalDerivative formalDerivative-sineCoefficients
  ∙ formalDerivative-cosineCoefficients


formalSecondDerivative-cosineCoefficients :
  formalSecondDerivative cosineCoefficients
  ≡ negateCoefficients cosineCoefficients
formalSecondDerivative-cosineCoefficients =
    cong formalDerivative formalDerivative-cosineCoefficients
  ∙ formalDerivative-negateCoefficients sineCoefficients
  ∙ cong negateCoefficients formalDerivative-sineCoefficients


-- Absolute convergence is shared through the original coefficient
-- sequence.  The proof is structural and applies to arbitrary nonnegative
-- coefficients; it is not tied to factorials.

alternatingEvenCoefficients-majorized : ∀ coefficients →
  NonnegativeCoefficients coefficients →
  CoefficientMajorizedBy
    (alternatingEvenCoefficients coefficients) coefficients
alternatingEvenCoefficients-majorized coefficients nonnegative zero =
  subst
    (_≤ℝ coefficients zero)
    (sym
      (nonnegative→abs-self
        (coefficients zero) (nonnegative zero)))
    (≤ℝ-refl (coefficients zero))
alternatingEvenCoefficients-majorized
    coefficients nonnegative (suc zero) =
  subst
    (_≤ℝ coefficients (suc zero))
    (sym Abs.absℝ-zero)
    (nonnegative (suc zero))
alternatingEvenCoefficients-majorized
    coefficients nonnegative (suc (suc n)) =
  subst
    (_≤ℝ coefficients (suc (suc n)))
    (sym
      (Abs.absℝ-neg
        (alternatingEvenCoefficients
          (coefficients ∘ suc ∘ suc) n)))
    (alternatingEvenCoefficients-majorized
      (coefficients ∘ suc ∘ suc)
      (nonnegative ∘ suc ∘ suc) n)


alternatingOddCoefficients-majorized : ∀ coefficients →
  NonnegativeCoefficients coefficients →
  CoefficientMajorizedBy
    (alternatingOddCoefficients coefficients) coefficients
alternatingOddCoefficients-majorized
    coefficients nonnegative zero =
  subst
    (_≤ℝ coefficients zero)
    (sym Abs.absℝ-zero)
    (nonnegative zero)
alternatingOddCoefficients-majorized
    coefficients nonnegative (suc zero) =
  subst
    (_≤ℝ coefficients (suc zero))
    (sym
      (nonnegative→abs-self
        (coefficients (suc zero)) (nonnegative (suc zero))))
    (≤ℝ-refl (coefficients (suc zero)))
alternatingOddCoefficients-majorized
    coefficients nonnegative (suc (suc n)) =
  subst
    (_≤ℝ coefficients (suc (suc n)))
    (sym
      (Abs.absℝ-neg
        (alternatingOddCoefficients
          (coefficients ∘ suc ∘ suc) n)))
    (alternatingOddCoefficients-majorized
      (coefficients ∘ suc ∘ suc)
      (nonnegative ∘ suc ∘ suc) n)


sineCoefficients-majorized :
  CoefficientMajorizedBy
    sineCoefficients exponentialCoefficients
sineCoefficients-majorized =
  alternatingOddCoefficients-majorized
    exponentialCoefficients
    exponentialCoefficients-nonnegative


cosineCoefficients-majorized :
  CoefficientMajorizedBy
    cosineCoefficients exponentialCoefficients
cosineCoefficients-majorized =
  alternatingEvenCoefficients-majorized
    exponentialCoefficients
    exponentialCoefficients-nonnegative


-- Eventual ratio criterion ---------------------------------------------
--
-- Keeping the cutoff and ratio as data gives a theorem with no countable
-- choice hidden in it.  Applications may obtain a single cutoff under a
-- truncation and eliminate it because summability is a proposition.

TailRatioBoundFrom :
  ℕ → Real.ℝ → RealSequence → Type₀
TailRatioBoundFrom start ratio terms =
  ∀ n →
  dropSeries start terms (suc n) ≤ℝ
  ratio Mul.· dropSeries start terms n


geometricTailUpperBound : ∀ start ratio terms →
  (zero≤ratio : zeroℝ ≤ℝ ratio) →
  TailRatioBoundFrom start ratio terms →
  ∀ n →
  dropSeries start terms n ≤ℝ
  scaleSeries (terms start) (geometricTerms ratio) n
geometricTailUpperBound
    start ratio terms zero≤ratio ratio-bound zero =
  subst
    (dropSeries start terms zero ≤ℝ_)
    (sym (mul-one-right (terms start)))
    (≤ℝ-refl (terms start))
geometricTailUpperBound
    start ratio terms zero≤ratio ratio-bound (suc n) =
  ≤ℝ-trans
    (dropSeries start terms (suc n))
    (ratio Mul.· dropSeries start terms n)
    (scaleSeries (terms start) (geometricTerms ratio) (suc n))
    (ratio-bound n)
    (subst
      ( (ratio Mul.· dropSeries start terms n) ≤ℝ_)
      rearrange
      (mul-preserves≤-left-nonnegative
        (dropSeries start terms n)
        (scaleSeries
          (terms start) (geometricTerms ratio) n)
        ratio
        (geometricTailUpperBound
          start ratio terms zero≤ratio ratio-bound n)
        zero≤ratio))
  where
  rearrange :
    ratio Mul.·
      scaleSeries (terms start) (geometricTerms ratio) n
    ≡
    scaleSeries (terms start) (geometricTerms ratio) (suc n)
  rearrange =
      mul-assoc ratio (terms start) (ratio ^ⁿ n)
    ∙ cong (Mul._· ratio ^ⁿ n)
        (mul-comm ratio (terms start))
    ∙ sym (mul-assoc (terms start) ratio (ratio ^ⁿ n))


tailRatioBoundIsSummable : ∀ start ratio terms →
  NonnegativeCoefficients terms →
  zeroℝ ≤ℝ ratio →
  TailRatioBoundFrom start ratio terms →
  RationalContractionBound ratio →
  Summable terms
tailRatioBoundIsSummable
    start ratio terms terms-nonnegative zero≤ratio
    ratio-bound contraction =
  dropSeriesReflectsSummable start terms
    (dominatedCauchySeriesIsSummable
      (dropSeries start terms)
      (scaleSeries (terms start) (geometricTerms ratio))
      dominates
      (scaleSeriesIsCauchy
        (terms start) (geometricTerms ratio)
        (geometricSeriesIsCauchyByRationalContraction
          ratio contraction)))
  where
  dominates : ∀ n →
    Abs.absℝ (dropSeries start terms n) ≤ℝ
    scaleSeries (terms start) (geometricTerms ratio) n
  dominates n =
    subst
      (_≤ℝ scaleSeries
        (terms start) (geometricTerms ratio) n)
      (sym
        (nonnegative→abs-self
          (dropSeries start terms n)
          (terms-nonnegative (n ℕ.+ start))))
      (geometricTailUpperBound
        start ratio terms zero≤ratio ratio-bound n)


-- Both alternating parity series inherit convergence from the canonical
-- exponential series.  One majorant proof is shared by pointwise, uniform,
-- derivative and divided-difference convergence.

sinePowerSeriesIsAbsolutelyCauchyByExponentialMajorant :
  ∀ x radius →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms exponentialCoefficients radius) →
  IsAbsolutelyCauchySeries (powerSeriesTerms sineCoefficients x)
sinePowerSeriesIsAbsolutelyCauchyByExponentialMajorant
    x radius absx≤radius factorial-cauchy =
  powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
    sineCoefficients exponentialCoefficients
    x radius sineCoefficients-majorized
    absx≤radius factorial-cauchy


cosinePowerSeriesIsAbsolutelyCauchyByExponentialMajorant :
  ∀ x radius →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms exponentialCoefficients radius) →
  IsAbsolutelyCauchySeries (powerSeriesTerms cosineCoefficients x)
cosinePowerSeriesIsAbsolutelyCauchyByExponentialMajorant
    x radius absx≤radius factorial-cauchy =
  powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
    cosineCoefficients exponentialCoefficients
    x radius cosineCoefficients-majorized
    absx≤radius factorial-cauchy


sinePowerSeriesSummableByExponentialMajorant :
  ∀ x radius →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms exponentialCoefficients radius) →
  PowerSeriesSummableAt sineCoefficients x
sinePowerSeriesSummableByExponentialMajorant
    x radius absx≤radius factorial-cauchy =
  powerSeriesIsSummableByCoefficientMajorant
    sineCoefficients exponentialCoefficients
    x radius sineCoefficients-majorized
    absx≤radius factorial-cauchy


cosinePowerSeriesSummableByExponentialMajorant :
  ∀ x radius →
  Abs.absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms exponentialCoefficients radius) →
  PowerSeriesSummableAt cosineCoefficients x
cosinePowerSeriesSummableByExponentialMajorant
    x radius absx≤radius factorial-cauchy =
  powerSeriesIsSummableByCoefficientMajorant
    cosineCoefficients exponentialCoefficients
    x radius cosineCoefficients-majorized
    absx≤radius factorial-cauchy


SinePowerSeriesSummableAt CosinePowerSeriesSummableAt :
  Real.ℝ → Type₀
SinePowerSeriesSummableAt = PowerSeriesSummableAt sineCoefficients
CosinePowerSeriesSummableAt = PowerSeriesSummableAt cosineCoefficients


sinePowerSeriesValue : ∀ x →
  SinePowerSeriesSummableAt x → Real.ℝ
sinePowerSeriesValue = powerSeriesValue sineCoefficients


cosinePowerSeriesValue : ∀ x →
  CosinePowerSeriesSummableAt x → Real.ℝ
cosinePowerSeriesValue = powerSeriesValue cosineCoefficients


-- Total convergence -----------------------------------------------------

sinePowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries (powerSeriesTerms sineCoefficients x)
sinePowerSeriesIsAbsolutelyCauchy x =
  sinePowerSeriesIsAbsolutelyCauchyByExponentialMajorant
    x (Abs.absℝ x) (≤ℝ-refl (Abs.absℝ x))
    (exponentialPowerSeriesIsCauchy (Abs.absℝ x))


cosinePowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries (powerSeriesTerms cosineCoefficients x)
cosinePowerSeriesIsAbsolutelyCauchy x =
  cosinePowerSeriesIsAbsolutelyCauchyByExponentialMajorant
    x (Abs.absℝ x) (≤ℝ-refl (Abs.absℝ x))
    (exponentialPowerSeriesIsCauchy (Abs.absℝ x))


sinePowerSeriesIsCauchy : ∀ x →
  IsCauchySeries (powerSeriesTerms sineCoefficients x)
sinePowerSeriesIsCauchy x =
  absoluteCauchySeriesIsCauchy _
    (sinePowerSeriesIsAbsolutelyCauchy x)


cosinePowerSeriesIsCauchy : ∀ x →
  IsCauchySeries (powerSeriesTerms cosineCoefficients x)
cosinePowerSeriesIsCauchy x =
  absoluteCauchySeriesIsCauchy _
    (cosinePowerSeriesIsAbsolutelyCauchy x)


sinePowerSeriesIsSummable : ∀ x →
  SinePowerSeriesSummableAt x
sinePowerSeriesIsSummable x =
  absoluteCauchySeriesIsSummable _
    (sinePowerSeriesIsAbsolutelyCauchy x)


cosinePowerSeriesIsSummable : ∀ x →
  CosinePowerSeriesSummableAt x
cosinePowerSeriesIsSummable x =
  absoluteCauchySeriesIsSummable _
    (cosinePowerSeriesIsAbsolutelyCauchy x)


sinePowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational :
  ∀ radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    sineCoefficients (Real.ιℚ (fst radius))
sinePowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational radius =
  powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
    sineCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius)) sineCoefficients-majorized
    (exponentialPowerSeriesIsCauchyAtPositiveRational radius)


cosinePowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational :
  ∀ radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    cosineCoefficients (Real.ιℚ (fst radius))
cosinePowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational radius =
  powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
    cosineCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius)) cosineCoefficients-majorized
    (exponentialPowerSeriesIsCauchyAtPositiveRational radius)


sineLocallyUniform : LocallyUniformPowerSeries sineCoefficients
sineLocallyUniform radius =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    _ _
    (sinePowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational radius)


cosineLocallyUniform : LocallyUniformPowerSeries cosineCoefficients
cosineLocallyUniform radius =
  uniformAbsoluteCauchySeriesIsUniformCauchy
    _ _
    (cosinePowerSeriesUniformlyAbsolutelyCauchyAtPositiveRational radius)


sineFormalDerivativeLocallyUniform :
  LocallyUniformPowerSeries (formalDerivative sineCoefficients)
sineFormalDerivativeLocallyUniform radius =
  formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
    sineCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius)) sineCoefficients-majorized
    (exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational radius)


cosineFormalDerivativeLocallyUniform :
  LocallyUniformPowerSeries (formalDerivative cosineCoefficients)
cosineFormalDerivativeLocallyUniform radius =
  formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
    cosineCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius)) cosineCoefficients-majorized
    (exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational radius)


sineLocallyUniformDifferenceFactor :
  LocallyUniformPowerSeriesDifferenceFactor sineCoefficients
sineLocallyUniformDifferenceFactor radius =
  powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
    sineCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius)) sineCoefficients-majorized
    (exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational radius)


cosineLocallyUniformDifferenceFactor :
  LocallyUniformPowerSeriesDifferenceFactor cosineCoefficients
cosineLocallyUniformDifferenceFactor radius =
  powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
    cosineCoefficients exponentialCoefficients
    (Real.ιℚ (fst radius)) cosineCoefficients-majorized
    (exponentialFormalDerivativeMajorantIsCauchyAtPositiveRational radius)


sinℝ cosℝ : Real.ℝ → Real.ℝ
sinℝ = locallyUniformPowerSeriesValue
  sineCoefficients sineLocallyUniform
cosℝ = locallyUniformPowerSeriesValue
  cosineCoefficients cosineLocallyUniform


sinℝHasSum : ∀ x →
  HasSum (powerSeriesTerms sineCoefficients x) (sinℝ x)
sinℝHasSum =
  locallyUniformPowerSeriesValueHasSum
    sineCoefficients sineLocallyUniform


cosℝHasSum : ∀ x →
  HasSum (powerSeriesTerms cosineCoefficients x) (cosℝ x)
cosℝHasSum =
  locallyUniformPowerSeriesValueHasSum
    cosineCoefficients cosineLocallyUniform


-- Compatibility with the earlier proof-parameterized evaluators.  This
-- keeps existing clients usable while making sinℝ and cosℝ the preferred
-- total interface.

sinePowerSeriesValue-agreesSinℝ : ∀ x summable →
  sinePowerSeriesValue x summable ≡ sinℝ x
sinePowerSeriesValue-agreesSinℝ x summable =
  seriesSumIndependent
    (powerSeriesTerms sineCoefficients x)
    summable
    (sinℝ x , sinℝHasSum x)


cosinePowerSeriesValue-agreesCosℝ : ∀ x summable →
  cosinePowerSeriesValue x summable ≡ cosℝ x
cosinePowerSeriesValue-agreesCosℝ x summable =
  seriesSumIndependent
    (powerSeriesTerms cosineCoefficients x)
    summable
    (cosℝ x , cosℝHasSum x)


-- Global derivative cycle ----------------------------------------------
--
-- Termwise differentiation first produces canonical sums for the formal
-- derivative coefficient sequences.  The coefficient identities above and
-- uniqueness of series sums then identify those opaque values with cosℝ and
-- - sinℝ.  Thus no choice of a convergence radius enters either public
-- derivative theorem.

sineFormalDerivativeValue cosineFormalDerivativeValue :
  Real.ℝ → Real.ℝ
sineFormalDerivativeValue =
  locallyUniformPowerSeriesValue
    (formalDerivative sineCoefficients)
    sineFormalDerivativeLocallyUniform
cosineFormalDerivativeValue =
  locallyUniformPowerSeriesValue
    (formalDerivative cosineCoefficients)
    cosineFormalDerivativeLocallyUniform


sineLocallyUniformHasFormalDerivative :
  IsDerivative sinℝ sineFormalDerivativeValue
sineLocallyUniformHasFormalDerivative =
  locallyUniformPowerSeriesHasFormalDerivative
    sineCoefficients
    sineLocallyUniform
    sineFormalDerivativeLocallyUniform
    sineLocallyUniformDifferenceFactor


cosineLocallyUniformHasFormalDerivative :
  IsDerivative cosℝ cosineFormalDerivativeValue
cosineLocallyUniformHasFormalDerivative =
  locallyUniformPowerSeriesHasFormalDerivative
    cosineCoefficients
    cosineLocallyUniform
    cosineFormalDerivativeLocallyUniform
    cosineLocallyUniformDifferenceFactor


sineFormalDerivativeValue-agreesCosℝ : ∀ x →
  sineFormalDerivativeValue x ≡ cosℝ x
sineFormalDerivativeValue-agreesCosℝ x =
  seriesSumIndependent
    (powerSeriesTerms cosineCoefficients x)
    ( sineFormalDerivativeValue x
    , derivative-value-has-cosine-sum
    )
    (cosℝ x , cosℝHasSum x)
  where
  derivative-terms≡cosine-terms :
    powerSeriesTerms (formalDerivative sineCoefficients) x
      ≡ powerSeriesTerms cosineCoefficients x
  derivative-terms≡cosine-terms =
    cong (λ coefficients → powerSeriesTerms coefficients x)
      formalDerivative-sineCoefficients

  derivative-value-has-cosine-sum :
    HasSum
      (powerSeriesTerms cosineCoefficients x)
      (sineFormalDerivativeValue x)
  derivative-value-has-cosine-sum =
    subst
      (λ terms → HasSum terms (sineFormalDerivativeValue x))
      derivative-terms≡cosine-terms
      (locallyUniformPowerSeriesValueHasSum
        (formalDerivative sineCoefficients)
        sineFormalDerivativeLocallyUniform x)


sineFormalDerivativeValue≡cosℝ :
  sineFormalDerivativeValue ≡ cosℝ
sineFormalDerivativeValue≡cosℝ =
  funExt sineFormalDerivativeValue-agreesCosℝ


sinℝHasDerivativeCosℝ : IsDerivative sinℝ cosℝ
sinℝHasDerivativeCosℝ =
  subst (IsDerivative sinℝ)
    sineFormalDerivativeValue≡cosℝ
    sineLocallyUniformHasFormalDerivative


-- Negating coefficients is scalar multiplication by -1.  Recording this
-- bridge once lets the ordinary linearity theorem for sums handle the
-- negative half of the derivative cycle.

negateCoefficients≡scaleNegOne : ∀ coefficients →
  negateCoefficients coefficients
    ≡ scaleSeries (Neg.- oneℝ) coefficients
negateCoefficients≡scaleNegOne coefficients =
  funExt λ n → ℝRing.-IsMult-1 (coefficients n)


powerSeriesTerms-negateCoefficients : ∀ coefficients x →
  powerSeriesTerms (negateCoefficients coefficients) x
    ≡ scaleSeries
        (Neg.- oneℝ) (powerSeriesTerms coefficients x)
powerSeriesTerms-negateCoefficients coefficients x =
    cong (λ c → powerSeriesTerms c x)
      (negateCoefficients≡scaleNegOne coefficients)
  ∙ powerSeriesTerms-scale-sequence
      (Neg.- oneℝ) coefficients x


negateCoefficientsHasSum : ∀ coefficients x value →
  HasSum (powerSeriesTerms coefficients x) value →
  HasSum
    (powerSeriesTerms (negateCoefficients coefficients) x)
    (Neg.- value)
negateCoefficientsHasSum coefficients x value terms-sum =
  subst2 HasSum
    (sym (powerSeriesTerms-negateCoefficients coefficients x))
    (sym (ℝRing.-IsMult-1 value))
    (scaleHasSum
      (Neg.- oneℝ) (powerSeriesTerms coefficients x)
      value terms-sum)


cosineFormalDerivativeValue-agreesNegativeSinℝ : ∀ x →
  cosineFormalDerivativeValue x ≡ Neg.- (sinℝ x)
cosineFormalDerivativeValue-agreesNegativeSinℝ x =
  seriesSumIndependent
    (powerSeriesTerms (negateCoefficients sineCoefficients) x)
    ( cosineFormalDerivativeValue x
    , derivative-value-has-negative-sine-sum
    )
    ( Neg.- (sinℝ x)
    , negateCoefficientsHasSum sineCoefficients x
        (sinℝ x) (sinℝHasSum x)
    )
  where
  derivative-terms≡negative-sine-terms :
    powerSeriesTerms (formalDerivative cosineCoefficients) x
      ≡
    powerSeriesTerms (negateCoefficients sineCoefficients) x
  derivative-terms≡negative-sine-terms =
    cong (λ coefficients → powerSeriesTerms coefficients x)
      formalDerivative-cosineCoefficients

  derivative-value-has-negative-sine-sum :
    HasSum
      (powerSeriesTerms (negateCoefficients sineCoefficients) x)
      (cosineFormalDerivativeValue x)
  derivative-value-has-negative-sine-sum =
    subst
      (λ terms → HasSum terms (cosineFormalDerivativeValue x))
      derivative-terms≡negative-sine-terms
      (locallyUniformPowerSeriesValueHasSum
        (formalDerivative cosineCoefficients)
        cosineFormalDerivativeLocallyUniform x)


cosineFormalDerivativeValue≡negativeSinℝ :
  cosineFormalDerivativeValue ≡ Neg.-_ ∘ sinℝ
cosineFormalDerivativeValue≡negativeSinℝ =
  funExt cosineFormalDerivativeValue-agreesNegativeSinℝ


cosℝHasDerivativeNegativeSinℝ :
  IsDerivative cosℝ (Neg.-_ ∘ sinℝ)
cosℝHasDerivativeNegativeSinℝ =
  subst (IsDerivative cosℝ)
    cosineFormalDerivativeValue≡negativeSinℝ
    cosineLocallyUniformHasFormalDerivative
