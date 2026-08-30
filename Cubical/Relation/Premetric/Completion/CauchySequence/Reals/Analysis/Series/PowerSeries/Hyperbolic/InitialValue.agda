module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.InitialValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities


private
  module InitialValueAlgebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)

    derivative-shape : ∀ a b sine cosine →
      a · sine + b · cosine ≡ b · cosine + a · sine
    derivative-shape a b sine cosine = solve! R

    zero-shape : ∀ a b →
      a · 1r + b · 0r ≡ a
    zero-shape a b = solve! R

    translate-shape : ∀ a b cx sx cy sy →
      a · (cx · cy + sx · sy) +
        b · (sx · cy + cx · sy)
        ≡
      (a · cx + b · sx) · cy +
        (b · cx + a · sx) · sy
    translate-shape a b cx sx cy sy = solve! R

    negate-shape : ∀ a b cosine sine →
      a · cosine + b · (- sine)
        ≡ a · cosine + (- b) · sine
    negate-shape a b cosine sine = solve! R

    add-parameters-shape : ∀ a b c d cosine sine →
      (a + c) · cosine + (b + d) · sine
        ≡ (a · cosine + b · sine) +
          (c · cosine + d · sine)
    add-parameters-shape a b c d cosine sine = solve! R

    scale-parameters-shape : ∀ scalar a b cosine sine →
      (scalar · a) · cosine + (scalar · b) · sine
        ≡ scalar · (a · cosine + b · sine)
    scale-parameters-shape scalar a b cosine sine = solve! R

    invariant-factorization : ∀ a b cosine sine →
      (a · cosine + b · sine) ·
          (a · cosine + b · sine) -
        (b · cosine + a · sine) ·
          (b · cosine + a · sine)
        ≡
      (a · a - b · b) ·
        (cosine · cosine - sine · sine)
    invariant-factorization a b cosine sine = solve! R


-- The coefficients are exactly the prescribed value and slope at zero.
-- Keeping this as a two-parameter construction packages the complete
-- algebraic solution family of the differential equation f'' = f.

hyperbolicInitialValue : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
hyperbolicInitialValue value slope x =
  (value Mul.· coshℝ x) Add.+ (slope Mul.· sinhℝ x)


hyperbolicInitialValueHasDerivativeSwap : ∀ value slope →
  IsDerivative
    (hyperbolicInitialValue value slope)
    (hyperbolicInitialValue slope value)
hyperbolicInitialValueHasDerivativeSwap value slope =
  subst
    (IsDerivative (hyperbolicInitialValue value slope))
    derivative-path
    (addHasDerivative
      ((value Mul.·_) ∘ coshℝ)
      ((slope Mul.·_) ∘ sinhℝ)
      ((value Mul.·_) ∘ sinhℝ)
      ((slope Mul.·_) ∘ coshℝ)
      (scaleHasDerivative coshℝ sinhℝ value
        coshℝHasDerivativeSinhℝ)
      (scaleHasDerivative sinhℝ coshℝ slope
        sinhℝHasDerivativeCoshℝ))
  where
  derivative-path :
    (λ x →
      (value Mul.· sinhℝ x) Add.+
        (slope Mul.· coshℝ x))
      ≡ hyperbolicInitialValue slope value
  derivative-path =
    funExt λ x →
      InitialValueAlgebra.derivative-shape ℝCommRing
        value slope (sinhℝ x) (coshℝ x)


hyperbolicInitialValueHasSecondDerivativeSelf : ∀ value slope →
  IsSecondDerivative
    (hyperbolicInitialValue value slope)
    (hyperbolicInitialValue slope value)
    (hyperbolicInitialValue value slope)
hyperbolicInitialValueHasSecondDerivativeSelf value slope =
  hyperbolicInitialValueHasDerivativeSwap value slope ,
  hyperbolicInitialValueHasDerivativeSwap slope value


hyperbolicInitialValue-zero : ∀ value slope →
  hyperbolicInitialValue value slope zeroℝ ≡ value
hyperbolicInitialValue-zero value slope =
    cong₂ Add._+_
      (cong (value Mul.·_) coshℝ-zero)
      (cong (slope Mul.·_) sinhℝ-zero)
  ∙ InitialValueAlgebra.zero-shape ℝCommRing value slope


hyperbolicInitialDerivative-zero : ∀ value slope →
  hyperbolicInitialValue slope value zeroℝ ≡ slope
hyperbolicInitialDerivative-zero value slope =
  hyperbolicInitialValue-zero slope value


-- Translation evolves the value/slope pair by the same construction.
-- This is the flow law for the first-order system (f,f')' = (f',f).

hyperbolicInitialValue-add : ∀ value slope x y →
  hyperbolicInitialValue value slope (x Add.+ y)
    ≡
  hyperbolicInitialValue
    (hyperbolicInitialValue value slope x)
    (hyperbolicInitialValue slope value x)
    y
hyperbolicInitialValue-add value slope x y =
    cong₂ Add._+_
      (cong (value Mul.·_) (coshℝ-add x y))
      (cong (slope Mul.·_) (sinhℝ-add x y))
  ∙ InitialValueAlgebra.translate-shape ℝCommRing
      value slope (coshℝ x) (sinhℝ x)
      (coshℝ y) (sinhℝ y)


hyperbolicInitialValue-neg : ∀ value slope x →
  hyperbolicInitialValue value slope (Neg.- x)
    ≡ hyperbolicInitialValue value (Neg.- slope) x
hyperbolicInitialValue-neg value slope x =
    cong₂ Add._+_
      (cong (value Mul.·_) (coshℝ-neg x))
      (cong (slope Mul.·_) (sinhℝ-neg x))
  ∙ InitialValueAlgebra.negate-shape ℝCommRing
      value slope (coshℝ x) (sinhℝ x)


-- Linearity in initial data makes the construction directly usable as a
-- solution operator, rather than merely as a collection of examples.

hyperbolicInitialValue-addParameters : ∀ a b c d x →
  hyperbolicInitialValue (a Add.+ c) (b Add.+ d) x
    ≡ hyperbolicInitialValue a b x Add.+
        hyperbolicInitialValue c d x
hyperbolicInitialValue-addParameters a b c d x =
  InitialValueAlgebra.add-parameters-shape ℝCommRing
    a b c d (coshℝ x) (sinhℝ x)


hyperbolicInitialValue-scaleParameters : ∀ scalar value slope x →
  hyperbolicInitialValue
      (scalar Mul.· value) (scalar Mul.· slope) x
    ≡ scalar Mul.· hyperbolicInitialValue value slope x
hyperbolicInitialValue-scaleParameters scalar value slope x =
  InitialValueAlgebra.scale-parameters-shape ℝCommRing
    scalar value slope (coshℝ x) (sinhℝ x)


-- The flow preserves the Lorentz quadratic form on value/slope pairs.
-- This strengthens the basic cosh²-sinh² identity to every solution.

hyperbolicInitialValue-invariant : ∀ value slope x →
  (hyperbolicInitialValue value slope x Mul.·
      hyperbolicInitialValue value slope x) Group.-
    (hyperbolicInitialValue slope value x Mul.·
      hyperbolicInitialValue slope value x)
    ≡ (value Mul.· value) Group.- (slope Mul.· slope)
hyperbolicInitialValue-invariant value slope x =
    InitialValueAlgebra.invariant-factorization ℝCommRing
      value slope (coshℝ x) (sinhℝ x)
  ∙ cong
      (((value Mul.· value) Group.- (slope Mul.· slope)) Mul.·_)
      (coshSquare-sub-sinhSquare≡one x)
  ∙ mul-one-right
      ((value Mul.· value) Group.- (slope Mul.· slope))


-- Pairing value and slope exposes the semigroup law as literal state
-- composition, convenient for later uniqueness and integration arguments.

hyperbolicState : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ × Real.ℝ
hyperbolicState value slope x =
  hyperbolicInitialValue value slope x ,
  hyperbolicInitialValue slope value x


hyperbolicState-zero : ∀ value slope →
  hyperbolicState value slope zeroℝ ≡ (value , slope)
hyperbolicState-zero value slope =
  cong₂ _,_
    (hyperbolicInitialValue-zero value slope)
    (hyperbolicInitialDerivative-zero value slope)


hyperbolicState-add : ∀ value slope x y →
  hyperbolicState value slope (x Add.+ y)
    ≡
  hyperbolicState
    (hyperbolicInitialValue value slope x)
    (hyperbolicInitialValue slope value x)
    y
hyperbolicState-add value slope x y =
  cong₂ _,_
    (hyperbolicInitialValue-add value slope x y)
    (hyperbolicInitialValue-add slope value x y)
