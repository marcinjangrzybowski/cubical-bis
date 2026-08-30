module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Order

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-comm)
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; mul-preserves≤-right-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (<ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference<)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Distance
  using (distance-sym)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- A derivative along a real-valued coordinate on an arbitrary premetric
-- parameter space.  This division-free formulation asks the first-order
-- error to be bounded by ε times the coordinate displacement.  It works on
-- subspaces without first constructing reciprocals of nonzero increments.

derivativeErrorAlong :
  ∀ {ℓ} {A : Type ℓ} →
  (coordinate function derivative : A → Real.ℝ) →
  A → A → Real.ℝ
derivativeErrorAlong coordinate function derivative x y =
  (function y Group.- function x) Group.-
    (derivative x Mul.· (coordinate y Group.- coordinate x))


IsDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ} →
  PremetricStr ℓ' A →
  (coordinate function derivative : A → Real.ℝ) →
  Type (ℓ-max ℓ ℓ')
IsDerivativeAlong source coordinate function derivative =
  ∀ x (ε : ℚ₊) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      PremetricStr._≈[_]_ source x δ y →
      Abs.absℝ
          (derivativeErrorAlong
            coordinate function derivative x y)
        ≤ℝ
      Real.ιℚ (fst ε) Mul.·
        Abs.absℝ (coordinate y Group.- coordinate x))


IsDerivative :
  (function derivative : Real.ℝ → Real.ℝ) → Type
IsDerivative =
  IsDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)


IsDerivativeAt :
  (function : Real.ℝ → Real.ℝ) →
  Real.ℝ → Real.ℝ → Type
IsDerivativeAt function derivative-value x =
  ∀ (ε : ℚ₊) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      x Real.Base.≈ᶜ[ δ ] y →
      Abs.absℝ
          ((function y Group.- function x) Group.-
            (derivative-value Mul.· (y Group.- x)))
        ≤ℝ
      Real.ιℚ (fst ε) Mul.· Abs.absℝ (y Group.- x))


isDerivativeAt :
  ∀ function derivative →
  IsDerivative function derivative →
  ∀ x →
  IsDerivativeAt function (derivative x) x
isDerivativeAt function derivative has-derivative x =
  has-derivative x


-- Differentiation along a coordinate is stable under continuous
-- reparameterisation.  Only the target neighbourhood is pulled back; no
-- modulus of continuity or derivative is selected globally.

pullbackHasDerivativeAlong :
  ∀ {ℓA ℓA' ℓB ℓB'}
    {A : Type ℓA} {B : Type ℓB}
    (source : PremetricStr ℓA' A)
    (target : PremetricStr ℓB' B)
    (coordinate function derivative : B → Real.ℝ)
    (map : A → B) →
  isContinuous source map target →
  IsDerivativeAlong target coordinate function derivative →
  IsDerivativeAlong
    source
    (coordinate ∘ map)
    (function ∘ map)
    (derivative ∘ map)
pullbackHasDerivativeAlong
  source target coordinate function derivative map
  map-continuous has-derivative x ε = do
    (δ , derivative-bound) ← has-derivative (map x) ε
    (η , map-near) ←
      map-continuous x .IsContinuousAt.pres≈ δ
    return
      ( η
      , λ y x≈y →
          derivative-bound (map y) (map-near y x≈y)
      )


private
  differenceFactorErrorPath :
    ∀ difference derivative-value factor-value →
    (difference Mul.· factor-value) Group.-
        (derivative-value Mul.· difference)
      ≡
    difference Mul.· (factor-value Group.- derivative-value)
  differenceFactorErrorPath
    difference derivative-value factor-value =
      cong
        (λ value →
          (difference Mul.· factor-value) Group.- value)
        (mul-comm derivative-value difference)
    ∙ sym
        (ℝRing.·DistR-
          difference factor-value derivative-value)


-- A continuous divided difference gives a derivative.  The theorem is
-- independent of power series and is reusable for polynomials and later
-- functions constructed by completion lifts.

continuousDifferenceFactorGivesDerivative :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → Real.ℝ)
    (factor : A × A → Real.ℝ) →
  (∀ x y →
    function y Group.- function x
      ≡
    (coordinate y Group.- coordinate x) Mul.· factor (x , y)) →
  (∀ x → factor (x , x) ≡ derivative x) →
  isContinuous
    (PremetricProductStr source source)
    factor
    (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate function derivative
continuousDifferenceFactorGivesDerivative
  source coordinate function derivative factor
  factorization diagonal factor-continuous
  x ε = do
    (δ , factor-preserves) ←
      factor-continuous (x , x) .IsContinuousAt.pres≈ ε
    return
      ( δ
      , λ y x≈y →
          factor-error-bound y
            (factor-preserves
              (x , y)
              ( PremetricStr.isRefl≈ source x δ
              , x≈y
              ))
      )
  where
  factor-error-path :
    ∀ y →
    derivativeErrorAlong coordinate function derivative x y
      ≡
    (coordinate y Group.- coordinate x) Mul.·
      (factor (x , y) Group.- factor (x , x))
  factor-error-path y =
      cong
        (Group._- (derivative x Mul.·
          (coordinate y Group.- coordinate x)))
        (factorization x y)
    ∙ differenceFactorErrorPath
        (coordinate y Group.- coordinate x)
        (derivative x)
        (factor (x , y))
    ∙ cong
        ((coordinate y Group.- coordinate x) Mul.·_)
        (cong (λ value → factor (x , y) Group.- value)
          (sym (diagonal x)))

  factor-difference-bound :
    ∀ y →
    factor (x , x) Real.Base.≈ᶜ[ ε ] factor (x , y) →
    Abs.absℝ (factor (x , y) Group.- factor (x , x))
      ≤ℝ Real.ιℚ (fst ε)
  factor-difference-bound y close =
    subst
      (_≤ℝ Real.ιℚ (fst ε))
      (distance-sym (factor (x , x)) (factor (x , y)))
      (<ℝ-weaken
        (Abs.absℝ (factor (x , x) Group.- factor (x , y)))
        (Real.ιℚ (fst ε))
        (closeness→absDifference<
          (factor (x , x)) (factor (x , y)) ε close))

  factor-error-bound :
    ∀ y →
    factor (x , x) Real.Base.≈ᶜ[ ε ] factor (x , y) →
    Abs.absℝ
        (derivativeErrorAlong coordinate function derivative x y)
      ≤ℝ
    Real.ιℚ (fst ε) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x)
  factor-error-bound y close =
    subst2 _≤ℝ_
      (sym
        ( cong Abs.absℝ (factor-error-path y)
        ∙ abs-mul
            (coordinate y Group.- coordinate x)
            (factor (x , y) Group.- factor (x , x))
        ∙ mul-comm
            (Abs.absℝ (coordinate y Group.- coordinate x))
            (Abs.absℝ
              (factor (x , y) Group.- factor (x , x)))))
      refl
      (mul-preserves≤-right-nonnegative
        (Abs.absℝ (factor (x , y) Group.- factor (x , x)))
        (Real.ιℚ (fst ε))
        (Abs.absℝ (coordinate y Group.- coordinate x))
        (factor-difference-bound y close)
        (zero≤abs (coordinate y Group.- coordinate x)))
