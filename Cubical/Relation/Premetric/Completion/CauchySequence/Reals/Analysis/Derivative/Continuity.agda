module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
  using (sub-add-cancel)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (abs-triangle ; add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; mul-preserves≤-right-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℚ→<ℝ ; ≤<ℝ-trans)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication
  using (mul-preserves≪-left-positive)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Distance
  using (distance-sym)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative


private
  derivativeErrorReconstructsDifference :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate function derivative : A → Real.ℝ)
      (x y : A) →
    derivativeErrorAlong coordinate function derivative x y Add.+
        (derivative x Mul.· (coordinate y Group.- coordinate x))
      ≡
    function y Group.- function x
  derivativeErrorReconstructsDifference
    coordinate function derivative x y =
    sub-add-cancel
      (function y Group.- function x)
      (derivative x Mul.· (coordinate y Group.- coordinate x))


-- At a selected bound for the derivative value, differentiability gives a
-- local linear estimate with coefficient `1 + B`.  The estimate is relative
-- to the coordinate; source continuity follows once that coordinate is
-- continuous.

derivativeAlongLocalLinearBoundAt :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → Real.ℝ) →
  IsDerivativeAlong source coordinate function derivative →
  ∀ x B →
  Abs.absℝ (derivative x) ≤ℝ Real.ιℚ (fst B) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      PremetricStr._≈[_]_ source x δ y →
      Abs.absℝ (function y Group.- function x)
        ≤ℝ
      Real.ιℚ (fst (1₊ +₊ B)) Mul.·
        Abs.absℝ (coordinate y Group.- coordinate x))
derivativeAlongLocalLinearBoundAt
  {A = A} source coordinate function derivative
  has-derivative x B derivative-bound = do
    (δ , error-bound) ← has-derivative x 1₊
    return
      ( δ
      , λ y x≈y → difference-bound y (error-bound y x≈y)
      )
  where
  distance : A → Real.ℝ
  distance y = Abs.absℝ (coordinate y Group.- coordinate x)

  coefficient-path : ∀ y →
    Real.ιℚ (fst (1₊ +₊ B)) Mul.· distance y
      ≡
    (Real.ιℚ 1 Mul.· distance y) Add.+
      (Real.ιℚ (fst B) Mul.· distance y)
  coefficient-path y =
      cong (Mul._· distance y)
        (sym (Add.add-ι-ι 1 (fst B)))
    ∙ mul-distrib-over-add-left
        (Real.ιℚ 1) (Real.ιℚ (fst B)) (distance y)

  linear-bound : ∀ y →
    Abs.absℝ
      (derivative x Mul.· (coordinate y Group.- coordinate x))
      ≤ℝ
    Real.ιℚ (fst B) Mul.· distance y
  linear-bound y =
    subst
      (_≤ℝ Real.ιℚ (fst B) Mul.· distance y)
      (sym
        (abs-mul
          (derivative x) (coordinate y Group.- coordinate x)))
      (mul-preserves≤-right-nonnegative
        (Abs.absℝ (derivative x))
        (Real.ιℚ (fst B))
        (distance y)
        derivative-bound
        (zero≤abs (coordinate y Group.- coordinate x)))

  difference-bound : ∀ y →
    Abs.absℝ
      (derivativeErrorAlong coordinate function derivative x y)
      ≤ℝ Real.ιℚ 1 Mul.· distance y →
    Abs.absℝ (function y Group.- function x)
      ≤ℝ
    Real.ιℚ (fst (1₊ +₊ B)) Mul.· distance y
  difference-bound y error-bound =
    subst
      (λ value →
        Abs.absℝ value ≤ℝ
          Real.ιℚ (fst (1₊ +₊ B)) Mul.· distance y)
      (derivativeErrorReconstructsDifference
        coordinate function derivative x y)
      (≤ℝ-trans
        (Abs.absℝ
          (derivativeErrorAlong coordinate function derivative x y Add.+
            (derivative x Mul.·
              (coordinate y Group.- coordinate x))))
        (Abs.absℝ
            (derivativeErrorAlong coordinate function derivative x y)
          Add.+
          Abs.absℝ
            (derivative x Mul.·
              (coordinate y Group.- coordinate x)))
        (Real.ιℚ (fst (1₊ +₊ B)) Mul.· distance y)
        (abs-triangle
          (derivativeErrorAlong coordinate function derivative x y)
          (derivative x Mul.·
            (coordinate y Group.- coordinate x)))
        (subst
          ((Abs.absℝ
              (derivativeErrorAlong coordinate function derivative x y)
            Add.+
            Abs.absℝ
              (derivative x Mul.·
                (coordinate y Group.- coordinate x))) ≤ℝ_)
          (sym (coefficient-path y))
          (add-monotone
            (Abs.absℝ
              (derivativeErrorAlong coordinate function derivative x y))
            (Real.ιℚ 1 Mul.· distance y)
            (Abs.absℝ
              (derivative x Mul.·
                (coordinate y Group.- coordinate x)))
            (Real.ιℚ (fst B) Mul.· distance y)
            error-bound (linear-bound y))))


derivativeAlongIsContinuousAtBound :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → Real.ℝ)
    (x : A) B →
  Abs.absℝ (derivative x) ≤ℝ Real.ιℚ (fst B) →
  IsContinuousAt source coordinate (snd Real.ℝPremetricSpace) x →
  IsDerivativeAlong source coordinate function derivative →
  IsContinuousAt source function (snd Real.ℝPremetricSpace) x
derivativeAlongIsContinuousAtBound
  source coordinate function derivative x B
  derivative-bound coordinate-continuous has-derivative
  .IsContinuousAt.pres≈ ε = do
    (δlinear , linear-bound) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate function derivative
        has-derivative x B derivative-bound
    (δcoordinate , coordinate-close) ←
      coordinate-continuous .IsContinuousAt.pres≈
        (ε ₊／₊ (1₊ +₊ B))
    return
      ( min₊ δlinear δcoordinate
      , λ y x≈y →
          output-close y
            (linear-bound y
              (PremetricStr.isMonotone≈≤
                source x y
                (min₊ δlinear δcoordinate) δlinear
                (min₊≤L δlinear δcoordinate) x≈y))
            (coordinate-close y
              (PremetricStr.isMonotone≈≤
                source x y
                (min₊ δlinear δcoordinate) δcoordinate
                (min₊≤R δlinear δcoordinate) x≈y))
      )
  where
  C : ℚ₊
  C = 1₊ +₊ B

  output-close : ∀ y →
    Abs.absℝ (function y Group.- function x)
      ≤ℝ
    Real.ιℚ (fst C) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x) →
    coordinate x Real.Base.≈ᶜ[ ε ₊／₊ C ] coordinate y →
    function x Real.Base.≈ᶜ[ ε ] function y
  output-close y function-bound coordinate-near =
    absDifference<→closeness
      (function x) (function y) ε
      (subst
        (_<ℝ Real.ιℚ (fst ε))
        (distance-sym (function y) (function x))
        (≤<ℝ-trans
          (Abs.absℝ (function y Group.- function x))
          (Real.ιℚ (fst C) Mul.·
            Abs.absℝ (coordinate y Group.- coordinate x))
          (Real.ιℚ (fst ε))
          function-bound
          (subst
            ((Real.ιℚ (fst C) Mul.·
              Abs.absℝ (coordinate y Group.- coordinate x)) <ℝ_)
            (Mul.mul-ι-ι (fst C) (fst (ε ₊／₊ C))
            ∙ cong Real.ιℚ (·／ C ε))
            (mul-preserves≪-left-positive
              (Abs.absℝ (coordinate y Group.- coordinate x))
              (Real.ιℚ (fst (ε ₊／₊ C)))
              (Real.ιℚ (fst C))
              (subst
                (_<ℝ Real.ιℚ (fst (ε ₊／₊ C)))
                (distance-sym (coordinate x) (coordinate y))
                (closeness→absDifference<
                  (coordinate x) (coordinate y)
                  (ε ₊／₊ C) coordinate-near))
              (<ℚ→<ℝ 0 (fst C) (snd C))))))


-- A single rational bound for the derivative value is opened only inside
-- the proposition-valued continuity witness.  Unlike the older proof, no
-- intermediate natural-number bound is required.

derivativeAlongIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → Real.ℝ) →
  isContinuous source coordinate (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate function derivative →
  isContinuous source function (snd Real.ℝPremetricSpace)
derivativeAlongIsContinuous
  source coordinate function derivative
  coordinate-continuous has-derivative x
  .IsContinuousAt.pres≈ ε = do
    (B , derivative-bound) ← ∃rationalBound (derivative x)
    derivativeAlongIsContinuousAtBound
        source coordinate function derivative x B
        derivative-bound (coordinate-continuous x) has-derivative
      .IsContinuousAt.pres≈ ε


derivativeIsContinuous :
  ∀ function derivative →
  IsDerivative function derivative →
  isContinuous
    (snd Real.ℝPremetricSpace) function
    (snd Real.ℝPremetricSpace)
derivativeIsContinuous function derivative =
  derivativeAlongIsContinuous
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ) function derivative
    (snd (CategoryStructures.idᶜ {M = Real.ℝPremetricSpace}))
