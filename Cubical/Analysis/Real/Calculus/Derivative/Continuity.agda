module Cubical.Analysis.Real.Calculus.Derivative.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-weaken; ≤<ℝ-trans)
open import Cubical.Analysis.Real.Order.Strict.Rational
  using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Multiplication
  using (mulPres<PosL)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
  using (closeness→absDifference<; absDifference<→closeness)
open import Cubical.Analysis.Real.Metric.Distance
  using (distanceSym)
open import Cubical.Analysis.Real.Calculus.Derivative.Base


private
  derivativeErrorReconstructsDifference :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate function derivative : A → ℝ)
      (x y : A) →
    derivativeErrorAlong coordinate function derivative x y +
        derivative x · (coordinate y - coordinate x)
      ≡
    function y - function x
  derivativeErrorReconstructsDifference
      coordinate function derivative x y =
    subAddCancel
      (function y - function x)
      (derivative x · (coordinate y - coordinate x))


-- At a selected rational bound for the derivative value, differentiability
-- supplies a local linear estimate with coefficient `1 + B`.
derivativeAlongLocalLinearBoundAt :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  IsDerivativeAlong source coordinate function derivative →
  ∀ x B →
  absℝ (derivative x) ≤ℝ rat (fst B) →
  ∃[ δ ∈ ℚ₊ ]
    (∀ y →
      PremetricStr._≈[_]_ source x δ y →
      absℝ (function y - function x)
        ≤ℝ
      rat (fst (1₊ +₊ B)) ·
        absℝ (coordinate y - coordinate x))
derivativeAlongLocalLinearBoundAt
  {A = A} source coordinate function derivative
  has-derivative x B derivative-bound = do
    (δ , error-bound) ← has-derivative x 1₊
    return
      ( δ
      , λ y x≈y → difference-bound y (error-bound y x≈y)
      )
  where
  distance : A → ℝ
  distance y = absℝ (coordinate y - coordinate x)

  coefficient-path : ∀ y →
    rat (fst (1₊ +₊ B)) · distance y
      ≡
    (rat 1 · distance y) +
      (rat (fst B) · distance y)
  coefficient-path y =
      cong (_· distance y)
        (sym (rat+rat 1 (fst B)))
    ∙ mulDistL (rat 1) (rat (fst B)) (distance y)

  linear-bound : ∀ y →
    absℝ
      (derivative x · (coordinate y - coordinate x))
      ≤ℝ
    rat (fst B) · distance y
  linear-bound y =
    subst
      (_≤ℝ rat (fst B) · distance y)
      (sym
        (absMul
          (derivative x) (coordinate y - coordinate x)))
      (mulPres≤R-0≤
        (absℝ (derivative x))
        (rat (fst B))
        (distance y)
        (absNonnegative (coordinate y - coordinate x))
        derivative-bound)

  difference-bound : ∀ y →
    absℝ
      (derivativeErrorAlong coordinate function derivative x y)
      ≤ℝ rat 1 · distance y →
    absℝ (function y - function x)
      ≤ℝ
    rat (fst (1₊ +₊ B)) · distance y
  difference-bound y error-bound =
    subst
      (λ value →
        absℝ value ≤ℝ
          rat (fst (1₊ +₊ B)) · distance y)
      (derivativeErrorReconstructsDifference
        coordinate function derivative x y)
      (≤ℝ-trans
        (absℝ
          (derivativeErrorAlong coordinate function derivative x y +
            (derivative x ·
              (coordinate y - coordinate x))))
        (absℝ
            (derivativeErrorAlong coordinate function derivative x y)
          +
          absℝ
            (derivative x ·
              (coordinate y - coordinate x)))
        (rat (fst (1₊ +₊ B)) · distance y)
        (absTriangle
          (derivativeErrorAlong coordinate function derivative x y)
          (derivative x ·
            (coordinate y - coordinate x)))
        (subst
          ((absℝ
              (derivativeErrorAlong coordinate function derivative x y)
            +
            absℝ
              (derivative x ·
                (coordinate y - coordinate x))) ≤ℝ_)
          (sym (coefficient-path y))
          (addPres≤
            (absℝ
              (derivativeErrorAlong coordinate function derivative x y))
            (rat 1 · distance y)
            (absℝ
              (derivative x ·
                (coordinate y - coordinate x)))
            (rat (fst B) · distance y)
            error-bound (linear-bound y))))


derivativeAlongIsContinuousAtBound :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ)
    (x : A) B →
  absℝ (derivative x) ≤ℝ rat (fst B) →
  IsContinuousAt source coordinate (ℝPremetricSpace .snd) x →
  IsDerivativeAlong source coordinate function derivative →
  IsContinuousAt source function (ℝPremetricSpace .snd) x
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
    absℝ (function y - function x)
      ≤ℝ
    rat (fst C) · absℝ (coordinate y - coordinate x) →
    coordinate x ∼[ ε ₊／₊ C ] coordinate y →
    function x ∼[ ε ] function y
  output-close y function-bound coordinate-near =
    absDifference<→closeness
      (function x) (function y) ε
      (subst
        (_<ℝ rat (fst ε))
        (distanceSym (function y) (function x))
        (≤<ℝ-trans
          (absℝ (function y - function x))
          (rat (fst C) ·
            absℝ (coordinate y - coordinate x))
          (rat (fst ε))
          function-bound
          (subst
            ((rat (fst C) ·
              absℝ (coordinate y - coordinate x)) <ℝ_)
            (mul-rat (fst C) (fst (ε ₊／₊ C))
            ∙ cong rat (·／ C ε))
            (mulPres<PosL
              (absℝ (coordinate y - coordinate x))
              (rat (fst (ε ₊／₊ C)))
              (rat (fst C))
              (<ℚ→<ℝ 0 (fst C) (snd C))
              (subst
                (_<ℝ rat (fst (ε ₊／₊ C)))
                (distanceSym (coordinate x) (coordinate y))
                (closeness→absDifference<
                  (coordinate x) (coordinate y)
                  (ε ₊／₊ C) coordinate-near))))))


-- The selected natural bound is eliminated only into the proposition-valued
-- local continuity witness.
derivativeAlongIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate function derivative →
  isContinuous source function (ℝPremetricSpace .snd)
derivativeAlongIsContinuous
  source coordinate function derivative
  coordinate-continuous has-derivative x
  .IsContinuousAt.pres≈ ε = do
    (n , derivative-strict-bound) ← ∃naturalAbsBound (derivative x)
    derivativeAlongIsContinuousAtBound
        source coordinate function derivative x (naturalBound n)
        (<ℝ-weaken
          (absℝ (derivative x))
          (rat (naturalRational n))
          derivative-strict-bound)
        (coordinate-continuous x) has-derivative
      .IsContinuousAt.pres≈ ε


derivativeIsContinuous :
  ∀ function derivative →
  IsDerivative function derivative →
  isContinuous
    (ℝPremetricSpace .snd) function
    (ℝPremetricSpace .snd)
derivativeIsContinuous function derivative =
  derivativeAlongIsContinuous
    (ℝPremetricSpace .snd)
    (idfun ℝ) function derivative
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))
