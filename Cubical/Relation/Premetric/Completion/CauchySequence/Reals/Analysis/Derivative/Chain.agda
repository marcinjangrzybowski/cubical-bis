module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation.Monad

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (abs-triangle ; add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using
    ( abs-mul
    ; mul-preserves≤-left-nonnegative
    ; mul-monotone-nonnegative
    )
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℚ→<ℝ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Continuity


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  telescopingDifference :
    ∀ a b c →
    (a Group.- b) Add.+ (b Group.- c) ≡ a Group.- c
  telescopingDifference a b c =
    add-assoc (a Group.- b) b (Neg.- c)
    ∙ cong (Add._+ (Neg.- c)) (sub-add-cancel a b)

  chainDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' : A → Real.ℝ)
      (outer outer' : Real.ℝ → Real.ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → outer (inner point))
        (λ point →
          outer' (inner point) Mul.· inner' point)
        x y
      ≡
    derivativeErrorAlong
        (idfun Real.ℝ) outer outer'
        (inner x) (inner y)
      Add.+
    (outer' (inner x) Mul.·
      derivativeErrorAlong coordinate inner inner' x y)
  chainDerivativeErrorPath
    coordinate inner inner' outer outer' x y =
      cong
        (λ value → outer-difference Group.- value)
        (sym
          (mul-assoc
            (outer' (inner x)) (inner' x) displacement))
    ∙ sym
        (telescopingDifference
          outer-difference
          (outer' (inner x) Mul.· inner-difference)
          (outer' (inner x) Mul.·
            (inner' x Mul.· displacement)))
    ∙ cong
        (outer-error Add.+_)
        (sym
          (ℝRing.·DistR-
            (outer' (inner x))
            inner-difference
            (inner' x Mul.· displacement)))
    where
    displacement : Real.ℝ
    displacement = coordinate y Group.- coordinate x

    inner-difference : Real.ℝ
    inner-difference = inner y Group.- inner x

    outer-difference : Real.ℝ
    outer-difference = outer (inner y) Group.- outer (inner x)

    outer-error : Real.ℝ
    outer-error =
      derivativeErrorAlong
        (idfun Real.ℝ) outer outer'
        (inner x) (inner y)

  positiveRationalNonnegative :
    ∀ B → Real.ιℚ 0 ≤ℝ Real.ιℚ (fst B)
  positiveRationalNonnegative B =
    <ℝ-weaken
      (Real.ιℚ 0) (Real.ιℚ (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  boundedErrorProduct :
    ∀ value error distance B ρ →
    Abs.absℝ value ≤ℝ Real.ιℚ (fst B) →
    Abs.absℝ error
      ≤ℝ Real.ιℚ (fst (ρ ₊／₊ B)) Mul.· distance →
    Abs.absℝ (value Mul.· error)
      ≤ℝ Real.ιℚ (fst ρ) Mul.· distance
  boundedErrorProduct
    value error distance B ρ
    absvalue≤B error-bound =
      subst
        (_≤ℝ Real.ιℚ (fst ρ) Mul.· distance)
        (sym (abs-mul value error))
        (subst
          ((Abs.absℝ value Mul.· Abs.absℝ error) ≤ℝ_)
          rational-product-path
          (mul-monotone-nonnegative
            (Abs.absℝ value) (Real.ιℚ (fst B))
            (Abs.absℝ error)
            (Real.ιℚ (fst (ρ ₊／₊ B)) Mul.· distance)
            absvalue≤B error-bound
            (zero≤abs value) (zero≤abs error)))
    where
    rational-product-path :
      Real.ιℚ (fst B) Mul.·
          (Real.ιℚ (fst (ρ ₊／₊ B)) Mul.· distance)
        ≡
      Real.ιℚ (fst ρ) Mul.· distance
    rational-product-path =
      mul-assoc
        (Real.ιℚ (fst B))
        (Real.ιℚ (fst (ρ ₊／₊ B))) distance
      ∙ cong (Mul._· distance)
          (Mul.mul-ι-ι (fst B) (fst (ρ ₊／₊ B))
          ∙ cong Real.ιℚ (·／ B ρ))

  boundedErrorThroughLinearInput :
    ∀ error input-distance coordinate-distance B ρ →
    Abs.absℝ error
      ≤ℝ
    Real.ιℚ (fst (ρ ₊／₊ B)) Mul.· input-distance →
    input-distance
      ≤ℝ Real.ιℚ (fst B) Mul.· coordinate-distance →
    Abs.absℝ error
      ≤ℝ Real.ιℚ (fst ρ) Mul.· coordinate-distance
  boundedErrorThroughLinearInput
    error input-distance coordinate-distance B ρ
    error-bound input-bound =
      ≤ℝ-trans
        (Abs.absℝ error)
        (Real.ιℚ (fst (ρ ₊／₊ B)) Mul.· input-distance)
        (Real.ιℚ (fst ρ) Mul.· coordinate-distance)
        error-bound
        (subst
          ((Real.ιℚ (fst (ρ ₊／₊ B)) Mul.· input-distance) ≤ℝ_)
          rational-product-path
          (mul-preserves≤-left-nonnegative
            input-distance
            (Real.ιℚ (fst B) Mul.· coordinate-distance)
            (Real.ιℚ (fst (ρ ₊／₊ B)))
            input-bound
            (positiveRationalNonnegative (ρ ₊／₊ B))))
    where
    rational-product-path :
      Real.ιℚ (fst (ρ ₊／₊ B)) Mul.·
          (Real.ιℚ (fst B) Mul.· coordinate-distance)
        ≡
      Real.ιℚ (fst ρ) Mul.· coordinate-distance
    rational-product-path =
      mul-assoc
        (Real.ιℚ (fst (ρ ₊／₊ B)))
        (Real.ιℚ (fst B)) coordinate-distance
      ∙ cong (Mul._· coordinate-distance)
          (mul-comm
              (Real.ιℚ (fst (ρ ₊／₊ B)))
              (Real.ιℚ (fst B))
          ∙ Mul.mul-ι-ι (fst B) (fst (ρ ₊／₊ B))
          ∙ cong Real.ιℚ (·／ B ρ))

  chainTotalErrorBound :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' : A → Real.ℝ)
      (outer outer' : Real.ℝ → Real.ℝ)
      (x y : A) C G ε →
    Abs.absℝ (outer' (inner x))
      ≤ℝ Real.ιℚ (fst G) →
    Abs.absℝ (inner y Group.- inner x)
      ≤ℝ
    Real.ιℚ (fst C) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x) →
    Abs.absℝ
        (derivativeErrorAlong
          (idfun Real.ℝ) outer outer'
          (inner x) (inner y))
      ≤ℝ
    Real.ιℚ (fst ((ε /2₊) ₊／₊ C)) Mul.·
      Abs.absℝ (inner y Group.- inner x) →
    Abs.absℝ
        (derivativeErrorAlong
          coordinate inner inner' x y)
      ≤ℝ
    Real.ιℚ (fst ((ε /2₊) ₊／₊ G)) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x) →
    Abs.absℝ
        (derivativeErrorAlong
          coordinate
          (λ point → outer (inner point))
          (λ point →
            outer' (inner point) Mul.· inner' point)
          x y)
      ≤ℝ
    Real.ιℚ (fst ε) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x)
  chainTotalErrorBound
    coordinate inner inner' outer outer'
    x y C G ε outer'-bound
    inner-linear-bound outer-error-bound inner-error-bound =
      subst
        (λ error →
          Abs.absℝ error
            ≤ℝ Real.ιℚ (fst ε) Mul.· coordinate-distance)
        (sym
          (chainDerivativeErrorPath
            coordinate inner inner' outer outer' x y))
        (≤ℝ-trans
          (Abs.absℝ
            (outer-error Add.+
              (outer' (inner x) Mul.· inner-error)))
          (Abs.absℝ outer-error Add.+
            Abs.absℝ (outer' (inner x) Mul.· inner-error))
          (Real.ιℚ (fst ε) Mul.· coordinate-distance)
          (abs-triangle
            outer-error
            (outer' (inner x) Mul.· inner-error))
          (subst
            ((Abs.absℝ outer-error Add.+
              Abs.absℝ
                (outer' (inner x) Mul.· inner-error)) ≤ℝ_)
            half-sum-path
            (add-monotone
              (Abs.absℝ outer-error)
              (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance)
              (Abs.absℝ
                (outer' (inner x) Mul.· inner-error))
              (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance)
              (boundedErrorThroughLinearInput
                outer-error
                (Abs.absℝ (inner y Group.- inner x))
                coordinate-distance C (ε /2₊)
                outer-error-bound inner-linear-bound)
              (boundedErrorProduct
                (outer' (inner x)) inner-error
                coordinate-distance G (ε /2₊)
                outer'-bound inner-error-bound))))
    where
    coordinate-distance : Real.ℝ
    coordinate-distance =
      Abs.absℝ (coordinate y Group.- coordinate x)

    outer-error : Real.ℝ
    outer-error =
      derivativeErrorAlong
        (idfun Real.ℝ) outer outer'
        (inner x) (inner y)

    inner-error : Real.ℝ
    inner-error =
      derivativeErrorAlong coordinate inner inner' x y

    half-sum-path :
      (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance) Add.+
          (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance)
        ≡
      Real.ιℚ (fst ε) Mul.· coordinate-distance
    half-sum-path =
      sym
        (mul-distrib-over-add-left
          (Real.ιℚ (fst (ε /2₊)))
          (Real.ιℚ (fst (ε /2₊)))
          coordinate-distance)
      ∙ cong (Mul._· coordinate-distance)
          (Add.add-ι-ι
            (fst (ε /2₊)) (fst (ε /2₊))
          ∙ cong Real.ιℚ (/2+/2≡id (fst ε)))


-- The chain rule needs only local rational bounds.  Those witnesses are
-- opened inside the proposition-valued derivative proof, so no countable or
-- global choice is introduced.

chainHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' : A → Real.ℝ)
    (outer outer' : Real.ℝ → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate inner inner' →
  IsDerivative outer outer' →
  IsDerivativeAlong
    source coordinate
    (λ point → outer (inner point))
    (λ point →
      outer' (inner point) Mul.· inner' point)
chainHasDerivativeAlong
  source coordinate inner inner' outer outer'
  coordinate-continuous inner-derivative outer-derivative
  x ε = do
    (B , inner'-bound) ← ∃rationalBound (inner' x)
    (G , outer'-bound) ← ∃rationalBound (outer' (inner x))
    let
      C : ℚ₊
      C = 1₊ +₊ B
    (δlinear , inner-linear-near) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate inner inner'
        inner-derivative x B inner'-bound
    (δinner , inner-error-near) ←
      inner-derivative x ((ε /2₊) ₊／₊ G)
    (δouter , outer-error-near) ←
      outer-derivative
        (inner x) ((ε /2₊) ₊／₊ C)
    (δcomposition , inner-close-near) ←
      derivativeAlongIsContinuousAtBound
          source coordinate inner inner' x B
          inner'-bound
          (coordinate-continuous x)
          inner-derivative
        .IsContinuousAt.pres≈ δouter
    let
      δ : ℚ₊
      δ = min₊ δlinear (min₊ δinner δcomposition)
    return
      ( δ
      , λ y x≈δy →
          chainTotalErrorBound
            coordinate inner inner' outer outer'
            x y C G ε outer'-bound
            (inner-linear-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δlinear
                (min₊≤L δlinear
                  (min₊ δinner δcomposition))
                x≈δy))
            (outer-error-near (inner y)
              (inner-close-near y
                (PremetricStr.isMonotone≈≤
                  source x y δ δcomposition
                  (ℚ.isTrans≤
                    (fst δ)
                    (fst (min₊ δinner δcomposition))
                    (fst δcomposition)
                    (min₊≤R δlinear
                      (min₊ δinner δcomposition))
                    (min₊≤R δinner δcomposition))
                  x≈δy)))
            (inner-error-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δinner
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δinner δcomposition))
                  (fst δinner)
                  (min₊≤R δlinear
                    (min₊ δinner δcomposition))
                  (min₊≤L δinner δcomposition))
                x≈δy))
      )


chainHasDerivative :
  ∀ inner inner' outer outer' →
  IsDerivative inner inner' →
  IsDerivative outer outer' →
  IsDerivative
    (λ x → outer (inner x))
    (λ x → outer' (inner x) Mul.· inner' x)
chainHasDerivative inner inner' outer outer' =
  chainHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)
    inner inner' outer outer'
    (snd
      (CategoryStructures.idᶜ
        {M = Real.ℝPremetricSpace}))


-- An indexed chain rule is useful when the outer function is defined only
-- on the same parameter space (for example, a reciprocal on a nonvanishing
-- subspace).  Its derivative is measured along `inner`, so no ambient
-- extension of the outer function and no intermediate-space choice are
-- required.

private
  indexedChainDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' outer outer' : A → Real.ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate outer
        (λ point → outer' point Mul.· inner' point)
        x y
      ≡
    derivativeErrorAlong inner outer outer' x y
      Add.+
    (outer' x Mul.·
      derivativeErrorAlong coordinate inner inner' x y)
  indexedChainDerivativeErrorPath
    coordinate inner inner' outer outer' x y =
      cong
        (λ value → outer-difference Group.- value)
        (sym (mul-assoc (outer' x) (inner' x) displacement))
    ∙ sym
        (telescopingDifference
          outer-difference
          (outer' x Mul.· inner-difference)
          (outer' x Mul.· (inner' x Mul.· displacement)))
    ∙ cong
        (outer-error Add.+_)
        (sym
          (ℝRing.·DistR-
            (outer' x) inner-difference
            (inner' x Mul.· displacement)))
    where
    displacement : Real.ℝ
    displacement = coordinate y Group.- coordinate x

    inner-difference : Real.ℝ
    inner-difference = inner y Group.- inner x

    outer-difference : Real.ℝ
    outer-difference = outer y Group.- outer x

    outer-error : Real.ℝ
    outer-error = derivativeErrorAlong inner outer outer' x y


  indexedChainTotalErrorBound :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate inner inner' outer outer' : A → Real.ℝ)
      (x y : A) C G ε →
    Abs.absℝ (outer' x) ≤ℝ Real.ιℚ (fst G) →
    Abs.absℝ (inner y Group.- inner x)
      ≤ℝ
    Real.ιℚ (fst C) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x) →
    Abs.absℝ
        (derivativeErrorAlong inner outer outer' x y)
      ≤ℝ
    Real.ιℚ (fst ((ε /2₊) ₊／₊ C)) Mul.·
      Abs.absℝ (inner y Group.- inner x) →
    Abs.absℝ
        (derivativeErrorAlong coordinate inner inner' x y)
      ≤ℝ
    Real.ιℚ (fst ((ε /2₊) ₊／₊ G)) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x) →
    Abs.absℝ
        (derivativeErrorAlong
          coordinate outer
          (λ point → outer' point Mul.· inner' point)
          x y)
      ≤ℝ
    Real.ιℚ (fst ε) Mul.·
      Abs.absℝ (coordinate y Group.- coordinate x)
  indexedChainTotalErrorBound
    coordinate inner inner' outer outer'
    x y C G ε outer'-bound
    inner-linear-bound outer-error-bound inner-error-bound =
      subst
        (λ error →
          Abs.absℝ error
            ≤ℝ Real.ιℚ (fst ε) Mul.· coordinate-distance)
        (sym
          (indexedChainDerivativeErrorPath
            coordinate inner inner' outer outer' x y))
        (≤ℝ-trans
          (Abs.absℝ
            (outer-error Add.+ (outer' x Mul.· inner-error)))
          (Abs.absℝ outer-error Add.+
            Abs.absℝ (outer' x Mul.· inner-error))
          (Real.ιℚ (fst ε) Mul.· coordinate-distance)
          (abs-triangle outer-error (outer' x Mul.· inner-error))
          (subst
            ((Abs.absℝ outer-error Add.+
              Abs.absℝ (outer' x Mul.· inner-error)) ≤ℝ_)
            half-sum-path
            (add-monotone
              (Abs.absℝ outer-error)
              (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance)
              (Abs.absℝ (outer' x Mul.· inner-error))
              (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance)
              (boundedErrorThroughLinearInput
                outer-error
                (Abs.absℝ (inner y Group.- inner x))
                coordinate-distance C (ε /2₊)
                outer-error-bound inner-linear-bound)
              (boundedErrorProduct
                (outer' x) inner-error coordinate-distance G (ε /2₊)
                outer'-bound inner-error-bound))))
    where
    coordinate-distance : Real.ℝ
    coordinate-distance =
      Abs.absℝ (coordinate y Group.- coordinate x)

    outer-error : Real.ℝ
    outer-error = derivativeErrorAlong inner outer outer' x y

    inner-error : Real.ℝ
    inner-error = derivativeErrorAlong coordinate inner inner' x y

    half-sum-path :
      (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance) Add.+
          (Real.ιℚ (fst (ε /2₊)) Mul.· coordinate-distance)
        ≡
      Real.ιℚ (fst ε) Mul.· coordinate-distance
    half-sum-path =
      sym
        (mul-distrib-over-add-left
          (Real.ιℚ (fst (ε /2₊)))
          (Real.ιℚ (fst (ε /2₊)))
          coordinate-distance)
      ∙ cong (Mul._· coordinate-distance)
          (Add.add-ι-ι
            (fst (ε /2₊)) (fst (ε /2₊))
          ∙ cong Real.ιℚ (/2+/2≡id (fst ε)))


chainHasDerivativeAlongIndexed :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' outer outer' : A → Real.ℝ) →
  IsDerivativeAlong source coordinate inner inner' →
  IsDerivativeAlong source inner outer outer' →
  IsDerivativeAlong
    source coordinate outer
    (λ point → outer' point Mul.· inner' point)
chainHasDerivativeAlongIndexed
  source coordinate inner inner' outer outer'
  inner-derivative outer-derivative x ε = do
    (B , inner'-bound) ← ∃rationalBound (inner' x)
    (G , outer'-bound) ← ∃rationalBound (outer' x)
    let C = 1₊ +₊ B
    (δlinear , inner-linear-near) ←
      derivativeAlongLocalLinearBoundAt
        source coordinate inner inner'
        inner-derivative x B inner'-bound
    (δinner , inner-error-near) ←
      inner-derivative x ((ε /2₊) ₊／₊ G)
    (δouter , outer-error-near) ←
      outer-derivative x ((ε /2₊) ₊／₊ C)
    let δ = min₊ δlinear (min₊ δinner δouter)
    return
      ( δ
      , λ y x≈y →
          indexedChainTotalErrorBound
            coordinate inner inner' outer outer'
            x y C G ε outer'-bound
            (inner-linear-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δlinear
                (min₊≤L δlinear (min₊ δinner δouter))
                x≈y))
            (outer-error-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δouter
                (ℚ.isTrans≤ _ _ _
                  (min₊≤R δlinear (min₊ δinner δouter))
                  (min₊≤R δinner δouter))
                x≈y))
            (inner-error-near y
              (PremetricStr.isMonotone≈≤
                source x y δ δinner
                (ℚ.isTrans≤ _ _ _
                  (min₊≤R δlinear (min₊ δinner δouter))
                  (min₊≤L δinner δouter))
                x≈y))
      )
