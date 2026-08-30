module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (abs-triangle ; add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; mul-monotone-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (<ℚ→<ℝ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  differenceOfSums :
    ∀ (a b c d : Real.ℝ) →
    (a Add.+ b) Group.- (c Add.+ d)
      ≡
    (a Group.- c) Add.+ (b Group.- d)
  differenceOfSums a b c d =
      cong ((a Add.+ b) Add.+_) (neg-add c d)
    ∙ sym (add-assoc a b ((Neg.- c) Add.+ (Neg.- d)))
    ∙ cong (a Add.+_)
        (add-assoc b (Neg.- c) (Neg.- d))
    ∙ cong (λ value → a Add.+ (value Add.+ (Neg.- d)))
        (add-comm b (Neg.- c))
    ∙ cong (a Add.+_)
        (sym (add-assoc (Neg.- c) b (Neg.- d)))
    ∙ add-assoc a (Neg.- c) (b Add.+ (Neg.- d))


  addDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f g f' g' : A → Real.ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → f point Add.+ g point)
        (λ point → f' point Add.+ g' point)
        x y
      ≡
    derivativeErrorAlong coordinate f f' x y Add.+
      derivativeErrorAlong coordinate g g' x y
  addDerivativeErrorPath coordinate f g f' g' x y =
      cong₂ Group._-_
        (differenceOfSums (f y) (g y) (f x) (g x))
        (mul-distrib-over-add-left
          (f' x) (g' x)
          (coordinate y Group.- coordinate x))
    ∙ differenceOfSums
        (f y Group.- f x)
        (g y Group.- g x)
        (f' x Mul.· (coordinate y Group.- coordinate x))
        (g' x Mul.· (coordinate y Group.- coordinate x))


addHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → Real.ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point Add.+ g point)
    (λ point → f' point Add.+ g' point)
addHasDerivativeAlong
  {A = A} source coordinate f g f' g'
  f-derivative g-derivative x ε = do
    (δf , f-bound) ← f-derivative x (ε /2₊)
    (δg , g-bound) ← g-derivative x (ε /2₊)
    return
      ( min₊ δf δg
      , λ y x≈y →
          total-bound y
            (f-bound y
              (PremetricStr.isMonotone≈≤
                source x y (min₊ δf δg) δf
                (min₊≤L δf δg) x≈y))
            (g-bound y
              (PremetricStr.isMonotone≈≤
                source x y (min₊ δf δg) δg
                (min₊≤R δf δg) x≈y))
      )
  where
  distance : A → Real.ℝ
  distance y = Abs.absℝ (coordinate y Group.- coordinate x)

  half-coefficient : Real.ℝ
  half-coefficient = Real.ιℚ (fst (ε /2₊))

  upper-path : ∀ y →
    (half-coefficient Mul.· distance y) Add.+
        (half-coefficient Mul.· distance y)
      ≡
    Real.ιℚ (fst ε) Mul.· distance y
  upper-path y =
      sym
        (mul-distrib-over-add-left
          half-coefficient half-coefficient (distance y))
    ∙ cong (Mul._· distance y)
        (Add.add-ι-ι (fst (ε /2₊)) (fst (ε /2₊))
        ∙ cong Real.ιℚ (/2+/2≡id (fst ε)))

  total-bound : ∀ y →
    Abs.absℝ (derivativeErrorAlong coordinate f f' x y)
      ≤ℝ half-coefficient Mul.· distance y →
    Abs.absℝ (derivativeErrorAlong coordinate g g' x y)
      ≤ℝ half-coefficient Mul.· distance y →
    Abs.absℝ
      (derivativeErrorAlong
        coordinate
        (λ point → f point Add.+ g point)
        (λ point → f' point Add.+ g' point)
        x y)
      ≤ℝ
    Real.ιℚ (fst ε) Mul.· distance y
  total-bound y f-error-bound g-error-bound =
    subst
      (λ error →
        Abs.absℝ error ≤ℝ Real.ιℚ (fst ε) Mul.· distance y)
      (sym (addDerivativeErrorPath coordinate f g f' g' x y))
      (≤ℝ-trans
        (Abs.absℝ
          (derivativeErrorAlong coordinate f f' x y Add.+
            derivativeErrorAlong coordinate g g' x y))
        (Abs.absℝ (derivativeErrorAlong coordinate f f' x y) Add.+
          Abs.absℝ (derivativeErrorAlong coordinate g g' x y))
        (Real.ιℚ (fst ε) Mul.· distance y)
        (abs-triangle
          (derivativeErrorAlong coordinate f f' x y)
          (derivativeErrorAlong coordinate g g' x y))
        (subst
          ((Abs.absℝ (derivativeErrorAlong coordinate f f' x y) Add.+
            Abs.absℝ (derivativeErrorAlong coordinate g g' x y)) ≤ℝ_)
          (upper-path y)
          (add-monotone
            (Abs.absℝ (derivativeErrorAlong coordinate f f' x y))
            (half-coefficient Mul.· distance y)
            (Abs.absℝ (derivativeErrorAlong coordinate g g' x y))
            (half-coefficient Mul.· distance y)
            f-error-bound g-error-bound)))


addHasDerivative :
  ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x Add.+ g x)
    (λ x → f' x Add.+ g' x)
addHasDerivative f g f' g' =
  addHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (λ x → x) f g f' g'


private
  differenceOfNegatives : ∀ a b →
    (Neg.- a) Group.- (Neg.- b) ≡ Neg.- (a Group.- b)
  differenceOfNegatives a b =
      cong ((Neg.- a) Add.+_) (Neg.neg-involutive b)
    ∙ add-comm (Neg.- a) b
    ∙ sym (neg-sub a b)


  negDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f f' : A → Real.ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → Neg.- f point)
        (λ point → Neg.- f' point)
        x y
      ≡
    Neg.- derivativeErrorAlong coordinate f f' x y
  negDerivativeErrorPath coordinate f f' x y =
      cong₂ Group._-_
        (differenceOfNegatives (f y) (f x))
        (ℝRing.-DistL·
          (f' x) (coordinate y Group.- coordinate x))
    ∙ differenceOfNegatives
        (f y Group.- f x)
        (f' x Mul.· (coordinate y Group.- coordinate x))


  negCoordinateDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f f' : A → Real.ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate f (λ point → Neg.- f' point) x y
      ≡
    derivativeErrorAlong
      (λ point → Neg.- coordinate point) f f' x y
  negCoordinateDerivativeErrorPath coordinate f f' x y =
    cong
      (λ value → (f y Group.- f x) Group.- value)
      ( ℝRing.-DistL· (f' x) displacement
      ∙ sym (ℝRing.-DistR· (f' x) displacement)
      ∙ cong (f' x Mul.·_)
          (sym
            (differenceOfNegatives
              (coordinate y) (coordinate x))))
    where
    displacement : Real.ℝ
    displacement = coordinate y Group.- coordinate x


negHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → Real.ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → Neg.- f point)
    (λ point → Neg.- f' point)
negHasDerivativeAlong
  source coordinate f f' f-derivative x ε = do
    (δ , error-bound) ← f-derivative x ε
    return
      ( δ
      , λ y x≈y →
          subst
            (λ error →
              Abs.absℝ error ≤ℝ
                Real.ιℚ (fst ε) Mul.·
                  Abs.absℝ (coordinate y Group.- coordinate x))
            (sym (negDerivativeErrorPath coordinate f f' x y))
            (subst
              (_≤ℝ
                (Real.ιℚ (fst ε) Mul.·
                  Abs.absℝ (coordinate y Group.- coordinate x)))
              (sym
                (Abs.absℝ-neg
                  (derivativeErrorAlong coordinate f f' x y)))
              (error-bound y x≈y))
      )


negHasDerivative :
  ∀ f f' →
  IsDerivative f f' →
  IsDerivative
    (λ x → Neg.- f x)
    (λ x → Neg.- f' x)
negHasDerivative f f' =
  negHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (λ x → x) f f'


-- Reversing the coordinate, rather than the output, reverses the derivative
-- value.  This is useful when transporting results between positive and
-- negative subspaces.

negCoordinateHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → Real.ℝ) →
  IsDerivativeAlong
    source (λ point → Neg.- coordinate point) f f' →
  IsDerivativeAlong
    source coordinate f (λ point → Neg.- f' point)
negCoordinateHasDerivativeAlong
  source coordinate f f' has-derivative x ε = do
    (δ , error-bound) ← has-derivative x ε
    return
      ( δ
      , λ y x≈y →
          let
            distance-path :
              Abs.absℝ
                ((Neg.- coordinate y) Group.- (Neg.- coordinate x))
                ≡
              Abs.absℝ (coordinate y Group.- coordinate x)
            distance-path =
                cong Abs.absℝ
                  (differenceOfNegatives
                    (coordinate y) (coordinate x))
              ∙ Abs.absℝ-neg
                  (coordinate y Group.- coordinate x)

            bound-at-original-distance =
              subst
                (Abs.absℝ
                  (derivativeErrorAlong
                    (λ point → Neg.- coordinate point)
                    f f' x y) ≤ℝ_)
                (cong (Real.ιℚ (fst ε) Mul.·_) distance-path)
                (error-bound y x≈y)
          in
          subst
            (λ error →
              Abs.absℝ error ≤ℝ
                Real.ιℚ (fst ε) Mul.·
                  Abs.absℝ (coordinate y Group.- coordinate x))
            (sym
              (negCoordinateDerivativeErrorPath
                coordinate f f' x y))
            bound-at-original-distance
      )


subHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → Real.ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point Group.- g point)
    (λ point → f' point Group.- g' point)
subHasDerivativeAlong
  source coordinate f g f' g'
  f-derivative g-derivative =
  addHasDerivativeAlong
    source coordinate
    f (λ point → Neg.- g point)
    f' (λ point → Neg.- g' point)
    f-derivative
    (negHasDerivativeAlong
      source coordinate g g' g-derivative)


subHasDerivative :
  ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x Group.- g x)
    (λ x → f' x Group.- g' x)
subHasDerivative f g f' g' =
  subHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (λ x → x) f g f' g'


private
  scaleDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f f' : A → Real.ℝ)
      (c : Real.ℝ) (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → c Mul.· f point)
        (λ point → c Mul.· f' point)
        x y
      ≡
    c Mul.· derivativeErrorAlong coordinate f f' x y
  scaleDerivativeErrorPath coordinate f f' c x y =
      cong₂ Group._-_
        (sym (ℝRing.·DistR- c (f y) (f x)))
        (sym
          (mul-assoc
            c (f' x) (coordinate y Group.- coordinate x)))
    ∙ sym
        (ℝRing.·DistR-
          c
          (f y Group.- f x)
          (f' x Mul.· (coordinate y Group.- coordinate x)))


scaleHasDerivativeAlongAtBound :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → Real.ℝ)
    (c : Real.ℝ) (B : ℚ₊) →
  Abs.absℝ c ≤ℝ Real.ιℚ (fst B) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → c Mul.· f point)
    (λ point → c Mul.· f' point)
scaleHasDerivativeAlongAtBound
  {A = A} source coordinate f f' c B
  absc≤B f-derivative x ε = do
    (δ , error-bound) ← f-derivative x (ε ₊／₊ B)
    return
      ( δ
      , λ y x≈y → scaled-error-bound y (error-bound y x≈y)
      )
  where
  distance : A → Real.ℝ
  distance y = Abs.absℝ (coordinate y Group.- coordinate x)

  error : A → Real.ℝ
  error y = derivativeErrorAlong coordinate f f' x y

  upper-path : ∀ y →
    Real.ιℚ (fst B) Mul.·
        (Real.ιℚ (fst (ε ₊／₊ B)) Mul.· distance y)
      ≡
    Real.ιℚ (fst ε) Mul.· distance y
  upper-path y =
      mul-assoc
        (Real.ιℚ (fst B))
        (Real.ιℚ (fst (ε ₊／₊ B)))
        (distance y)
    ∙ cong (Mul._· distance y)
        (Mul.mul-ι-ι (fst B) (fst (ε ₊／₊ B))
        ∙ cong Real.ιℚ (·／ B ε))

  scaled-error-bound : ∀ y →
    Abs.absℝ (error y)
      ≤ℝ
    Real.ιℚ (fst (ε ₊／₊ B)) Mul.· distance y →
    Abs.absℝ
      (derivativeErrorAlong
        coordinate
        (λ point → c Mul.· f point)
        (λ point → c Mul.· f' point)
        x y)
      ≤ℝ
    Real.ιℚ (fst ε) Mul.· distance y
  scaled-error-bound y base-bound =
    subst
      (λ value →
        Abs.absℝ value ≤ℝ Real.ιℚ (fst ε) Mul.· distance y)
      (sym (scaleDerivativeErrorPath coordinate f f' c x y))
      (subst
        (_≤ℝ Real.ιℚ (fst ε) Mul.· distance y)
        (sym (abs-mul c (error y)))
        (subst
          ((Abs.absℝ c Mul.· Abs.absℝ (error y)) ≤ℝ_)
          (upper-path y)
          (mul-monotone-nonnegative
            (Abs.absℝ c) (Real.ιℚ (fst B))
            (Abs.absℝ (error y))
            (Real.ιℚ (fst (ε ₊／₊ B)) Mul.· distance y)
            absc≤B base-bound
            (zero≤abs c) (zero≤abs (error y)))))


-- Every completed-real scalar is allowed.  Its merely existing rational
-- absolute bound is eliminated independently at each requested derivative
-- radius, so the result is stronger than a rational-scalar-only API without
-- invoking any countable choice.

scaleHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → Real.ℝ)
    (c : Real.ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → c Mul.· f point)
    (λ point → c Mul.· f' point)
scaleHasDerivativeAlong
  source coordinate f f' c f-derivative x ε = do
    (B , absc≤B) ← ∃rationalBound c
    scaleHasDerivativeAlongAtBound
        source coordinate f f' c B absc≤B f-derivative x ε


scaleHasDerivative :
  ∀ f f' c →
  IsDerivative f f' →
  IsDerivative
    (λ x → c Mul.· f x)
    (λ x → c Mul.· f' x)
scaleHasDerivative f f' c =
  scaleHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (λ x → x) f f' c
