module Cubical.HITs.CauchyRealsP.Analysis.Derivative.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative.Continuity

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

  differenceOfSums :
    ∀ (a b c d : ℝ) →
    (a + b) - (c + d)
      ≡
    (a - c) + (b - d)
  differenceOfSums a b c d =
    cong ((a + b) +_)
      (negAdd c d)
    ∙ sym (addAssoc a b ((- c) + (- d)))
    ∙ cong (a +_)
        (addAssoc b (- c) (- d))
    ∙ cong (λ value → a + (value + (- d)))
        (addComm b (- c))
    ∙ cong (a +_)
        (sym (addAssoc (- c) b (- d)))
    ∙ addAssoc a (- c) (b + (- d))

  addDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f g f' g' : A → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → f point + g point)
        (λ point → f' point + g' point)
        x y
      ≡
    derivativeErrorAlong coordinate f f' x y
      + derivativeErrorAlong coordinate g g' x y
  addDerivativeErrorPath
    coordinate f g f' g' x y =
      cong₂ _-_
        (differenceOfSums
          (f y) (g y) (f x) (g x))
        (mulDistL
          (f' x) (g' x)
          (coordinate y - coordinate x))
      ∙ differenceOfSums
          (f y - f x)
          (g y - g x)
          (f' x · (coordinate y - coordinate x))
          (g' x · (coordinate y - coordinate x))

addHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point + g point)
    (λ point → f' point + g' point)
addHasDerivativeAlong
  {A = A} source coordinate f g f' g'
  f-derivative g-derivative x ε = do
    (δf , f-bound) ←
      f-derivative x (ε /2₊)
    (δg , g-bound) ←
      g-derivative x (ε /2₊)
    return
      ( min₊ δf δg
      , λ y x∼y →
          total-bound y
            (f-bound y
              (PremetricStr.isMonotone≈≤
                source x y
                (min₊ δf δg) δf
                (min₊≤L δf δg) x∼y))
            (g-bound y
              (PremetricStr.isMonotone≈≤
                source x y
                (min₊ δf δg) δg
                (min₊≤R δf δg) x∼y))
      )
  where
  distance : A → ℝ
  distance y =
    absℝ (coordinate y - coordinate x)

  half-coefficient : ℝ
  half-coefficient =
    rat (fst (ε /2₊))

  upper-path :
    ∀ y →
    half-coefficient · distance y
        + half-coefficient · distance y
      ≡
    rat (fst ε) · distance y
  upper-path y =
    sym
      (mulDistL
        half-coefficient
        half-coefficient
        (distance y))
    ∙ cong
        (_· distance y)
        (rat+rat
          (fst (ε /2₊))
          (fst (ε /2₊))
        ∙ cong rat
            (1/2∈ℚ./2+/2≡id
              (fst ε)))

  total-bound :
    ∀ y →
    absℝ
        (derivativeErrorAlong
          coordinate f f' x y)
      ≤ℝ
    half-coefficient · distance y →
    absℝ
        (derivativeErrorAlong
          coordinate g g' x y)
      ≤ℝ
    half-coefficient · distance y →
    absℝ
        (derivativeErrorAlong
          coordinate
          (λ point → f point + g point)
          (λ point → f' point + g' point)
          x y)
      ≤ℝ
    rat (fst ε) · distance y
  total-bound y f-bound g-bound =
    subst
      (λ error →
        absℝ error
          ≤ℝ rat (fst ε) · distance y)
      (sym
        (addDerivativeErrorPath
          coordinate f g f' g' x y))
      (≤ℝ-trans
        (absℝ
          (derivativeErrorAlong coordinate f f' x y
            + derivativeErrorAlong coordinate g g' x y))
        (absℝ (derivativeErrorAlong coordinate f f' x y)
          + absℝ (derivativeErrorAlong coordinate g g' x y))
        (rat (fst ε) · distance y)
        (absTriangle
          (derivativeErrorAlong coordinate f f' x y)
          (derivativeErrorAlong coordinate g g' x y))
        (subst
          ((absℝ (derivativeErrorAlong coordinate f f' x y)
            + absℝ (derivativeErrorAlong coordinate g g' x y)) ≤ℝ_)
          (upper-path y)
          (≤ℝ-add
            (absℝ (derivativeErrorAlong coordinate f f' x y))
            (half-coefficient · distance y)
            (absℝ (derivativeErrorAlong coordinate g g' x y))
            (half-coefficient · distance y)
            f-bound g-bound)))

addHasDerivative :
  ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x + g x)
    (λ x → f' x + g' x)
addHasDerivative f g f' g' =
  addHasDerivativeAlong
    (snd ℝPremetricSpace)
    (λ x → x)
    f g f' g'

private
  differenceOfNegatives :
    ∀ a b →
    (- a) - (- b) ≡ - (a - b)
  differenceOfNegatives a b =
    cong ((- a) +_) (negInvol b)
    ∙ addComm (- a) b
    ∙ sym (negSub a b)

  negDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f f' : A → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → - f point)
        (λ point → - f' point)
        x y
      ≡
    - derivativeErrorAlong
        coordinate f f' x y
  negDerivativeErrorPath
    coordinate f f' x y =
      cong₂ _-_
        (differenceOfNegatives
          (f y) (f x))
        (ℝRing.-DistL·
          (f' x)
          (coordinate y - coordinate x))
    ∙ differenceOfNegatives
        (f y - f x)
        (f' x · (coordinate y - coordinate x))

  negCoordinateDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f f' : A → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate f (λ point → - f' point) x y
      ≡
    derivativeErrorAlong
        (λ point → - coordinate point) f f' x y
  negCoordinateDerivativeErrorPath
    coordinate f f' x y =
      cong
        (λ value → (f y - f x) - value)
        (ℝRing.-DistL·
            (f' x) displacement
        ∙ sym
            (ℝRing.-DistR·
              (f' x) displacement)
        ∙ cong
            (f' x ·_)
            (sym
              (differenceOfNegatives
                (coordinate y) (coordinate x))))
    where
    displacement : ℝ
    displacement =
      coordinate y - coordinate x

negHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → - f point)
    (λ point → - f' point)
negHasDerivativeAlong
  source coordinate f f' f-derivative x ε = do
    (δ , error-bound) ←
      f-derivative x ε
    return
      ( δ
      , λ y x∼y →
          subst
            (λ error →
              absℝ error
                ≤ℝ rat (fst ε)
                  · absℝ (coordinate y - coordinate x))
            (sym
              (negDerivativeErrorPath
                coordinate f f' x y))
            (subst
              (_≤ℝ
                rat (fst ε)
                  · absℝ (coordinate y - coordinate x))
              (sym
                (absNeg
                  (derivativeErrorAlong
                    coordinate f f' x y)))
              (error-bound y x∼y))
      )

negHasDerivative :
  ∀ f f' →
  IsDerivative f f' →
  IsDerivative
    (λ x → - f x)
    (λ x → - f' x)
negHasDerivative f f' =
  negHasDerivativeAlong
    (snd ℝPremetricSpace)
    (λ x → x)
    f f'

-- Reversing the real coordinate reverses the derivative value.  This is a
-- coordinate transport theorem, distinct from negating the output function
-- above; both transformations are needed for reciprocal on negative reals.
negCoordinateHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → ℝ) →
  IsDerivativeAlong
    source (λ point → - coordinate point) f f' →
  IsDerivativeAlong
    source coordinate f (λ point → - f' point)
negCoordinateHasDerivativeAlong
  source coordinate f f'
  has-derivative x ε = do
    (δ , error-bound) ←
      has-derivative x ε
    return
      ( δ
      , λ y x∼y →
          let
            distance-path :
              absℝ
                  ((- coordinate y)
                    - (- coordinate x))
                ≡
              absℝ (coordinate y - coordinate x)
            distance-path =
              cong absℝ
                (differenceOfNegatives
                  (coordinate y) (coordinate x))
              ∙ absNeg
                  (coordinate y - coordinate x)

            old-error-bound =
              error-bound y x∼y

            bound-at-original-distance =
              subst
                (absℝ
                  (derivativeErrorAlong
                    (λ point → - coordinate point)
                    f f' x y) ≤ℝ_)
                (cong
                  (rat (fst ε) ·_)
                  distance-path)
                old-error-bound
          in
          subst
            (λ error →
              absℝ error
                ≤ℝ
              rat (fst ε)
                · absℝ
                    (coordinate y - coordinate x))
            (sym
              (negCoordinateDerivativeErrorPath
                coordinate f f' x y))
            bound-at-original-distance
      )

subHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point - g point)
    (λ point → f' point - g' point)
subHasDerivativeAlong
  source coordinate f g f' g'
  f-derivative g-derivative =
    addHasDerivativeAlong
      source coordinate
      f (λ point → - g point)
      f' (λ point → - g' point)
      f-derivative
      (negHasDerivativeAlong
        source coordinate g g' g-derivative)

subHasDerivative :
  ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x - g x)
    (λ x → f' x - g' x)
subHasDerivative f g f' g' =
  subHasDerivativeAlong
    (snd ℝPremetricSpace)
    (λ x → x)
    f g f' g'

private
  scaleDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f f' : A → ℝ)
      (c : ℝ) (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → c · f point)
        (λ point → c · f' point)
        x y
      ≡
    c · derivativeErrorAlong
        coordinate f f' x y
  scaleDerivativeErrorPath
    coordinate f f' c x y =
      cong₂ _-_
        (sym
          (ℝRing.·DistR-
            c (f y) (f x)))
        (mulAssoc
          c (f' x)
          (coordinate y - coordinate x))
    ∙ sym
        (ℝRing.·DistR-
          c
          (f y - f x)
          (f' x · (coordinate y - coordinate x)))

scaleHasDerivativeAlongAtBound :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → ℝ)
    (c : ℝ) (B : ℚ₊) →
  absℝ c ≤ℝ rat (fst B) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → c · f point)
    (λ point → c · f' point)
scaleHasDerivativeAlongAtBound
  {A = A} source coordinate f f' c B
  absc≤B f-derivative x ε = do
    (δ , error-bound) ←
      f-derivative x (ε ₊／₊ B)
    return
      ( δ
      , λ y x∼y →
          scaled-error-bound y
            (error-bound y x∼y)
      )
  where
  distance : A → ℝ
  distance y =
    absℝ (coordinate y - coordinate x)

  error : A → ℝ
  error y =
    derivativeErrorAlong coordinate f f' x y

  positive-bound :
    0 ≤ℝ rat (fst B)
  positive-bound =
    <ℝ-weaken
      0 (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  upper-path :
    ∀ y →
    rat (fst B)
        · (rat (fst (ε ₊／₊ B)) · distance y)
      ≡
    rat (fst ε) · distance y
  upper-path y =
    sym
      (mulAssoc
        (rat (fst B))
        (rat (fst (ε ₊／₊ B)))
        (distance y))
    ∙ cong
        (_· distance y)
        (mul-rat
          (fst B) (fst (ε ₊／₊ B))
        ∙ cong rat
            (·／ B ε))

  scaled-error-bound :
    ∀ y →
    absℝ (error y)
      ≤ℝ
    rat (fst (ε ₊／₊ B)) · distance y →
    absℝ
        (derivativeErrorAlong
          coordinate
          (λ point → c · f point)
          (λ point → c · f' point)
          x y)
      ≤ℝ
    rat (fst ε) · distance y
  scaled-error-bound y base-bound =
    subst
      (λ value →
        absℝ value
          ≤ℝ rat (fst ε) · distance y)
      (sym
        (scaleDerivativeErrorPath
          coordinate f f' c x y))
      (subst
        (_≤ℝ rat (fst ε) · distance y)
        (sym (absMul c (error y)))
        (subst
          ((absℝ c · absℝ (error y)) ≤ℝ_)
          (upper-path y)
          (mulMono≤
            (absℝ c) (rat (fst B))
            (absℝ (error y))
            (rat (fst (ε ₊／₊ B)) · distance y)
            positive-bound
            (absNonnegative (error y))
            absc≤B base-bound)))

scaleHasDerivativeAtBound :
  ∀ f f' c B →
  absℝ c ≤ℝ rat (fst B) →
  IsDerivative f f' →
  IsDerivative
    (λ x → c · f x)
    (λ x → c · f' x)
scaleHasDerivativeAtBound f f' c B =
  scaleHasDerivativeAlongAtBound
    (snd ℝPremetricSpace)
    (λ x → x)
    f f' c B

rationalScaleBound : ℚ → ℚ₊
rationalScaleBound q =
  ℚ.maxWithPos [ 1 / 1 ]₊ (abs q)

rationalScaleBoundContains :
  ∀ q →
  absℝ (rat q)
    ≤ℝ rat (fst (rationalScaleBound q))
rationalScaleBoundContains q =
  subst
    (_≤ℝ rat (fst (rationalScaleBound q)))
    (sym (abs-rat q))
    (≤ℚ→≤ℝ
      (abs q)
      (fst (rationalScaleBound q))
      (ℚ.≤max' 1 (abs q)))

rationalScaleHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → ℝ)
    (q : ℚ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → rat q · f point)
    (λ point → rat q · f' point)
rationalScaleHasDerivativeAlong
  source coordinate f f' q =
    scaleHasDerivativeAlongAtBound
      source coordinate f f'
      (rat q) (rationalScaleBound q)
      (rationalScaleBoundContains q)

rationalScaleHasDerivative :
  ∀ f f' q →
  IsDerivative f f' →
  IsDerivative
    (λ x → rat q · f x)
    (λ x → rat q · f' x)
rationalScaleHasDerivative f f' q =
  rationalScaleHasDerivativeAlong
    (snd ℝPremetricSpace)
    (λ x → x)
    f f' q

private
  swapNestedProduct :
    ∀ a b c →
    (a · b) · c ≡ (a · c) · b
  swapNestedProduct a b c =
    mulAssoc a b c
    ∙ cong (a ·_) (mulComm b c)
    ∙ sym (mulAssoc a c b)

  productDifferencePath :
    ∀ a b c d →
    a · c - b · d
      ≡
    c · (a - b) + b · (c - d)
  productDifferencePath a b c d =
    cong ((a · c) +_)
      (sym (addIdL (- (b · d))))
    ∙ cong
        (λ value →
          a · c + (value + (- (b · d))))
        (sym (addInvL (b · c)))
    ∙ addAssoc
        (a · c) ((- (b · c)) + b · c) (- (b · d))
    ∙ cong (_+ (- (b · d)))
        (addAssoc (a · c) (- (b · c)) (b · c))
    ∙ sym
        (addAssoc
          ((a · c) + (- (b · c)))
          (b · c) (- (b · d)))
    ∙ cong₂ _+_
        (sym (ℝRing.·DistL- a b c))
        (sym (ℝRing.·DistR- b c d))
    ∙ cong
        (_+ b · (c - d))
        (mulComm (a - b) c)

  productDerivativeErrorPath :
    ∀ {ℓ} {A : Type ℓ}
      (coordinate f g f' g' : A → ℝ)
      (x y : A) →
    derivativeErrorAlong
        coordinate
        (λ point → f point · g point)
        (λ point →
          f' point · g point
            + f point · g' point)
        x y
      ≡
    ( g y · derivativeErrorAlong
          coordinate f f' x y
      + f x · derivativeErrorAlong
          coordinate g g' x y)
      +
    (f' x · (g y - g x))
      · (coordinate y - coordinate x)
  productDerivativeErrorPath
    coordinate f g f' g' x y =
      cong
        (_-
          (f' x · g x + f x · g' x)
            · displacement)
        (productDifferencePath
          (f y) (f x) (g y) (g x))
    ∙ cong
        (λ value →
          (g y · f-difference
            + f x · g-difference) - value)
        (mulDistL
          (f' x · g x)
          (f x · g' x)
          displacement)
    ∙ differenceOfSums
        (g y · f-difference)
        (f x · g-difference)
        ((f' x · g x) · displacement)
        ((f x · g' x) · displacement)
    ∙ cong₂ _+_
        first-factor-path
        second-factor-path
    ∙ sym
        (addAssoc
          (g y · f-error)
          cross-error
          (f x · g-error))
    ∙ cong
        (g y · f-error +_)
        (addComm cross-error (f x · g-error))
    ∙ addAssoc
        (g y · f-error)
        (f x · g-error)
        cross-error
    where
    displacement : ℝ
    displacement =
      coordinate y - coordinate x

    f-difference g-difference : ℝ
    f-difference = f y - f x
    g-difference = g y - g x

    f-error g-error : ℝ
    f-error =
      derivativeErrorAlong coordinate f f' x y
    g-error =
      derivativeErrorAlong coordinate g g' x y

    cross-error : ℝ
    cross-error =
      (f' x · g-difference) · displacement

    first-factor-path :
      g y · f-difference
          - (f' x · g x) · displacement
        ≡
      g y · f-error + cross-error
    first-factor-path =
      cong₂ _-_
        (mulComm (g y) f-difference)
        (swapNestedProduct
          (f' x) (g x) displacement)
      ∙ productDifferencePath
          f-difference
          (f' x · displacement)
          (g y) (g x)
      ∙ cong
          (g y · f-error +_)
          (swapNestedProduct
            (f' x) displacement g-difference)

    second-factor-path :
      f x · g-difference
          - (f x · g' x) · displacement
        ≡
      f x · g-error
    second-factor-path =
      cong
        (λ value →
          f x · g-difference - value)
        (mulAssoc
          (f x) (g' x) displacement)
      ∙ sym
          (ℝRing.·DistR-
            (f x)
            g-difference
            (g' x · displacement))

  positiveRationalNonnegative :
    ∀ B →
    0 ≤ℝ rat (fst B)
  positiveRationalNonnegative B =
    <ℝ-weaken
      0 (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  boundedErrorProduct :
    ∀ value error distance B ρ →
    absℝ value ≤ℝ rat (fst B) →
    absℝ error
      ≤ℝ rat (fst (ρ ₊／₊ B)) · distance →
    absℝ (value · error)
      ≤ℝ rat (fst ρ) · distance
  boundedErrorProduct
    value error distance B ρ
    absvalue≤B error-bound =
      subst
        (_≤ℝ rat (fst ρ) · distance)
        (sym (absMul value error))
        (subst
          ((absℝ value · absℝ error) ≤ℝ_)
          rational-product-path
          (mulMono≤
            (absℝ value) (rat (fst B))
            (absℝ error)
            (rat (fst (ρ ₊／₊ B)) · distance)
            (positiveRationalNonnegative B)
            (absNonnegative error)
            absvalue≤B error-bound))
    where
    rational-product-path :
      rat (fst B)
          · (rat (fst (ρ ₊／₊ B)) · distance)
        ≡
      rat (fst ρ) · distance
    rational-product-path =
      sym
        (mulAssoc
          (rat (fst B))
          (rat (fst (ρ ₊／₊ B)))
          distance)
      ∙ cong
          (_· distance)
          (mul-rat
            (fst B) (fst (ρ ₊／₊ B))
          ∙ cong rat
              (·／ B ρ))

mulHasDerivativeAlongWithContinuousRight :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  isContinuous source g (snd ℝPremetricSpace) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point · g point)
    (λ point →
      f' point · g point
        + f point · g' point)
mulHasDerivativeAlongWithContinuousRight
  {A = A} source coordinate f g f' g'
  g-continuous f-derivative g-derivative x ε = do
    value-bounds ←
      jointNaturalAbsBounds (g x) (f x)
    (n , f'-strict-bound) ←
      ∃naturalAbsBound (f' x)
    let
      B : ℚ₊
      B =
        jointBound
          {x = g x} {y = f x}
          value-bounds

      F : ℚ₊
      F = naturalBound n

      C : ℚ₊
      C = B +₊ B

      abs-gx≤B :
        absℝ (g x) ≤ℝ rat (fst B)
      abs-gx≤B =
        jointBoundContainsLeft
          {x = g x} {y = f x}
          value-bounds

      abs-fx≤B :
        absℝ (f x) ≤ℝ rat (fst B)
      abs-fx≤B =
        jointBoundContainsRight
          {x = g x} {y = f x}
          value-bounds

      abs-f'x≤F :
        absℝ (f' x) ≤ℝ rat (fst F)
      abs-f'x≤F =
        <ℝ-weaken
          (absℝ (f' x))
          (rat (fst F))
          f'-strict-bound
    (δf , f-error-near) ←
      f-derivative x ((ε /4₊) ₊／₊ C)
    (δg , g-error-near) ←
      g-derivative x ((ε /4₊) ₊／₊ B)
    (δB , g-bounded-near) ←
      g-continuous x .IsContinuousAt.pres≈ B
    (δcross , g-cross-near) ←
      g-continuous x .IsContinuousAt.pres≈
        ((ε /2₊) ₊／₊ F)
    let
      δ : ℚ₊
      δ =
        min₊ δf
          (min₊ δg
            (min₊ δB δcross))
    return
      ( δ
      , λ y x∼δy →
          let
            x∼δfy :
              PremetricStr._≈[_]_
                source x δf y
            x∼δfy =
              PremetricStr.isMonotone≈≤
                source x y δ δf
                (min₊≤L δf
                  (min₊ δg
                    (min₊ δB δcross)))
                x∼δy

            x∼δgy :
              PremetricStr._≈[_]_
                source x δg y
            x∼δgy =
              PremetricStr.isMonotone≈≤
                source x y δ δg
                (ℚ.isTrans≤
                  (fst δ)
                  (fst
                    (min₊ δg
                      (min₊ δB δcross)))
                  (fst δg)
                  (min₊≤R δf
                    (min₊ δg
                      (min₊ δB δcross)))
                  (min₊≤L δg
                    (min₊ δB δcross)))
                x∼δy

            x∼δBy :
              PremetricStr._≈[_]_
                source x δB y
            x∼δBy =
              PremetricStr.isMonotone≈≤
                source x y δ δB
                (ℚ.isTrans≤
                  (fst δ)
                  (fst
                    (min₊ δg
                      (min₊ δB δcross)))
                  (fst δB)
                  (min₊≤R δf
                    (min₊ δg
                      (min₊ δB δcross)))
                  (ℚ.isTrans≤
                    (fst
                      (min₊ δg
                        (min₊ δB δcross)))
                    (fst (min₊ δB δcross))
                    (fst δB)
                    (min₊≤R δg
                      (min₊ δB δcross))
                    (min₊≤L δB δcross)))
                x∼δy

            x∼δcrossy :
              PremetricStr._≈[_]_
                source x δcross y
            x∼δcrossy =
              PremetricStr.isMonotone≈≤
                source x y δ δcross
                (ℚ.isTrans≤
                  (fst δ)
                  (fst
                    (min₊ δg
                      (min₊ δB δcross)))
                  (fst δcross)
                  (min₊≤R δf
                    (min₊ δg
                      (min₊ δB δcross)))
                  (ℚ.isTrans≤
                    (fst
                      (min₊ δg
                        (min₊ δB δcross)))
                    (fst (min₊ δB δcross))
                    (fst δcross)
                    (min₊≤R δg
                      (min₊ δB δcross))
                    (min₊≤R δB δcross)))
                x∼δy

            gx∼Bgy : g x ∼[ B ] g y
            gx∼Bgy =
              g-bounded-near y x∼δBy

            abs-gy≤abs-gx+B :
              absℝ (g y)
                ≤ℝ absℝ (g x) + rat (fst B)
            abs-gy≤abs-gx+B =
              close→upperBound
                (absℝ (g y)) (absℝ (g x)) B
                (sym∼
                  (absℝ (g x)) (absℝ (g y)) B
                  (absPres∼
                    (g x) (g y) B gx∼Bgy))

            abs-gx+B≤C :
              absℝ (g x) + rat (fst B)
                ≤ℝ rat (fst C)
            abs-gx+B≤C =
              subst
                (absℝ (g x) + rat (fst B) ≤ℝ_)
                (rat+rat (fst B) (fst B))
                (≤ℝ-add
                  (absℝ (g x)) (rat (fst B))
                  (rat (fst B)) (rat (fst B))
                  abs-gx≤B
                  (≤ℝ-refl (rat (fst B))))

            abs-gy≤C :
              absℝ (g y) ≤ℝ rat (fst C)
            abs-gy≤C =
              ≤ℝ-trans
                (absℝ (g y))
                (absℝ (g x) + rat (fst B))
                (rat (fst C))
                abs-gy≤abs-gx+B
                abs-gx+B≤C

            displacement : ℝ
            displacement =
              coordinate y - coordinate x

            distance : ℝ
            distance = absℝ displacement

            f-error : ℝ
            f-error =
              derivativeErrorAlong
                coordinate f f' x y

            g-error : ℝ
            g-error =
              derivativeErrorAlong
                coordinate g g' x y

            first-error : ℝ
            first-error = g y · f-error

            second-error : ℝ
            second-error = f x · g-error

            cross-error : ℝ
            cross-error =
              (f' x · (g y - g x))
                · displacement

            first-bound :
              absℝ first-error
                ≤ℝ
              rat (fst (ε /4₊)) · distance
            first-bound =
              boundedErrorProduct
                (g y) f-error distance C (ε /4₊)
                abs-gy≤C
                (f-error-near y x∼δfy)

            second-bound :
              absℝ second-error
                ≤ℝ
              rat (fst (ε /4₊)) · distance
            second-bound =
              boundedErrorProduct
                (f x) g-error distance B (ε /4₊)
                abs-fx≤B
                (g-error-near y x∼δgy)

            gx∼crossgy :
              g x ∼[ (ε /2₊) ₊／₊ F ] g y
            gx∼crossgy =
              g-cross-near y x∼δcrossy

            g-difference-bound :
              absℝ (g y - g x)
                ≤ℝ
              rat (fst ((ε /2₊) ₊／₊ F))
            g-difference-bound =
              <ℝ-weaken
                (absℝ (g y - g x))
                (rat (fst ((ε /2₊) ₊／₊ F)))
                (subst
                  (_<ℝ
                    rat (fst ((ε /2₊) ₊／₊ F)))
                  (absSubComm (g x) (g y))
                  (closeness→absDifference<
                    (g x) (g y)
                    ((ε /2₊) ₊／₊ F)
                    gx∼crossgy))

            inner-cross-rational-path :
              rat (fst F)
                  · rat (fst ((ε /2₊) ₊／₊ F))
                ≡
              rat (fst (ε /2₊))
            inner-cross-rational-path =
              mul-rat
                (fst F)
                (fst ((ε /2₊) ₊／₊ F))
              ∙ cong rat
                  (·／ F (ε /2₊))

            inner-cross-bound :
              absℝ (f' x · (g y - g x))
                ≤ℝ rat (fst (ε /2₊))
            inner-cross-bound =
              subst2 _≤ℝ_
                (sym
                  (absMul
                    (f' x) (g y - g x)))
                inner-cross-rational-path
                (mulMono≤
                  (absℝ (f' x)) (rat (fst F))
                  (absℝ (g y - g x))
                  (rat
                    (fst ((ε /2₊) ₊／₊ F)))
                  (positiveRationalNonnegative F)
                  (absNonnegative (g y - g x))
                  abs-f'x≤F
                  g-difference-bound)

            cross-bound :
              absℝ cross-error
                ≤ℝ
              rat (fst (ε /2₊)) · distance
            cross-bound =
              subst
                (_≤ℝ
                  rat (fst (ε /2₊)) · distance)
                (sym
                  (absMul
                    (f' x · (g y - g x))
                    displacement))
                (mulMonoR≤
                  (absℝ
                    (f' x · (g y - g x)))
                  (rat (fst (ε /2₊)))
                  distance
                  (absNonnegative displacement)
                  inner-cross-bound)

            first-two-bound :
              absℝ (first-error + second-error)
                ≤ℝ
              rat (fst (ε /4₊)) · distance
                + rat (fst (ε /4₊)) · distance
            first-two-bound =
              ≤ℝ-trans
                (absℝ (first-error + second-error))
                (absℝ first-error + absℝ second-error)
                (rat (fst (ε /4₊)) · distance
                  + rat (fst (ε /4₊)) · distance)
                (absTriangle first-error second-error)
                (≤ℝ-add
                  (absℝ first-error)
                  (rat (fst (ε /4₊)) · distance)
                  (absℝ second-error)
                  (rat (fst (ε /4₊)) · distance)
                  first-bound second-bound)

            three-term-bound :
              absℝ
                  ((first-error + second-error)
                    + cross-error)
                ≤ℝ
              (rat (fst (ε /4₊)) · distance
                + rat (fst (ε /4₊)) · distance)
                + rat (fst (ε /2₊)) · distance
            three-term-bound =
              ≤ℝ-trans
                (absℝ
                  ((first-error + second-error)
                    + cross-error))
                (absℝ (first-error + second-error)
                  + absℝ cross-error)
                ((rat (fst (ε /4₊)) · distance
                  + rat (fst (ε /4₊)) · distance)
                  + rat (fst (ε /2₊)) · distance)
                (absTriangle
                  (first-error + second-error)
                  cross-error)
                (≤ℝ-add
                  (absℝ (first-error + second-error))
                  (rat (fst (ε /4₊)) · distance
                    + rat (fst (ε /4₊)) · distance)
                  (absℝ cross-error)
                  (rat (fst (ε /2₊)) · distance)
                  first-two-bound cross-bound)

            quarter-sum-path :
              rat (fst (ε /4₊))
                  + rat (fst (ε /4₊))
                ≡
              rat (fst (ε /2₊))
            quarter-sum-path =
              rat+rat
                (fst (ε /4₊))
                (fst (ε /4₊))
              ∙ cong rat
                  (1/2∈ℚ./4+/4≡/2
                    (fst ε))

            total-upper-path :
              (rat (fst (ε /4₊)) · distance
                + rat (fst (ε /4₊)) · distance)
                + rat (fst (ε /2₊)) · distance
                ≡
              rat (fst ε) · distance
            total-upper-path =
              cong
                (_+ rat (fst (ε /2₊)) · distance)
                (sym
                  (mulDistL
                    (rat (fst (ε /4₊)))
                    (rat (fst (ε /4₊)))
                    distance)
                ∙ cong
                    (_· distance)
                    quarter-sum-path)
              ∙ sym
                  (mulDistL
                    (rat (fst (ε /2₊)))
                    (rat (fst (ε /2₊)))
                    distance)
              ∙ cong
                  (_· distance)
                  (rat+rat
                    (fst (ε /2₊))
                    (fst (ε /2₊))
                  ∙ cong rat
                      (1/2∈ℚ./2+/2≡id
                        (fst ε)))
          in
            subst
              (λ error →
                absℝ error
                  ≤ℝ rat (fst ε) · distance)
              (sym
                (productDerivativeErrorPath
                  coordinate f g f' g' x y))
              (subst
                (absℝ
                  ((first-error + second-error)
                    + cross-error) ≤ℝ_)
                total-upper-path
                three-term-bound)
      )

mulHasDerivativeWithContinuousRight :
  ∀ f g f' g' →
  isContinuous
    (snd ℝPremetricSpace) g
    (snd ℝPremetricSpace) →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x · g x)
    (λ x → f' x · g x + f x · g' x)
mulHasDerivativeWithContinuousRight
  f g f' g' =
    mulHasDerivativeAlongWithContinuousRight
      (snd ℝPremetricSpace)
      (λ x → x)
      f g f' g'

mulHasDerivativeAlongWithContinuousLeft :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  isContinuous source f (snd ℝPremetricSpace) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point · g point)
    (λ point →
      f' point · g point
        + f point · g' point)
mulHasDerivativeAlongWithContinuousLeft
  source coordinate f g f' g'
  f-continuous f-derivative g-derivative =
    subst2
      (IsDerivativeAlong source coordinate)
      function-path derivative-path
      (mulHasDerivativeAlongWithContinuousRight
        source coordinate
        g f g' f'
        f-continuous
        g-derivative f-derivative)
  where
  function-path :
    (λ point → g point · f point)
      ≡
    (λ point → f point · g point)
  function-path =
    funExt
      (λ point →
        mulComm (g point) (f point))

  derivative-path :
    (λ point →
      g' point · f point
        + g point · f' point)
      ≡
    (λ point →
      f' point · g point
        + f point · g' point)
  derivative-path =
    funExt
      (λ point →
        cong₂ _+_
          (mulComm (g' point) (f point))
          (mulComm (g point) (f' point))
        ∙ addComm
            (f point · g' point)
            (f' point · g point))

mulHasDerivativeWithContinuousLeft :
  ∀ f g f' g' →
  isContinuous
    (snd ℝPremetricSpace) f
    (snd ℝPremetricSpace) →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x · g x)
    (λ x → f' x · g x + f x · g' x)
mulHasDerivativeWithContinuousLeft
  f g f' g' =
    mulHasDerivativeAlongWithContinuousLeft
      (snd ℝPremetricSpace)
      (λ x → x)
      f g f' g'

mulHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  isContinuous
    source coordinate
    (snd ℝPremetricSpace) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point · g point)
    (λ point →
      f' point · g point
        + f point · g' point)
mulHasDerivativeAlong
  source coordinate f g f' g'
  coordinate-continuous f-derivative g-derivative =
    mulHasDerivativeAlongWithContinuousRight
      source coordinate f g f' g'
      (derivativeAlongIsContinuous
        source coordinate g g'
        coordinate-continuous g-derivative)
      f-derivative g-derivative

mulHasDerivative :
  ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x · g x)
    (λ x → f' x · g x + f x · g' x)
mulHasDerivative f g f' g' =
  mulHasDerivativeAlong
    (snd ℝPremetricSpace)
    (λ x → x)
    f g f' g'
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))
