module Cubical.Analysis.Real.Calculus.Derivative.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Calculus.Derivative.Base

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  differenceOfSums : ∀ (a b c d : ℝ) →
    (a + b) - (c + d) ≡
    (a - c) + (b - d)
  differenceOfSums a b c d =
    cong ((a + b) +_) (negAdd c d)
    ∙ sym (addAssoc a b ((- c) + (- d)))
    ∙ cong (a +_) (addAssoc b (- c) (- d))
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
    derivativeErrorAlong coordinate f f' x y +
      derivativeErrorAlong coordinate g g' x y
  addDerivativeErrorPath coordinate f g f' g' x y =
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
    (δf , f-bound) ← f-derivative x (ε /2₊)
    (δg , g-bound) ← g-derivative x (ε /2₊)
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
  distance y = absℝ (coordinate y - coordinate x)

  half-coefficient : ℝ
  half-coefficient = rat (fst (ε /2₊))

  upper-path : ∀ y →
    half-coefficient · distance y +
        half-coefficient · distance y
      ≡
    rat (fst ε) · distance y
  upper-path y =
    sym
      (mulDistL
        half-coefficient half-coefficient (distance y))
    ∙ cong (_· distance y)
        (rat+rat
          (fst (ε /2₊)) (fst (ε /2₊))
        ∙ cong rat (/2+/2≡id (fst ε)))

  total-bound : ∀ y →
    absℝ (derivativeErrorAlong coordinate f f' x y)
      ≤ℝ half-coefficient · distance y →
    absℝ (derivativeErrorAlong coordinate g g' x y)
      ≤ℝ half-coefficient · distance y →
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
        absℝ error ≤ℝ rat (fst ε) · distance y)
      (sym
        (addDerivativeErrorPath
          coordinate f g f' g' x y))
      (≤ℝ-trans
        (absℝ
          (derivativeErrorAlong coordinate f f' x y +
            derivativeErrorAlong coordinate g g' x y))
        (absℝ (derivativeErrorAlong coordinate f f' x y) +
          absℝ (derivativeErrorAlong coordinate g g' x y))
        (rat (fst ε) · distance y)
        (absTriangle
          (derivativeErrorAlong coordinate f f' x y)
          (derivativeErrorAlong coordinate g g' x y))
        (subst
          ((absℝ (derivativeErrorAlong coordinate f f' x y) +
            absℝ (derivativeErrorAlong coordinate g g' x y)) ≤ℝ_)
          (upper-path y)
          (addPres≤
            (absℝ (derivativeErrorAlong coordinate f f' x y))
            (half-coefficient · distance y)
            (absℝ (derivativeErrorAlong coordinate g g' x y))
            (half-coefficient · distance y)
            f-bound g-bound)))


addHasDerivative : ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x + g x)
    (λ x → f' x + g' x)
addHasDerivative f g f' g' =
  addHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    f g f' g'


private
  negSub : ∀ a b → - (a - b) ≡ b - a
  negSub a b =
    negAdd a (- b)
    ∙ cong ((- a) +_) (negInvol b)
    ∙ addComm (- a) b

  differenceOfNegatives : ∀ a b →
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
    - derivativeErrorAlong coordinate f f' x y
  negDerivativeErrorPath coordinate f f' x y =
    cong₂ _-_
      (differenceOfNegatives (f y) (f x))
      (ℝRing.-DistL·
        (f' x) (coordinate y - coordinate x))
    ∙ differenceOfNegatives
        (f y - f x)
        (f' x · (coordinate y - coordinate x))


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
    (δ , error-bound) ← f-derivative x ε
    return
      ( δ
      , λ y x∼y →
          subst
            (λ error →
              absℝ error ≤ℝ
                rat (fst ε) ·
                  absℝ (coordinate y - coordinate x))
            (sym (negDerivativeErrorPath coordinate f f' x y))
            (subst
              (_≤ℝ
                rat (fst ε) ·
                  absℝ (coordinate y - coordinate x))
              (sym
                (absNeg
                  (derivativeErrorAlong coordinate f f' x y)))
              (error-bound y x∼y))
      )


negHasDerivative : ∀ f f' →
  IsDerivative f f' →
  IsDerivative
    (λ x → - f x)
    (λ x → - f' x)
negHasDerivative f f' =
  negHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    f f'


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


subHasDerivative : ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x - g x)
    (λ x → f' x - g' x)
subHasDerivative f g f' g' =
  subHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
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
    c · derivativeErrorAlong coordinate f f' x y
  scaleDerivativeErrorPath coordinate f f' c x y =
    cong₂ _-_
      (sym (ℝRing.·DistR- c (f y) (f x)))
      (sym
        (mulAssoc
          c (f' x) (coordinate y - coordinate x)))
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
  distance y = absℝ (coordinate y - coordinate x)

  error : A → ℝ
  error y = derivativeErrorAlong coordinate f f' x y

  positive-bound : 0ℝ ≤ℝ rat (fst B)
  positive-bound =
    <ℝ-weaken 0ℝ (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  upper-path : ∀ y →
    rat (fst B) ·
        (rat (fst (ε ₊／₊ B)) · distance y)
      ≡
    rat (fst ε) · distance y
  upper-path y =
    mulAssoc
      (rat (fst B))
      (rat (fst (ε ₊／₊ B)))
      (distance y)
    ∙ cong (_· distance y)
        (mul-rat
          (fst B) (fst (ε ₊／₊ B))
        ∙ cong rat (·／ B ε))

  scaled-error-bound : ∀ y →
    absℝ (error y) ≤ℝ
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
        absℝ value ≤ℝ rat (fst ε) · distance y)
      (sym
        (scaleDerivativeErrorPath
          coordinate f f' c x y))
      (subst
        (_≤ℝ rat (fst ε) · distance y)
        (sym (absMul c (error y)))
        (subst
          ((absℝ c · absℝ (error y)) ≤ℝ_)
          (upper-path y)
          (mulPres≤
            (absℝ c) (rat (fst B))
            (absℝ (error y))
            (rat (fst (ε ₊／₊ B)) · distance y)
            positive-bound
            (absNonnegative (error y))
            absc≤B base-bound)))


scaleHasDerivativeAtBound : ∀ f f' c B →
  absℝ c ≤ℝ rat (fst B) →
  IsDerivative f f' →
  IsDerivative
    (λ x → c · f x)
    (λ x → c · f' x)
scaleHasDerivativeAtBound f f' c B =
  scaleHasDerivativeAlongAtBound
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    f f' c B


-- The Archimedean witness is eliminated separately for each requested local
-- radius; no global bound or countable family of choices is selected.

scaleHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → ℝ)
    (c : ℝ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → c · f point)
    (λ point → c · f' point)
scaleHasDerivativeAlong
  source coordinate f f' c f-derivative x ε = do
    (n , absc<n) ← ∃naturalAbsBound c
    scaleHasDerivativeAlongAtBound
      source coordinate f f'
      c (naturalBound n)
      (<ℝ-weaken
        (absℝ c) (rat (naturalRational n)) absc<n)
      f-derivative x ε


scaleHasDerivative : ∀ f f' c →
  IsDerivative f f' →
  IsDerivative
    (λ x → c · f x)
    (λ x → c · f' x)
scaleHasDerivative f f' c =
  scaleHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    f f' c


rationalScaleHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f f' : A → ℝ)
    (q : ℚ) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong
    source coordinate
    (λ point → q ⋆ f point)
    (λ point → q ⋆ f' point)
rationalScaleHasDerivativeAlong
  source coordinate f f' q f-derivative =
  subst2
    (IsDerivativeAlong source coordinate)
    (funExt λ point →
      sym (scalar-as-mul q (f point)))
    (funExt λ point →
      sym (scalar-as-mul q (f' point)))
    (scaleHasDerivativeAlong
      source coordinate f f' (rat q) f-derivative)


rationalScaleHasDerivative : ∀ f f' q →
  IsDerivative f f' →
  IsDerivative
    (λ x → q ⋆ f x)
    (λ x → q ⋆ f' x)
rationalScaleHasDerivative f f' q =
  rationalScaleHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    f f' q
