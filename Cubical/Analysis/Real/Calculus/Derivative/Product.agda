module Cubical.Analysis.Real.Calculus.Derivative.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Metric using (close→upperBound)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
  using (closeness→absDifference<)
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  differenceOfSums : ∀ (a b c d : ℝ) →
    (a + b) - (c + d) ≡ (a - c) + (b - d)
  differenceOfSums a b c d =
    cong ((a + b) +_) (negAdd c d)
    ∙ sym (addAssoc a b ((- c) + (- d)))
    ∙ cong (a +_) (addAssoc b (- c) (- d))
    ∙ cong (λ value → a + (value + (- d)))
        (addComm b (- c))
    ∙ cong (a +_)
        (sym (addAssoc (- c) b (- d)))
    ∙ addAssoc a (- c) (b + (- d))

  swapNestedProduct : ∀ a b c →
    (a · b) · c ≡ (a · c) · b
  swapNestedProduct a b c =
    sym (mulAssoc a b c)
    ∙ cong (a ·_) (mulComm b c)
    ∙ mulAssoc a c b

  productDifferencePath : ∀ a b c d →
    a · c - b · d ≡ c · (a - b) + b · (c - d)
  productDifferencePath a b c d =
    cong ((a · c) +_)
      (sym (addIdL (- (b · d))))
    ∙ cong
        (λ value → a · c + (value + (- (b · d))))
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
          f' point · g point + f point · g' point)
        x y
      ≡
    ( g y · derivativeErrorAlong coordinate f f' x y
      + f x · derivativeErrorAlong coordinate g g' x y)
      +
    (f' x · (g y - g x)) ·
      (coordinate y - coordinate x)
  productDerivativeErrorPath
    coordinate f g f' g' x y =
      cong
        (_-
          (f' x · g x + f x · g' x) · displacement)
        (productDifferencePath
          (f y) (f x) (g y) (g x))
    ∙ cong
        (λ value →
          (g y · f-difference + f x · g-difference) - value)
        (mulDistL
          (f' x · g x) (f x · g' x) displacement)
    ∙ differenceOfSums
        (g y · f-difference)
        (f x · g-difference)
        ((f' x · g x) · displacement)
        ((f x · g' x) · displacement)
    ∙ cong₂ _+_ first-factor-path second-factor-path
    ∙ sym
        (addAssoc
          (g y · f-error) cross-error (f x · g-error))
    ∙ cong
        (g y · f-error +_)
        (addComm cross-error (f x · g-error))
    ∙ addAssoc
        (g y · f-error) (f x · g-error) cross-error
    where
    displacement : ℝ
    displacement = coordinate y - coordinate x

    f-difference g-difference : ℝ
    f-difference = f y - f x
    g-difference = g y - g x

    f-error g-error : ℝ
    f-error = derivativeErrorAlong coordinate f f' x y
    g-error = derivativeErrorAlong coordinate g g' x y

    cross-error : ℝ
    cross-error = (f' x · g-difference) · displacement

    first-factor-path :
      g y · f-difference - (f' x · g x) · displacement
        ≡
      g y · f-error + cross-error
    first-factor-path =
      cong₂ _-_
        (mulComm (g y) f-difference)
        (swapNestedProduct (f' x) (g x) displacement)
      ∙ productDifferencePath
          f-difference (f' x · displacement) (g y) (g x)
      ∙ cong
          (g y · f-error +_)
          (swapNestedProduct
            (f' x) displacement g-difference)

    second-factor-path :
      f x · g-difference - (f x · g' x) · displacement
        ≡
      f x · g-error
    second-factor-path =
      cong
        (λ value → f x · g-difference - value)
        (sym (mulAssoc (f x) (g' x) displacement))
      ∙ sym
          (ℝRing.·DistR-
            (f x) g-difference (g' x · displacement))

  positiveRationalNonnegative : ∀ B →
    0ℝ ≤ℝ rat (fst B)
  positiveRationalNonnegative B =
    <ℝ-weaken
      0ℝ (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  boundedErrorProduct : ∀ value error distance B ρ →
    absℝ value ≤ℝ rat (fst B) →
    absℝ error
      ≤ℝ rat (fst (ρ ₊／₊ B)) · distance →
    absℝ (value · error)
      ≤ℝ rat (fst ρ) · distance
  boundedErrorProduct
    value error distance B ρ absvalue≤B error-bound =
      subst
        (_≤ℝ rat (fst ρ) · distance)
        (sym (absMul value error))
        (subst
          ((absℝ value · absℝ error) ≤ℝ_)
          rational-product-path
          (mulPres≤
            (absℝ value) (rat (fst B))
            (absℝ error)
            (rat (fst (ρ ₊／₊ B)) · distance)
            (positiveRationalNonnegative B)
            (absNonnegative error)
            absvalue≤B error-bound))
    where
    rational-product-path :
      rat (fst B) ·
          (rat (fst (ρ ₊／₊ B)) · distance)
        ≡
      rat (fst ρ) · distance
    rational-product-path =
      mulAssoc
        (rat (fst B)) (rat (fst (ρ ₊／₊ B))) distance
      ∙ cong
          (_· distance)
          (mul-rat (fst B) (fst (ρ ₊／₊ B))
          ∙ cong rat (·／ B ρ))


-- The explicit continuity premise is useful when the coordinate map is not
-- known to be continuous.  The ordinary rule below discharges it from the
-- derivative of the right factor.
mulHasDerivativeAlongWithContinuousRight :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  isContinuous source g (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point · g point)
    (λ point →
      f' point · g point + f point · g' point)
mulHasDerivativeAlongWithContinuousRight
  {A = A} source coordinate f g f' g'
  g-continuous f-derivative g-derivative x ε = do
    (ng , gx-strict-bound) ← ∃naturalAbsBound (g x)
    (nf , fx-strict-bound) ← ∃naturalAbsBound (f x)
    (nd , f'-strict-bound) ← ∃naturalAbsBound (f' x)
    let
      G : ℚ₊
      G = naturalBound ng

      X : ℚ₊
      X = naturalBound nf

      F : ℚ₊
      F = naturalBound nd

      C : ℚ₊
      C = G +₊ G

      abs-gx≤G : absℝ (g x) ≤ℝ rat (fst G)
      abs-gx≤G =
        <ℝ-weaken
          (absℝ (g x)) (rat (fst G)) gx-strict-bound

      abs-fx≤X : absℝ (f x) ≤ℝ rat (fst X)
      abs-fx≤X =
        <ℝ-weaken
          (absℝ (f x)) (rat (fst X)) fx-strict-bound

      abs-f'x≤F : absℝ (f' x) ≤ℝ rat (fst F)
      abs-f'x≤F =
        <ℝ-weaken
          (absℝ (f' x)) (rat (fst F)) f'-strict-bound
    (δf , f-error-near) ←
      f-derivative x ((ε /4₊) ₊／₊ C)
    (δg , g-error-near) ←
      g-derivative x ((ε /4₊) ₊／₊ X)
    (δG , g-bounded-near) ←
      g-continuous x .IsContinuousAt.pres≈ G
    (δcross , g-cross-near) ←
      g-continuous x .IsContinuousAt.pres≈
        ((ε /2₊) ₊／₊ F)
    let
      δ : ℚ₊
      δ =
        min₊ δf
          (min₊ δg
            (min₊ δG δcross))
    return
      ( δ
      , λ y x∼δy →
          let
            x∼δfy :
              PremetricStr._≈[_]_ source x δf y
            x∼δfy =
              PremetricStr.isMonotone≈≤
                source x y δ δf
                (min₊≤L δf
                  (min₊ δg (min₊ δG δcross)))
                x∼δy

            x∼δgy :
              PremetricStr._≈[_]_ source x δg y
            x∼δgy =
              PremetricStr.isMonotone≈≤
                source x y δ δg
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δg (min₊ δG δcross)))
                  (fst δg)
                  (min₊≤R δf
                    (min₊ δg (min₊ δG δcross)))
                  (min₊≤L δg (min₊ δG δcross)))
                x∼δy

            x∼δGy :
              PremetricStr._≈[_]_ source x δG y
            x∼δGy =
              PremetricStr.isMonotone≈≤
                source x y δ δG
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δg (min₊ δG δcross)))
                  (fst δG)
                  (min₊≤R δf
                    (min₊ δg (min₊ δG δcross)))
                  (ℚ.isTrans≤
                    (fst (min₊ δg (min₊ δG δcross)))
                    (fst (min₊ δG δcross))
                    (fst δG)
                    (min₊≤R δg (min₊ δG δcross))
                    (min₊≤L δG δcross)))
                x∼δy

            x∼δcrossy :
              PremetricStr._≈[_]_ source x δcross y
            x∼δcrossy =
              PremetricStr.isMonotone≈≤
                source x y δ δcross
                (ℚ.isTrans≤
                  (fst δ)
                  (fst (min₊ δg (min₊ δG δcross)))
                  (fst δcross)
                  (min₊≤R δf
                    (min₊ δg (min₊ δG δcross)))
                  (ℚ.isTrans≤
                    (fst (min₊ δg (min₊ δG δcross)))
                    (fst (min₊ δG δcross))
                    (fst δcross)
                    (min₊≤R δg (min₊ δG δcross))
                    (min₊≤R δG δcross)))
                x∼δy

            gx∼Ggy : g x ∼[ G ] g y
            gx∼Ggy = g-bounded-near y x∼δGy

            abs-gy≤abs-gx+G :
              absℝ (g y) ≤ℝ absℝ (g x) + rat (fst G)
            abs-gy≤abs-gx+G =
              close→upperBound
                (absℝ (g y)) (absℝ (g x)) G
                (sym∼
                  (absℝ (g x)) (absℝ (g y)) G
                  (abs-pres∼ (g x) (g y) G gx∼Ggy))

            abs-gx+G≤C :
              absℝ (g x) + rat (fst G) ≤ℝ rat (fst C)
            abs-gx+G≤C =
              subst
                (absℝ (g x) + rat (fst G) ≤ℝ_)
                (rat+rat (fst G) (fst G))
                (addPres≤
                  (absℝ (g x)) (rat (fst G))
                  (rat (fst G)) (rat (fst G))
                  abs-gx≤G (≤ℝ-refl (rat (fst G))))

            abs-gy≤C : absℝ (g y) ≤ℝ rat (fst C)
            abs-gy≤C =
              ≤ℝ-trans
                (absℝ (g y))
                (absℝ (g x) + rat (fst G))
                (rat (fst C))
                abs-gy≤abs-gx+G abs-gx+G≤C

            displacement : ℝ
            displacement = coordinate y - coordinate x

            distance : ℝ
            distance = absℝ displacement

            f-error : ℝ
            f-error = derivativeErrorAlong coordinate f f' x y

            g-error : ℝ
            g-error = derivativeErrorAlong coordinate g g' x y

            first-error : ℝ
            first-error = g y · f-error

            second-error : ℝ
            second-error = f x · g-error

            cross-error : ℝ
            cross-error =
              (f' x · (g y - g x)) · displacement

            first-bound :
              absℝ first-error
                ≤ℝ rat (fst (ε /4₊)) · distance
            first-bound =
              boundedErrorProduct
                (g y) f-error distance C (ε /4₊)
                abs-gy≤C (f-error-near y x∼δfy)

            second-bound :
              absℝ second-error
                ≤ℝ rat (fst (ε /4₊)) · distance
            second-bound =
              boundedErrorProduct
                (f x) g-error distance X (ε /4₊)
                abs-fx≤X (g-error-near y x∼δgy)

            gx∼crossgy :
              g x ∼[ (ε /2₊) ₊／₊ F ] g y
            gx∼crossgy = g-cross-near y x∼δcrossy

            g-difference-bound :
              absℝ (g y - g x)
                ≤ℝ rat (fst ((ε /2₊) ₊／₊ F))
            g-difference-bound =
              <ℝ-weaken
                (absℝ (g y - g x))
                (rat (fst ((ε /2₊) ₊／₊ F)))
                (subst
                  (_<ℝ rat (fst ((ε /2₊) ₊／₊ F)))
                  (absSubComm (g x) (g y))
                  (closeness→absDifference<
                    (g x) (g y) ((ε /2₊) ₊／₊ F)
                    gx∼crossgy))

            inner-cross-rational-path :
              rat (fst F) · rat (fst ((ε /2₊) ₊／₊ F))
                ≡
              rat (fst (ε /2₊))
            inner-cross-rational-path =
              mul-rat (fst F) (fst ((ε /2₊) ₊／₊ F))
              ∙ cong rat (·／ F (ε /2₊))

            inner-cross-bound :
              absℝ (f' x · (g y - g x))
                ≤ℝ rat (fst (ε /2₊))
            inner-cross-bound =
              subst2 _≤ℝ_
                (sym (absMul (f' x) (g y - g x)))
                inner-cross-rational-path
                (mulPres≤
                  (absℝ (f' x)) (rat (fst F))
                  (absℝ (g y - g x))
                  (rat (fst ((ε /2₊) ₊／₊ F)))
                  (positiveRationalNonnegative F)
                  (absNonnegative (g y - g x))
                  abs-f'x≤F g-difference-bound)

            cross-bound :
              absℝ cross-error
                ≤ℝ rat (fst (ε /2₊)) · distance
            cross-bound =
              subst
                (_≤ℝ rat (fst (ε /2₊)) · distance)
                (sym
                  (absMul
                    (f' x · (g y - g x)) displacement))
                (mulPres≤R-0≤
                  (absℝ (f' x · (g y - g x)))
                  (rat (fst (ε /2₊))) distance
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
                (addPres≤
                  (absℝ first-error)
                  (rat (fst (ε /4₊)) · distance)
                  (absℝ second-error)
                  (rat (fst (ε /4₊)) · distance)
                  first-bound second-bound)

            three-term-bound :
              absℝ ((first-error + second-error) + cross-error)
                ≤ℝ
              (rat (fst (ε /4₊)) · distance
                + rat (fst (ε /4₊)) · distance)
                + rat (fst (ε /2₊)) · distance
            three-term-bound =
              ≤ℝ-trans
                (absℝ ((first-error + second-error) + cross-error))
                (absℝ (first-error + second-error) + absℝ cross-error)
                ((rat (fst (ε /4₊)) · distance
                  + rat (fst (ε /4₊)) · distance)
                  + rat (fst (ε /2₊)) · distance)
                (absTriangle (first-error + second-error) cross-error)
                (addPres≤
                  (absℝ (first-error + second-error))
                  (rat (fst (ε /4₊)) · distance
                    + rat (fst (ε /4₊)) · distance)
                  (absℝ cross-error)
                  (rat (fst (ε /2₊)) · distance)
                  first-two-bound cross-bound)

            quarter-sum-path :
              rat (fst (ε /4₊)) + rat (fst (ε /4₊))
                ≡
              rat (fst (ε /2₊))
            quarter-sum-path =
              rat+rat (fst (ε /4₊)) (fst (ε /4₊))
              ∙ cong rat (/4+/4≡/2 (fst ε))

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
                    (rat (fst (ε /4₊))) distance)
                ∙ cong (_· distance) quarter-sum-path)
              ∙ sym
                  (mulDistL
                    (rat (fst (ε /2₊)))
                    (rat (fst (ε /2₊))) distance)
              ∙ cong
                  (_· distance)
                  (rat+rat (fst (ε /2₊)) (fst (ε /2₊))
                  ∙ cong rat (/2+/2≡id (fst ε)))
          in
            subst
              (λ error →
                absℝ error ≤ℝ rat (fst ε) · distance)
              (sym
                (productDerivativeErrorPath
                  coordinate f g f' g' x y))
              (subst
                (absℝ
                  ((first-error + second-error) + cross-error) ≤ℝ_)
                total-upper-path three-term-bound)
      )


mulHasDerivativeWithContinuousRight : ∀ f g f' g' →
  isContinuous
    (ℝPremetricSpace .snd) g
    (ℝPremetricSpace .snd) →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x · g x)
    (λ x → f' x · g x + f x · g' x)
mulHasDerivativeWithContinuousRight f g f' g' =
  mulHasDerivativeAlongWithContinuousRight
    (ℝPremetricSpace .snd) (idfun ℝ) f g f' g'


mulHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate f g f' g' : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate f f' →
  IsDerivativeAlong source coordinate g g' →
  IsDerivativeAlong
    source coordinate
    (λ point → f point · g point)
    (λ point →
      f' point · g point + f point · g' point)
mulHasDerivativeAlong
  source coordinate f g f' g'
  coordinate-continuous f-derivative g-derivative =
    mulHasDerivativeAlongWithContinuousRight
      source coordinate f g f' g'
      (derivativeAlongIsContinuous
        source coordinate g g'
        coordinate-continuous g-derivative)
      f-derivative g-derivative


mulHasDerivative : ∀ f g f' g' →
  IsDerivative f f' →
  IsDerivative g g' →
  IsDerivative
    (λ x → f x · g x)
    (λ x → f' x · g x + f x · g' x)
mulHasDerivative f g f' g' =
  mulHasDerivativeAlong
    (ℝPremetricSpace .snd) (idfun ℝ) f g f' g'
    (snd (CategoryStructures.idᶜ {M = ℝPremetricSpace}))
