module Cubical.Analysis.Real.Algebra.Polynomial.LocalLipschitz where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Polynomial
open import Cubical.Analysis.Real.Algebra.Polynomial.Bounds
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication

open PositiveRationals using (ℚ₊; _·₊_)


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  addNonnegative : ∀ x y →
    0ℝ ≤ℝ x → 0ℝ ≤ℝ y →
    0ℝ ≤ℝ x + y
  addNonnegative x y 0≤x 0≤y =
    subst (_≤ℝ (x + y))
      (addIdL 0ℝ)
      (≤ℝ-trans
        (0ℝ + 0ℝ) (x + 0ℝ) (x + y)
        (addPres≤R 0ℝ x 0ℝ 0≤x)
        (addPres≤L 0ℝ y x 0≤y))

  mulNonnegative : ∀ x y →
    0ℝ ≤ℝ x → 0ℝ ≤ℝ y →
    0ℝ ≤ℝ x · y
  mulNonnegative x y 0≤x 0≤y =
    isNonnegative→0≤ (x · y)
      (mulPresIsNonnegative x y
        (0≤→isNonnegative x 0≤x)
        (0≤→isNonnegative y 0≤y))

-- Horner's recurrence gives this recurrence for a Lipschitz constant on the
-- ball |x| ≤ radius.  The head coefficient contributes no variation.

polynomialLipschitzMajorant : List ℝ → ℝ → ℝ
polynomialLipschitzMajorant [] radius =
  0ℝ
polynomialLipschitzMajorant (a ∷ coefficients) radius =
  polynomialMajorant coefficients radius
  + radius · polynomialLipschitzMajorant coefficients radius


polynomialLipschitzMajorantNonnegative : ∀ coefficients radius →
  0ℝ ≤ℝ radius →
  0ℝ ≤ℝ polynomialLipschitzMajorant coefficients radius
polynomialLipschitzMajorantNonnegative [] radius 0≤radius =
  ≤ℝ-refl 0ℝ
polynomialLipschitzMajorantNonnegative
  (a ∷ coefficients) radius 0≤radius =
  addNonnegative
    (polynomialMajorant coefficients radius)
    (radius · polynomialLipschitzMajorant coefficients radius)
    (polynomialMajorantNonnegative coefficients radius 0≤radius)
    (mulNonnegative
      radius (polynomialLipschitzMajorant coefficients radius)
      0≤radius
      (polynomialLipschitzMajorantNonnegative
        coefficients radius 0≤radius))


private
  hornerDifferencePath : ∀ a x y p q →
    (a + x · p) - (a + y · q) ≡
    (x - y) · p + y · (p - q)
  hornerDifferencePath a x y p q =
    sym (ℝRing.translatedDifference a (x · p) (y · q))
    ∙ productDifferencePath
    where
    xp : ℝ
    xp = x · p

    yp : ℝ
    yp = y · p

    yq : ℝ
    yq = y · q

    productDifferencePath :
      xp - yq ≡ (x - y) · p + y · (p - q)
    productDifferencePath =
      cong (xp +_) (sym (addIdL (- yq)))
      ∙ cong (λ z → xp + (z + (- yq))) (sym (addInvL yp))
      ∙ addAssoc xp ((- yp) + yp) (- yq)
      ∙ cong (_+ (- yq)) (addAssoc xp (- yp) yp)
      ∙ sym (addAssoc (xp + (- yp)) yp (- yq))
      ∙ cong₂ _+_
          (sym (ℝRing.·DistL- x y p))
          (sym (ℝRing.·DistR- y p q))


evaluatePolynomialLipschitzBound :
  ∀ coefficients radius x y →
  0ℝ ≤ℝ radius →
  absℝ x ≤ℝ radius →
  absℝ y ≤ℝ radius →
  absℝ
    (evaluatePolynomial coefficients x
      - evaluatePolynomial coefficients y)
    ≤ℝ
  polynomialLipschitzMajorant coefficients radius
    · absℝ (x - y)
evaluatePolynomialLipschitzBound
  [] radius x y 0≤radius absx≤radius absy≤radius =
  subst2 _≤ℝ_
    (sym (cong absℝ (subSelf 0ℝ) ∙ absZero))
    (sym (ℝRing.0LeftAnnihilates (absℝ (x - y))))
    (≤ℝ-refl 0ℝ)
evaluatePolynomialLipschitzBound
  (a ∷ coefficients) radius x y
  0≤radius absx≤radius absy≤radius =
  subst
    (λ difference → absℝ difference ≤ℝ lipschitz · distance)
    (sym (hornerDifferencePath a x y tail-x tail-y))
    decompositionBound
  where
  tail-x : ℝ
  tail-x = evaluatePolynomial coefficients x

  tail-y : ℝ
  tail-y = evaluatePolynomial coefficients y

  majorant : ℝ
  majorant = polynomialMajorant coefficients radius

  tail-lipschitz : ℝ
  tail-lipschitz = polynomialLipschitzMajorant coefficients radius

  lipschitz : ℝ
  lipschitz = majorant + radius · tail-lipschitz

  distance : ℝ
  distance = absℝ (x - y)

  firstTermBound :
    absℝ ((x - y) · tail-x) ≤ℝ majorant · distance
  firstTermBound =
    subst (_≤ℝ majorant · distance)
      (sym
        (absMul (x - y) tail-x
        ∙ mulComm distance (absℝ tail-x)))
      (mulPres≤R-0≤
        (absℝ tail-x) majorant distance
        (absNonnegative (x - y))
        (≤ℝ-trans
          (absℝ tail-x)
          (polynomialMajorant coefficients (absℝ x))
          majorant
          (evaluatePolynomialAbsBound coefficients x)
          (polynomialMajorantMono
            coefficients (absℝ x) radius
            (absNonnegative x) absx≤radius)))

  secondTermBound :
    absℝ (y · (tail-x - tail-y)) ≤ℝ
    radius · (tail-lipschitz · distance)
  secondTermBound =
    subst (_≤ℝ radius · (tail-lipschitz · distance))
      (sym (absMul y (tail-x - tail-y)))
      (mulPres≤
        (absℝ y) radius
        (absℝ (tail-x - tail-y))
        (tail-lipschitz · distance)
        0≤radius
        (absNonnegative (tail-x - tail-y))
        absy≤radius
        (evaluatePolynomialLipschitzBound
          coefficients radius x y
          0≤radius absx≤radius absy≤radius))

  sumBoundsPath :
    majorant · distance
      + radius · (tail-lipschitz · distance)
    ≡ lipschitz · distance
  sumBoundsPath =
    cong (majorant · distance +_)
      (mulAssoc radius tail-lipschitz distance)
    ∙ sym (mulDistL majorant (radius · tail-lipschitz) distance)

  rawDecompositionBound :
    absℝ
      ((x - y) · tail-x
        + y · (tail-x - tail-y))
      ≤ℝ
    majorant · distance
      + radius · (tail-lipschitz · distance)
  rawDecompositionBound =
    ≤ℝ-trans
      (absℝ
        ((x - y) · tail-x
          + y · (tail-x - tail-y)))
      (absℝ ((x - y) · tail-x)
        + absℝ (y · (tail-x - tail-y)))
      (majorant · distance
        + radius · (tail-lipschitz · distance))
      (absTriangle
        ((x - y) · tail-x)
        (y · (tail-x - tail-y)))
      (addPres≤
        (absℝ ((x - y) · tail-x))
        (majorant · distance)
        (absℝ (y · (tail-x - tail-y)))
        (radius · (tail-lipschitz · distance))
        firstTermBound secondTermBound)

  decompositionBound :
    absℝ
      ((x - y) · tail-x
        + y · (tail-x - tail-y))
      ≤ℝ lipschitz · distance
  decompositionBound =
    subst
      (λ upper →
        absℝ
          ((x - y) · tail-x
            + y · (tail-x - tail-y))
          ≤ℝ upper)
      sumBoundsPath
      rawDecompositionBound


evaluatePolynomialLipschitzOnRationalBall :
  ∀ coefficients (B L : ℚ₊) →
  polynomialLipschitzMajorant coefficients (rat (fst B))
    ≤ℝ rat (fst L) →
  ∀ x y →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  ∀ ε →
  x ∼[ ε ] y →
  evaluatePolynomial coefficients x
    ∼[ L ·₊ ε ]
  evaluatePolynomial coefficients y
evaluatePolynomialLipschitzOnRationalBall
  coefficients B L majorant≤L
  x y absx≤B absy≤B ε x∼y =
  absDifference<→closeness
    (evaluatePolynomial coefficients x)
    (evaluatePolynomial coefficients y)
    (L ·₊ ε)
    outputDifferenceStrict
  where
  distance : ℝ
  distance = absℝ (x - y)

  distance<ε : distance <ℝ rat (fst ε)
  distance<ε = closeness→absDifference< x y ε x∼y

  radiusNonnegative : 0ℝ ≤ℝ rat (fst B)
  radiusNonnegative =
    <ℝ-weaken 0ℝ (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  hornerBound :
    absℝ
      (evaluatePolynomial coefficients x
        - evaluatePolynomial coefficients y)
      ≤ℝ
    polynomialLipschitzMajorant coefficients (rat (fst B))
      · distance
  hornerBound =
    evaluatePolynomialLipschitzBound
      coefficients (rat (fst B)) x y
      radiusNonnegative absx≤B absy≤B

  rationalMajorantBound :
    polynomialLipschitzMajorant coefficients (rat (fst B))
      · distance
      ≤ℝ
    rat (fst L) · distance
  rationalMajorantBound =
    mulPres≤R-0≤
      (polynomialLipschitzMajorant coefficients (rat (fst B)))
      (rat (fst L))
      distance
      (absNonnegative (x - y))
      majorant≤L

  scaledDistanceStrict :
    rat (fst L) · distance <ℝ
    rat (fst L) · rat (fst ε)
  scaledDistanceStrict =
    mulPres<PosL
      distance (rat (fst ε)) (rat (fst L))
      (<ℚ→<ℝ 0 (fst L) (snd L))
      distance<ε

  outputDifferenceBeforeRadiusPath :
    absℝ
      (evaluatePolynomial coefficients x
        - evaluatePolynomial coefficients y)
      <ℝ
    rat (fst L) · rat (fst ε)
  outputDifferenceBeforeRadiusPath =
    ≤<ℝ-trans
      (absℝ
        (evaluatePolynomial coefficients x
          - evaluatePolynomial coefficients y))
      (polynomialLipschitzMajorant coefficients (rat (fst B))
        · distance)
      (rat (fst L) · rat (fst ε))
      hornerBound
      (≤<ℝ-trans
        (polynomialLipschitzMajorant coefficients (rat (fst B))
          · distance)
        (rat (fst L) · distance)
        (rat (fst L) · rat (fst ε))
        rationalMajorantBound
        scaledDistanceStrict)

  outputDifferenceStrict :
    absℝ
      (evaluatePolynomial coefficients x
        - evaluatePolynomial coefficients y)
      <ℝ
    rat (fst (L ·₊ ε))
  outputDifferenceStrict =
    subst
      (absℝ
        (evaluatePolynomial coefficients x
          - evaluatePolynomial coefficients y)
        <ℝ_)
      (mul-rat (fst L) (fst ε))
      outputDifferenceBeforeRadiusPath
