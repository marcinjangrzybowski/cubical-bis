module Cubical.HITs.CauchyRealsP.Algebra.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.MultiplicationLaws

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties

open PremetricTheory ℝPremetricSpace
  using (isCauchySeq)

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

-- Coefficients are stored in increasing degree order.  Thus
-- `a ∷ b ∷ []` denotes `a + b · x`.
evaluatePolynomial : List ℝ → ℝ → ℝ
evaluatePolynomial [] x =
  0
evaluatePolynomial (a ∷ coefficients) x =
  a + x · evaluatePolynomial coefficients x

evaluatePolynomialℚ : List ℚ → ℚ → ℚ
evaluatePolynomialℚ [] x =
  0
evaluatePolynomialℚ (a ∷ coefficients) x =
  a ℚ.+ x ℚ.· evaluatePolynomialℚ coefficients x

evaluatePolynomial-rat : ∀ coefficients x →
  evaluatePolynomial (map rat coefficients) (rat x) ≡
  rat (evaluatePolynomialℚ coefficients x)
evaluatePolynomial-rat [] x =
  refl
evaluatePolynomial-rat (a ∷ coefficients) x =
  cong
    (λ tail → rat a + rat x · tail)
    (evaluatePolynomial-rat coefficients x)
  ∙ cong (rat a +_)
      (mul-rat x (evaluatePolynomialℚ coefficients x))
  ∙ rat+rat
      a (x ℚ.· evaluatePolynomialℚ coefficients x)

private
  identityIsContinuous :
    isContinuous
      (snd ℝPremetricSpace) (idfun ℝ)
      (snd ℝPremetricSpace)
  identityIsContinuous =
    snd (CategoryStructures.idᶜ {M = ℝPremetricSpace})

evaluatePolynomialOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (x : A → ℝ) →
  isContinuous source x
    (snd ℝPremetricSpace) →
  ∀ coefficients →
  isContinuous source
    (λ point →
      evaluatePolynomial coefficients (x point))
    (snd ℝPremetricSpace)
evaluatePolynomialOfContinuousIsContinuous
  source x x-continuous [] point
  .IsContinuousAt.pres≈ ε =
    return
      ( 1
      , λ _ _ → refl∼ 0 ε
      )
evaluatePolynomialOfContinuousIsContinuous
  source x x-continuous
  (a ∷ coefficients) =
    addOfContinuousIsContinuous
      source
      (λ _ → a)
      (λ point →
        x point
          · evaluatePolynomial
              coefficients (x point))
      constant-continuous
      (mulOfContinuousIsContinuous
        source
        x
        (λ point →
          evaluatePolynomial
            coefficients (x point))
        x-continuous
        (evaluatePolynomialOfContinuousIsContinuous
          source x x-continuous coefficients))
  where
  constant-continuous :
    isContinuous source (λ _ → a)
      (snd ℝPremetricSpace)
  constant-continuous point
    .IsContinuousAt.pres≈ ε =
      return
        ( 1
        , λ _ _ → refl∼ a ε
        )

evaluatePolynomialIsContinuous : ∀ coefficients →
  isContinuous
    (snd ℝPremetricSpace)
    (evaluatePolynomial coefficients)
    (snd ℝPremetricSpace)
evaluatePolynomialIsContinuous [] =
  evaluatePolynomialOfContinuousIsContinuous
    (snd ℝPremetricSpace)
    (idfun ℝ) identityIsContinuous []
evaluatePolynomialIsContinuous (a ∷ coefficients) =
  evaluatePolynomialOfContinuousIsContinuous
    (snd ℝPremetricSpace)
    (idfun ℝ) identityIsContinuous
    (a ∷ coefficients)

polynomialMajorant : List ℝ → ℝ → ℝ
polynomialMajorant coefficients radius =
  evaluatePolynomial (map absℝ coefficients) radius

private
  addNonnegative : ∀ x y →
    0 ≤ℝ x → 0 ≤ℝ y →
    0 ≤ℝ x + y
  addNonnegative x y 0≤x 0≤y =
    subst (_≤ℝ (x + y))
      (addIdL 0)
      (≤ℝ-add 0 x 0 y 0≤x 0≤y)

polynomialMajorantNonnegative : ∀ coefficients radius →
  0 ≤ℝ radius →
  0 ≤ℝ polynomialMajorant coefficients radius
polynomialMajorantNonnegative [] radius 0≤radius =
  ≤ℝ-refl 0
polynomialMajorantNonnegative (a ∷ coefficients) radius 0≤radius =
  addNonnegative
    (absℝ a)
    (radius · polynomialMajorant coefficients radius)
    (absNonnegative a)
    (mulNonnegative
      radius (polynomialMajorant coefficients radius)
      0≤radius
      (polynomialMajorantNonnegative
        coefficients radius 0≤radius))

evaluatePolynomialAbsBound : ∀ coefficients x →
  absℝ (evaluatePolynomial coefficients x) ≤ℝ
  polynomialMajorant coefficients (absℝ x)
evaluatePolynomialAbsBound [] x =
  subst (_≤ℝ 0) (sym absZero) (≤ℝ-refl 0)
evaluatePolynomialAbsBound (a ∷ coefficients) x =
  ≤ℝ-trans
    (absℝ
      (a + x · evaluatePolynomial coefficients x))
    (absℝ a
      + absℝ (x · evaluatePolynomial coefficients x))
    (absℝ a
      + absℝ x · polynomialMajorant coefficients (absℝ x))
    (absTriangle a (x · evaluatePolynomial coefficients x))
    (subst
      (λ productAbs →
        absℝ a + productAbs ≤ℝ
        absℝ a
          + absℝ x · polynomialMajorant coefficients (absℝ x))
      (sym (absMul x (evaluatePolynomial coefficients x)))
      (≤ℝ-add
        (absℝ a) (absℝ a)
        (absℝ x · absℝ (evaluatePolynomial coefficients x))
        (absℝ x · polynomialMajorant coefficients (absℝ x))
        (≤ℝ-refl (absℝ a))
        (mulMonoL≤
          (absℝ (evaluatePolynomial coefficients x))
          (polynomialMajorant coefficients (absℝ x))
          (absℝ x)
          (absNonnegative x)
          (evaluatePolynomialAbsBound coefficients x))))

polynomialMajorantMono :
  ∀ coefficients x y →
  0 ≤ℝ x →
  x ≤ℝ y →
  polynomialMajorant coefficients x ≤ℝ
  polynomialMajorant coefficients y
polynomialMajorantMono
  [] x y 0≤x x≤y =
    ≤ℝ-refl 0
polynomialMajorantMono
  (a ∷ coefficients) x y 0≤x x≤y =
    ≤ℝ-add
      (absℝ a) (absℝ a)
      (x · polynomialMajorant coefficients x)
      (y · polynomialMajorant coefficients y)
      (≤ℝ-refl (absℝ a))
      (mulMono≤
        x y
        (polynomialMajorant coefficients x)
        (polynomialMajorant coefficients y)
        (≤ℝ-trans 0 x y 0≤x x≤y)
        (polynomialMajorantNonnegative
          coefficients x 0≤x)
        x≤y
        (polynomialMajorantMono
          coefficients x y 0≤x x≤y))

polynomialLipschitzMajorant : List ℝ → ℝ → ℝ
polynomialLipschitzMajorant [] radius =
  0
polynomialLipschitzMajorant
  (a ∷ coefficients) radius =
    polynomialMajorant coefficients radius
    + radius
      · polynomialLipschitzMajorant
          coefficients radius

polynomialLipschitzMajorantNonnegative :
  ∀ coefficients radius →
  0 ≤ℝ radius →
  0 ≤ℝ
    polynomialLipschitzMajorant
      coefficients radius
polynomialLipschitzMajorantNonnegative
  [] radius 0≤radius =
    ≤ℝ-refl 0
polynomialLipschitzMajorantNonnegative
  (a ∷ coefficients) radius 0≤radius =
    addNonnegative
      (polynomialMajorant coefficients radius)
      (radius
        · polynomialLipschitzMajorant
            coefficients radius)
      (polynomialMajorantNonnegative
        coefficients radius 0≤radius)
      (mulNonnegative
        radius
        (polynomialLipschitzMajorant
          coefficients radius)
        0≤radius
        (polynomialLipschitzMajorantNonnegative
          coefficients radius 0≤radius))

private
  hornerDifferencePath :
    ∀ a x y p q →
    (a + x · p) - (a + y · q) ≡
    (x - y) · p + y · (p - q)
  hornerDifferencePath a x y p q =
    sym
      (ℝRing.translatedDifference
        a (x · p) (y · q))
    ∙ productDifferencePath
    where
    xp : ℝ
    xp =
      x · p

    yp : ℝ
    yp =
      y · p

    yq : ℝ
    yq =
      y · q

    productDifferencePath :
      xp - yq ≡
      (x - y) · p + y · (p - q)
    productDifferencePath =
      cong (xp +_)
        (sym (addIdL (- yq)))
      ∙ cong (λ z → xp + (z + (- yq)))
          (sym (addInvL yp))
      ∙ addAssoc xp ((- yp) + yp) (- yq)
      ∙ cong (_+ (- yq))
          (addAssoc xp (- yp) yp)
      ∙ sym
          (addAssoc
            (xp + (- yp)) yp (- yq))
      ∙ cong₂ _+_
          (sym (ℝRing.·DistL- x y p))
          (sym (ℝRing.·DistR- y p q))

evaluatePolynomialLipschitzBound :
  ∀ coefficients radius x y →
  0 ≤ℝ radius →
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
      (sym
        (cong absℝ (subSelf 0)
        ∙ absZero))
      (sym
        (mulZeroL (absℝ (x - y))))
      (≤ℝ-refl 0)
evaluatePolynomialLipschitzBound
  (a ∷ coefficients) radius x y
  0≤radius absx≤radius absy≤radius =
    subst
      (λ difference →
        absℝ difference ≤ℝ
        lipschitz · distance)
      (sym
        (hornerDifferencePath
          a x y tail-x tail-y))
      decompositionBound
  where
  tail-x : ℝ
  tail-x =
    evaluatePolynomial coefficients x

  tail-y : ℝ
  tail-y =
    evaluatePolynomial coefficients y

  majorant : ℝ
  majorant =
    polynomialMajorant coefficients radius

  tail-lipschitz : ℝ
  tail-lipschitz =
    polynomialLipschitzMajorant
      coefficients radius

  lipschitz : ℝ
  lipschitz =
    majorant + radius · tail-lipschitz

  distance : ℝ
  distance =
    absℝ (x - y)

  firstTermBound :
    absℝ ((x - y) · tail-x) ≤ℝ
    majorant · distance
  firstTermBound =
    subst
      (_≤ℝ majorant · distance)
      (sym
        (absMul (x - y) tail-x
        ∙ mulComm distance (absℝ tail-x)))
      (mulMonoR≤
        (absℝ tail-x) majorant
        distance
        (absNonnegative (x - y))
        (≤ℝ-trans
          (absℝ tail-x)
          (polynomialMajorant
            coefficients (absℝ x))
          majorant
          (evaluatePolynomialAbsBound
            coefficients x)
          (polynomialMajorantMono
            coefficients
            (absℝ x) radius
            (absNonnegative x)
            absx≤radius)))

  secondTermBound :
    absℝ (y · (tail-x - tail-y)) ≤ℝ
    radius · (tail-lipschitz · distance)
  secondTermBound =
    subst
      (_≤ℝ radius · (tail-lipschitz · distance))
      (sym (absMul y (tail-x - tail-y)))
      (mulMono≤
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
      + radius · (tail-lipschitz · distance) ≡
    lipschitz · distance
  sumBoundsPath =
    cong
      (majorant · distance +_)
      (sym
        (mulAssoc
          radius tail-lipschitz distance))
    ∙ sym
        (mulDistL
          majorant
          (radius · tail-lipschitz)
          distance)

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
      (≤ℝ-add
        (absℝ ((x - y) · tail-x))
        (majorant · distance)
        (absℝ (y · (tail-x - tail-y)))
        (radius · (tail-lipschitz · distance))
        firstTermBound secondTermBound)

  decompositionBound :
    absℝ
      ((x - y) · tail-x
        + y · (tail-x - tail-y))
      ≤ℝ
    lipschitz · distance
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
  ∀ coefficients B L →
  polynomialLipschitzMajorant
      coefficients (rat (fst B))
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
  distance =
    absℝ (x - y)

  distance<ε :
    distance <ℝ rat (fst ε)
  distance<ε =
    closeness→absDifference<
      x y ε x∼y

  radiusNonnegative :
    0 ≤ℝ rat (fst B)
  radiusNonnegative =
    <ℝ-weaken 0 (rat (fst B))
      (<ℚ→<ℝ 0 (fst B) (snd B))

  hornerBound :
    absℝ
      (evaluatePolynomial coefficients x
        - evaluatePolynomial coefficients y)
      ≤ℝ
    polynomialLipschitzMajorant
        coefficients (rat (fst B))
      · distance
  hornerBound =
    evaluatePolynomialLipschitzBound
      coefficients (rat (fst B)) x y
      radiusNonnegative absx≤B absy≤B

  rationalMajorantBound :
    polynomialLipschitzMajorant
        coefficients (rat (fst B))
      · distance
      ≤ℝ
    rat (fst L) · distance
  rationalMajorantBound =
    mulMonoR≤
      (polynomialLipschitzMajorant
        coefficients (rat (fst B)))
      (rat (fst L))
      distance
      (absNonnegative (x - y))
      majorant≤L

  scaledDistanceStrict :
    rat (fst L) · distance
      <ℝ
    rat (fst L) · rat (fst ε)
  scaledDistanceStrict =
    mulMonoL<
      distance (rat (fst ε))
      (rat (fst L))
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
      (polynomialLipschitzMajorant
        coefficients (rat (fst B))
        · distance)
      (rat (fst L) · rat (fst ε))
      hornerBound
      (≤<ℝ-trans
        (polynomialLipschitzMajorant
          coefficients (rat (fst B))
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

polynomialPresIsCauchySeqOnRationalBall :
  ∀ coefficients B L →
  polynomialLipschitzMajorant
      coefficients (rat (fst B))
    ≤ℝ rat (fst L) →
  ∀ x →
  (∀ n → absℝ (x n) ≤ℝ rat (fst B)) →
  isCauchySeq x →
  isCauchySeq
    (evaluatePolynomial coefficients ∘ x)
polynomialPresIsCauchySeqOnRationalBall
  coefficients B L majorant≤L
  x x-bounded x-cauchy .fst ε =
    fst x-cauchy (ε ₊／₊ L)
polynomialPresIsCauchySeqOnRationalBall
  coefficients B L majorant≤L
  x x-bounded x-cauchy .snd
  ε m n modulus≤m modulus≤n =
    subst∼
      (evaluatePolynomial coefficients (x m))
      (evaluatePolynomial coefficients (x n))
      {ε = L ·₊ (ε ₊／₊ L)}
      {ε' = ε}
      (·／ L ε)
      (evaluatePolynomialLipschitzOnRationalBall
        coefficients B L majorant≤L
        (x m) (x n)
        (x-bounded m) (x-bounded n)
        (ε ₊／₊ L)
        (snd x-cauchy
          (ε ₊／₊ L)
          m n modulus≤m modulus≤n))
