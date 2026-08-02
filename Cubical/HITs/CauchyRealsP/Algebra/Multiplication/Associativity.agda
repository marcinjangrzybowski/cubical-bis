module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Associativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Archimedean
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.BoundedLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.CommonBounds
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Laws

open import Cubical.Relation.Premetric.Mappings

private
  assocLeft : ℚ₊ → ℚ₊ → ℝ → ℝ → ℝ → ℝ
  assocLeft B C x y z =
    boundedMulℝ C
      (boundedMulℝ B x y)
      (clampℝ B z)

  assocRight : ℚ₊ → ℚ₊ → ℝ → ℝ → ℝ → ℝ
  assocRight B C x y z =
    boundedMulℝ C
      (clampℝ B x)
      (boundedMulℝ B y z)

  assocLeftLip₁ : ∀ B C y z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → assocLeft B C x y z)
      (snd ℝPremetricSpace) (C ·₊ B)
  assocLeftLip₁ B C y z =
    composeRealLipschitzWith
      (λ u → boundedMulℝ C u (clampℝ B z))
      (λ x → boundedMulℝ B x y)
      C B
      (boundedMulIsLipschitz₁At C (clampℝ B z))
      (boundedMulIsLipschitz₁At B y)

  assocLeftLip₂ : ∀ B C x z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ y → assocLeft B C x y z)
      (snd ℝPremetricSpace) (C ·₊ B)
  assocLeftLip₂ B C x z =
    composeRealLipschitzWith
      (λ u → boundedMulℝ C u (clampℝ B z))
      (boundedMulℝ B x)
      C B
      (boundedMulIsLipschitz₁At C (clampℝ B z))
      (boundedMulIsLipschitz₂ B x)

  assocLeftLip₃ : ∀ B C x y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (assocLeft B C x y)
      (snd ℝPremetricSpace) C
  assocLeftLip₃ B C x y
    .IsLipschitzWith.pres≈ z z' ε z∼z' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₂ C (boundedMulℝ B x y))
        (clampℝ B z) (clampℝ B z') ε
        (clampPres∼ B z z' ε z∼z')

  assocRightLip₁ : ∀ B C y z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → assocRight B C x y z)
      (snd ℝPremetricSpace) C
  assocRightLip₁ B C y z
    .IsLipschitzWith.pres≈ x x' ε x∼x' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₁At C (boundedMulℝ B y z))
        (clampℝ B x) (clampℝ B x') ε
        (clampPres∼ B x x' ε x∼x')

  assocRightLip₂ : ∀ B C x z →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ y → assocRight B C x y z)
      (snd ℝPremetricSpace) (C ·₊ B)
  assocRightLip₂ B C x z =
    composeRealLipschitzWith
      (boundedMulℝ C (clampℝ B x))
      (λ y → boundedMulℝ B y z)
      C B
      (boundedMulIsLipschitz₂ C (clampℝ B x))
      (boundedMulIsLipschitz₁At B z)

  assocRightLip₃ : ∀ B C x y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (assocRight B C x y)
      (snd ℝPremetricSpace) (C ·₊ B)
  assocRightLip₃ B C x y =
    composeRealLipschitzWith
      (boundedMulℝ C (clampℝ B x))
      (boundedMulℝ B y)
      C B
      (boundedMulIsLipschitz₂ C (clampℝ B x))
      (boundedMulIsLipschitz₂ B y)

  assocLeft-rat : ∀ B C →
    fst B ℚ.≤ fst C →
    boundedSquare B ℚ.≤ fst C →
    ∀ p q r →
    assocLeft B C (rat p) (rat q) (rat r) ≡
    rat
      (boundedMulℚ B p q ℚ.· clampAt B r)
  assocLeft-rat B C B≤C square≤C p q r =
    cong₂ (boundedMulℝ C)
      (boundedMul-rat B p q)
      (clamp-rat B r)
    ∙ boundedMul-rat-within C
        (boundedMulℚ B p q) (clampAt B r)
        (fst productInterval) (snd productInterval)
        (fst rInterval) (snd rInterval)
    where
    productAbs≤C :
      abs (boundedMulℚ B p q) ℚ.≤ fst C
    productAbs≤C =
      ℚ.isTrans≤
        (abs (boundedMulℚ B p q))
        (boundedSquare B) (fst C)
        (clampedProductAbs≤Square B p q)
        square≤C

    productInterval =
      rationalAbsBound→Interval C
        (boundedMulℚ B p q) productAbs≤C

    rAbs≤C : abs (clampAt B r) ℚ.≤ fst C
    rAbs≤C =
      ℚ.isTrans≤
        (abs (clampAt B r)) (fst B) (fst C)
        (clampAtAbs≤ B r) B≤C

    rInterval =
      rationalAbsBound→Interval C (clampAt B r) rAbs≤C

  assocRight-rat : ∀ B C →
    fst B ℚ.≤ fst C →
    boundedSquare B ℚ.≤ fst C →
    ∀ p q r →
    assocRight B C (rat p) (rat q) (rat r) ≡
    rat
      (clampAt B p ℚ.· boundedMulℚ B q r)
  assocRight-rat B C B≤C square≤C p q r =
    cong₂ (boundedMulℝ C)
      (clamp-rat B p)
      (boundedMul-rat B q r)
    ∙ boundedMul-rat-within C
        (clampAt B p) (boundedMulℚ B q r)
        (fst pInterval) (snd pInterval)
        (fst productInterval) (snd productInterval)
    where
    pAbs≤C : abs (clampAt B p) ℚ.≤ fst C
    pAbs≤C =
      ℚ.isTrans≤
        (abs (clampAt B p)) (fst B) (fst C)
        (clampAtAbs≤ B p) B≤C

    pInterval =
      rationalAbsBound→Interval C (clampAt B p) pAbs≤C

    productAbs≤C :
      abs (boundedMulℚ B q r) ℚ.≤ fst C
    productAbs≤C =
      ℚ.isTrans≤
        (abs (boundedMulℚ B q r))
        (boundedSquare B) (fst C)
        (clampedProductAbs≤Square B q r)
        square≤C

    productInterval =
      rationalAbsBound→Interval C
        (boundedMulℚ B q r) productAbs≤C

boundedMulAssocClamped : ∀ B C →
  fst B ℚ.≤ fst C →
  boundedSquare B ℚ.≤ fst C →
  ∀ x y z →
  boundedMulℝ C
    (boundedMulℝ B x y)
    (clampℝ B z)
  ≡
  boundedMulℝ C
    (clampℝ B x)
    (boundedMulℝ B y z)
boundedMulAssocClamped B C B≤C square≤C =
  lipschitzExtensionality₃
    (assocLeft B C) (assocRight B C)
    (λ y z → ∣ C ·₊ B , assocLeftLip₁ B C y z ∣₁)
    (λ x z → ∣ C ·₊ B , assocLeftLip₂ B C x z ∣₁)
    (λ x y → ∣ C , assocLeftLip₃ B C x y ∣₁)
    (λ y z → ∣ C , assocRightLip₁ B C y z ∣₁)
    (λ x z → ∣ C ·₊ B , assocRightLip₂ B C x z ∣₁)
    (λ x y → ∣ C ·₊ B , assocRightLip₃ B C x y ∣₁)
    λ p q r →
      assocLeft-rat B C B≤C square≤C p q r
      ∙ cong rat
          (sym (ℚ.·Assoc
            (clampAt B p)
            (clampAt B q)
            (clampAt B r)))
      ∙ sym (assocRight-rat B C B≤C square≤C p q r)

boundedMulAssocWithin : ∀ B C →
  fst B ℚ.≤ fst C →
  boundedSquare B ℚ.≤ fst C →
  ∀ x y z →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  absℝ z ≤ℝ rat (fst B) →
  boundedMulℝ C (boundedMulℝ B x y) z ≡
  boundedMulℝ C x (boundedMulℝ B y z)
boundedMulAssocWithin B C B≤C square≤C
  x y z absx≤B absy≤B absz≤B =
  sym
    (cong
      (boundedMulℝ C (boundedMulℝ B x y))
      (clampFixpointFromAbs B z absz≤B))
  ∙ boundedMulAssocClamped B C B≤C square≤C x y z
  ∙ cong
      (λ u → boundedMulℝ C u (boundedMulℝ B y z))
      (clampFixpointFromAbs B x absx≤B)

mulAssocAtTripleBound : ∀ (x y z : ℝ) →
  TripleNaturalAbsBounds x y z →
  (x · y) · z ≡ x · (y · z)
mulAssocAtTripleBound x y z w =
  multiplicationWithin C (x · y) z absxy≤C absz≤C
  ∙ cong (λ u → boundedMulℝ C u z)
      (multiplicationWithin B x y absx≤B absy≤B)
  ∙ boundedMulAssocWithin B C
      (bound≤Expanded B) (square≤Expanded B)
      x y z absx≤B absy≤B absz≤B
  ∙ sym
      (cong (boundedMulℝ C x)
        (multiplicationWithin B y z absy≤B absz≤B))
  ∙ sym
      (multiplicationWithin C x (y · z) absx≤C absyz≤C)
  where
  B : ℚ₊
  B = tripleBound {x = x} {y = y} {z = z} w

  C : ℚ₊
  C = expandedBound B

  absx≤B : absℝ x ≤ℝ rat (fst B)
  absx≤B =
    tripleBoundContains₁ {x = x} {y = y} {z = z} w

  absy≤B : absℝ y ≤ℝ rat (fst B)
  absy≤B =
    tripleBoundContains₂ {x = x} {y = y} {z = z} w

  absz≤B : absℝ z ≤ℝ rat (fst B)
  absz≤B =
    tripleBoundContains₃ {x = x} {y = y} {z = z} w

  B≤C-real : rat (fst B) ≤ℝ rat (fst C)
  B≤C-real =
    ≤ℚ→≤ℝ (fst B) (fst C) (bound≤Expanded B)

  square≤C-real :
    rat (boundedSquare B) ≤ℝ rat (fst C)
  square≤C-real =
    ≤ℚ→≤ℝ
      (boundedSquare B) (fst C) (square≤Expanded B)

  absx≤C : absℝ x ≤ℝ rat (fst C)
  absx≤C =
    ≤ℝ-trans
      (absℝ x) (rat (fst B)) (rat (fst C))
      absx≤B B≤C-real

  absz≤C : absℝ z ≤ℝ rat (fst C)
  absz≤C =
    ≤ℝ-trans
      (absℝ z) (rat (fst B)) (rat (fst C))
      absz≤B B≤C-real

  absxy≤C : absℝ (x · y) ≤ℝ rat (fst C)
  absxy≤C =
    ≤ℝ-trans
      (absℝ (x · y))
      (rat (boundedSquare B))
      (rat (fst C))
      (mulAbs≤AtBound B x y absx≤B absy≤B)
      square≤C-real

  absyz≤C : absℝ (y · z) ≤ℝ rat (fst C)
  absyz≤C =
    ≤ℝ-trans
      (absℝ (y · z))
      (rat (boundedSquare B))
      (rat (fst C))
      (mulAbs≤AtBound B y z absy≤B absz≤B)
      square≤C-real

mulAssoc : ∀ (x y z : ℝ) → (x · y) · z ≡ x · (y · z)
mulAssoc x y z =
  PT.rec
    (isSetℝ _ _)
    (mulAssocAtTripleBound x y z)
    (tripleNaturalAbsBounds x y z)
