module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.BoundedLaws where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded

open import Cubical.Relation.Premetric.Mappings

private
  constantZeroIsNonExpanding :
    IsNonExpanding
      (snd ℝPremetricSpace)
      (λ _ → 0)
      (snd ℝPremetricSpace)
  constantZeroIsNonExpanding
    .IsNonExpanding.pres≈ _ _ ε _ = refl∼ 0 ε

clampAtZero : ∀ B → clampAt B 0 ≡ 0
clampAtZero B =
  ℚ.inClamps
    (ℚ.- fst B) (fst B) 0
    (-ℚ₊≤0 B) (ℚ.0≤ℚ₊ B)

boundedMulZeroR : ∀ B x → boundedMulℝ B x 0 ≡ 0
boundedMulZeroR B =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      (λ x → boundedMulℝ B x 0)
      (λ _ → 0)
      ∣ B , boundedMulIsLipschitz₁At B 0 ∣₁
      (isNonExpanding→isLipschitz
        (snd ℝPremetricSpace) (λ _ → 0)
        (snd ℝPremetricSpace) constantZeroIsNonExpanding)
      λ q →
        boundedMul-rat B q 0
        ∙ cong rat
            (cong (clampAt B q ℚ.·_) (clampAtZero B)
            ∙ ℚ.·AnnihilR (clampAt B q)))

boundedMulZeroL : ∀ B x → boundedMulℝ B 0 x ≡ 0
boundedMulZeroL B x =
  boundedMulComm B 0 x
  ∙ boundedMulZeroR B x

clampAtOne : ∀ B →
  1 ℚ.≤ fst B →
  clampAt B 1 ≡ 1
clampAtOne B 1≤B =
  ℚ.inClamps
    (ℚ.- fst B) (fst B) 1
    (ℚ.isTrans≤
      (ℚ.- fst B) 0 1
      (-ℚ₊≤0 B)
      (ℚ.<Weaken≤ 0 1 (ℚ.0<pos 0 1)))
    1≤B

boundedMulOneR : ∀ B →
  1 ℚ.≤ fst B →
  ∀ x → boundedMulℝ B x 1 ≡ clampℝ B x
boundedMulOneR B 1≤B =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      (λ x → boundedMulℝ B x 1)
      (clampℝ B)
      ∣ B , boundedMulIsLipschitz₁At B 1 ∣₁
      (isNonExpanding→isLipschitz
        (snd ℝPremetricSpace) (clampℝ B)
        (snd ℝPremetricSpace) (clampIsNonExpanding B))
      λ q →
        boundedMul-rat B q 1
        ∙ cong rat
            (cong (clampAt B q ℚ.·_) (clampAtOne B 1≤B)
            ∙ ℚ.·IdR (clampAt B q))
        ∙ sym (clamp-rat B q))

boundedMulOneL : ∀ B →
  1 ℚ.≤ fst B →
  ∀ x → boundedMulℝ B 1 x ≡ clampℝ B x
boundedMulOneL B 1≤B x =
  boundedMulComm B 1 x
  ∙ boundedMulOneR B 1≤B x

boundedSquare : ℚ₊ → ℚ
boundedSquare B = fst B ℚ.· fst B

private
  boundedMulAbsMax : ℚ₊ → ℝ → ℝ → ℝ
  boundedMulAbsMax B x y =
    maxℝ
      (absℝ (boundedMulℝ B x y))
      (rat (boundedSquare B))

  boundedMulAbsMaxLip₁ : ∀ B y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → boundedMulAbsMax B x y)
      (snd ℝPremetricSpace) B
  boundedMulAbsMaxLip₁ B y
    .IsLipschitzWith.pres≈ x x' ε x∼x' =
      maxPres∼₁
        (absℝ (boundedMulℝ B x y))
        (absℝ (boundedMulℝ B x' y))
        (rat (boundedSquare B))
        (B ·₊ ε)
        (absPres∼
          (boundedMulℝ B x y)
          (boundedMulℝ B x' y)
          (B ·₊ ε)
          (IsLipschitzWith.pres≈
            (boundedMulIsLipschitz₁At B y)
            x x' ε x∼x'))

  boundedMulAbsMaxLip₂ : ∀ B x →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (boundedMulAbsMax B x)
      (snd ℝPremetricSpace) B
  boundedMulAbsMaxLip₂ B x
    .IsLipschitzWith.pres≈ y y' ε y∼y' =
      maxPres∼₁
        (absℝ (boundedMulℝ B x y))
        (absℝ (boundedMulℝ B x y'))
        (rat (boundedSquare B))
        (B ·₊ ε)
        (absPres∼
          (boundedMulℝ B x y)
          (boundedMulℝ B x y')
          (B ·₊ ε)
          (IsLipschitzWith.pres≈
            (boundedMulIsLipschitz₂ B x)
            y y' ε y∼y'))

  constantSquareIsNonExpanding : ∀ B →
    IsNonExpanding
      (snd ℝPremetricSpace)
      (λ _ → rat (boundedSquare B))
      (snd ℝPremetricSpace)
  constantSquareIsNonExpanding B
    .IsNonExpanding.pres≈ _ _ ε _ =
      refl∼ (rat (boundedSquare B)) ε

  boundedMulℚAbs≤Square : ∀ B q r →
    abs (boundedMulℚ B q r) ℚ.≤ boundedSquare B
  boundedMulℚAbs≤Square B q r =
    subst
      (ℚ._≤ boundedSquare B)
      (ℚ.abs·abs (clampAt B q) (clampAt B r))
      (ℚ.≤Monotone·-onNonNeg
        (abs (clampAt B q)) (fst B)
        (abs (clampAt B r)) (fst B)
        (clampAtAbs≤ B q)
        (clampAtAbs≤ B r)
        (OrderedCommRingTheory.0≤abs
          ℚOrderedCommRing (clampAt B q))
        (OrderedCommRingTheory.0≤abs
          ℚOrderedCommRing (clampAt B r)))

boundedMulAbsMaxPath : ∀ B x y →
  maxℝ
    (absℝ (boundedMulℝ B x y))
    (rat (boundedSquare B))
  ≡ rat (boundedSquare B)
boundedMulAbsMaxPath B =
  lipschitzExtensionality₂
    (boundedMulAbsMax B)
    (λ _ _ → rat (boundedSquare B))
    (λ y → ∣ B , boundedMulAbsMaxLip₁ B y ∣₁)
    (λ x → ∣ B , boundedMulAbsMaxLip₂ B x ∣₁)
    (λ _ →
      isNonExpanding→isLipschitz
        (snd ℝPremetricSpace)
        (λ _ → rat (boundedSquare B))
        (snd ℝPremetricSpace)
        (constantSquareIsNonExpanding B))
    (λ _ →
      isNonExpanding→isLipschitz
        (snd ℝPremetricSpace)
        (λ _ → rat (boundedSquare B))
        (snd ℝPremetricSpace)
        (constantSquareIsNonExpanding B))
    λ q r →
      cong
        (λ z → maxℝ (absℝ z) (rat (boundedSquare B)))
        (boundedMul-rat B q r)
      ∙ cong
          (λ z → maxℝ z (rat (boundedSquare B)))
          (abs-rat (boundedMulℚ B q r))
      ∙ max-rat (abs (boundedMulℚ B q r)) (boundedSquare B)
      ∙ cong rat
          (ℚ.≤→max
            (abs (boundedMulℚ B q r))
            (boundedSquare B)
            (boundedMulℚAbs≤Square B q r))

opaque
  unfolding _≤ℝ_

  boundedMulAbs≤Square : ∀ B x y →
    absℝ (boundedMulℝ B x y) ≤ℝ rat (boundedSquare B)
  boundedMulAbs≤Square = boundedMulAbsMaxPath

rationalAbsBound→Interval : ∀ (B : ℚ₊) (q : ℚ) →
  abs q ℚ.≤ fst B →
  (ℚ.- fst B ℚ.≤ q) × (q ℚ.≤ fst B)
rationalAbsBound→Interval B q absq≤B =
  subst
    (ℚ.- fst B ℚ.≤_)
    (ℚ.-Invol q)
    (ℚ.minus-≤
      (ℚ.- q) (fst B)
      (ℚ.isTrans≤
        (ℚ.- q) (abs q) (fst B)
        (OrderedCommRingTheory.-≤abs ℚOrderedCommRing q)
        absq≤B))
  , ℚ.isTrans≤
      q (abs q) (fst B)
      (OrderedCommRingTheory.≤abs ℚOrderedCommRing q)
      absq≤B

clampedProductAbs≤Square : ∀ (B : ℚ₊) (q r : ℚ) →
  abs (clampAt B q ℚ.· clampAt B r)
    ℚ.≤ boundedSquare B
clampedProductAbs≤Square = boundedMulℚAbs≤Square
