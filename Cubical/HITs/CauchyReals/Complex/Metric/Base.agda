module Cubical.HITs.CauchyReals.Complex.Metric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using
  (x<δ→x≤0)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Zero
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


infix 4 _≈ℂ[_]_


_≈ℂ[_]_ : ℂ → ℚ₊ → ℂ → Type
z ≈ℂ[ ε ] w = modulus (z -ℂ w) <ᵣ rat (fst ε)


opaque
  self-difference-zero : ∀ z → z -ℂ z ≡ 0ℂ
  self-difference-zero _ = ℂ≡ ℝ! ℝ!


opaque
  modulus-self-difference : ∀ z → modulus (z -ℂ z) ≡ 0
  modulus-self-difference z =
    cong modulus (self-difference-zero z) ∙ modulus0


opaque
  difference-sym-path : ∀ z w → z -ℂ w ≡ -ℂ (w -ℂ z)
  difference-sym-path _ _ = ℂ≡ ℝ! ℝ!


opaque
  modulus-difference-sym : ∀ z w →
    modulus (z -ℂ w) ≡ modulus (w -ℂ z)
  modulus-difference-sym z w =
    cong modulus (difference-sym-path z w) ∙ modulus-neg (w -ℂ z)


opaque
  difference-via : ∀ z w u →
    z -ℂ u ≡ (z -ℂ w) +ℂ (w -ℂ u)
  difference-via _ _ _ = ℂ≡ ℝ! ℝ!


opaque
  modulus-difference-triangle : ∀ z w u →
    modulus (z -ℂ u) ≤ᵣ
    modulus (z -ℂ w) +ᵣ modulus (w -ℂ u)
  modulus-difference-triangle z w u =
    isTrans≡≤ᵣ _ _ _
      (cong modulus (difference-via z w u))
      (modulus-triangle (z -ℂ w) (w -ℂ u))


opaque
  realDifferenceZero→equal : ∀ x y → x -ᵣ y ≡ 0 → x ≡ y
  realDifferenceZero→equal x y x-y≡0 =
    sym (Rℝ.minusPlus x y)
    ∙ cong (_+ᵣ y) x-y≡0
    ∙ Rℝ.+IdL y


opaque
  differenceZero→equal : ∀ z w → z -ℂ w ≡ 0ℂ → z ≡ w
  differenceZero→equal z w z-w≡0 = ℂ≡
    (realDifferenceZero→equal (re z) (re w) (cong re z-w≡0))
    (realDifferenceZero→equal (im z) (im w) (cong im z-w≡0))


opaque
  allClose→modulusDifferenceZero : ∀ z w →
    ((ε : ℚ₊) → z ≈ℂ[ ε ] w) → modulus (z -ℂ w) ≡ 0
  allClose→modulusDifferenceZero z w allClose =
    isAntisym≤ᵣ (modulus (z -ℂ w)) 0
      (x<δ→x≤0 (modulus (z -ℂ w)) allClose)
      (modulusNonNeg (z -ℂ w))


opaque
  allClose→equal : ∀ z w →
    ((ε : ℚ₊) → z ≈ℂ[ ε ] w) → z ≡ w
  allClose→equal z w allClose = differenceZero→equal z w
    (modulusZero→zero (z -ℂ w)
      (allClose→modulusDifferenceZero z w allClose))


opaque
  complexCloseTriangle : ∀ z w u ε δ →
    z ≈ℂ[ ε ] w → w ≈ℂ[ δ ] u → z ≈ℂ[ ε +₊ δ ] u
  complexCloseTriangle z w u ε δ z≈w w≈u =
    isTrans≤<ᵣ _ _ _
      (modulus-difference-triangle z w u)
      (subst
        (modulus (z -ℂ w) +ᵣ modulus (w -ℂ u) <ᵣ_)
        (+ᵣ-rat (fst ε) (fst δ))
        (<ᵣMonotone+ᵣ _ _ _ _ z≈w w≈u))


opaque
  complexCloseRounded : ∀ z w ε → z ≈ℂ[ ε ] w →
    ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (z ≈ℂ[ δ ] w)
  complexCloseRounded z w ε z≈w =
    PT.map
      (λ (q , |z-w|<q , q<ε) →
        let 0<q = isTrans≤<ᵣ 0 (modulus (z -ℂ w)) (rat q)
              (modulusNonNeg (z -ℂ w)) |z-w|<q
            q₊ : ℚ₊
            q₊ = q , <ᵣ→<ℚ 0 q 0<q
        in q₊ , <ᵣ→<ℚ q (fst ε) q<ε , |z-w|<q)
      (denseℚinℝ (modulus (z -ℂ w)) (rat (fst ε)) z≈w)


isPremetricℂ : IsPremetric _≈ℂ[_]_
isPremetricℂ .IsPremetric.isSetM = isSetℂ
isPremetricℂ .IsPremetric.isProp≈ z w ε = isProp<ᵣ _ _
isPremetricℂ .IsPremetric.isRefl≈ z ε =
  subst (_<ᵣ rat (fst ε)) (sym (modulus-self-difference z))
    (<ℚ→<ᵣ 0 (fst ε) (snd ε))
isPremetricℂ .IsPremetric.isSym≈ z w ε z≈w =
  subst (_<ᵣ rat (fst ε)) (modulus-difference-sym z w) z≈w
isPremetricℂ .IsPremetric.isSeparated≈ z w allClose =
  allClose→equal z w allClose
isPremetricℂ .IsPremetric.isTriangular≈ z w u ε δ z≈w w≈u =
  complexCloseTriangle z w u ε δ z≈w w≈u
isPremetricℂ .IsPremetric.isRounded≈ z w ε z≈w =
  complexCloseRounded z w ε z≈w


ℂPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℂPremetricSpace = premetricspace ℂ _≈ℂ[_]_ isPremetricℂ
