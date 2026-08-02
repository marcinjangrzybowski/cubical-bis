module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.CommonBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Archimedean
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.BoundedLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base

-- Standard output bounds used when transferring bounded algebraic laws to the
-- total multiplication.  Keeping these constructions separate from any one
-- law makes the witness bookkeeping reusable.

expandedBound : ℚ₊ → ℚ₊
expandedBound B = ℚ.maxWithPos B (boundedSquare B)

bound≤Expanded : ∀ B →
  fst B ℚ.≤ fst (expandedBound B)
bound≤Expanded B =
  ℚ.≤max (fst B) (boundedSquare B)

square≤Expanded : ∀ B →
  boundedSquare B ℚ.≤ fst (expandedBound B)
square≤Expanded B =
  ℚ.≤max' (fst B) (boundedSquare B)

doubledBound : ℚ₊ → ℚ₊
doubledBound B = B +₊ B

bound≤Doubled : ∀ B →
  fst B ℚ.≤ fst (doubledBound B)
bound≤Doubled B =
  subst
    (ℚ._≤ (fst B ℚ.+ fst B))
    (ℚ.+IdR (fst B))
    (ℚ.≤Monotone+
      (fst B) (fst B) 0 (fst B)
      (ℚ.isRefl≤ (fst B))
      (ℚ.0≤ℚ₊ B))

TripleNaturalAbsBounds : ℝ → ℝ → ℝ → Type
TripleNaturalAbsBounds x y z =
  JointNaturalAbsBounds x y × NaturalAbsBound z

tripleNaturalAbsBounds : ∀ (x y z : ℝ) →
  ∥ TripleNaturalAbsBounds x y z ∥₁
tripleNaturalAbsBounds x y z =
  PT.map2 _,_
    (jointNaturalAbsBounds x y)
    (∃naturalAbsBound z)

tripleBound : ∀ {x y z : ℝ} →
  TripleNaturalAbsBounds x y z → ℚ₊
tripleBound {x} {y} {z} w =
  ℚ.maxWithPos
    (jointBound {x = x} {y = y} (fst w))
    (naturalRational (fst (snd w)))

tripleBoundContains₁ : ∀ {x y z : ℝ}
  (w : TripleNaturalAbsBounds x y z) →
  absℝ x ≤ℝ
  rat (fst (tripleBound {x = x} {y = y} {z = z} w))
tripleBoundContains₁ {x} {y} {z} w =
  ≤ℝ-trans
    (absℝ x) (rat (fst pairB)) (rat (fst B))
    absx≤pairB
    (≤ℚ→≤ℝ (fst pairB) (fst B)
      (ℚ.≤max (fst pairB) (naturalRational n)))
  where
  pairWitness : JointNaturalAbsBounds x y
  pairWitness = fst w

  zWitness : NaturalAbsBound z
  zWitness = snd w

  pairB : ℚ₊
  pairB = jointBound {x = x} {y = y} pairWitness

  n : ℕ₊₁
  n = fst zWitness

  B : ℚ₊
  B = tripleBound {x = x} {y = y} {z = z} w

  absx≤pairB : absℝ x ≤ℝ rat (fst pairB)
  absx≤pairB =
    jointBoundContainsLeft {x = x} {y = y} pairWitness

tripleBoundContains₂ : ∀ {x y z : ℝ}
  (w : TripleNaturalAbsBounds x y z) →
  absℝ y ≤ℝ
  rat (fst (tripleBound {x = x} {y = y} {z = z} w))
tripleBoundContains₂ {x} {y} {z} w =
  ≤ℝ-trans
    (absℝ y) (rat (fst pairB)) (rat (fst B))
    absy≤pairB
    (≤ℚ→≤ℝ (fst pairB) (fst B)
      (ℚ.≤max (fst pairB) (naturalRational n)))
  where
  pairWitness : JointNaturalAbsBounds x y
  pairWitness = fst w

  zWitness : NaturalAbsBound z
  zWitness = snd w

  pairB : ℚ₊
  pairB = jointBound {x = x} {y = y} pairWitness

  n : ℕ₊₁
  n = fst zWitness

  B : ℚ₊
  B = tripleBound {x = x} {y = y} {z = z} w

  absy≤pairB : absℝ y ≤ℝ rat (fst pairB)
  absy≤pairB =
    jointBoundContainsRight {x = x} {y = y} pairWitness

tripleBoundContains₃ : ∀ {x y z : ℝ}
  (w : TripleNaturalAbsBounds x y z) →
  absℝ z ≤ℝ
  rat (fst (tripleBound {x = x} {y = y} {z = z} w))
tripleBoundContains₃ {x} {y} {z} w =
  ≤ℝ-trans
    (absℝ z) (rat (naturalRational n)) (rat (fst B))
    (<ℝ-weaken
      (absℝ z) (rat (naturalRational n))
      zAbs<n)
    (≤ℚ→≤ℝ (naturalRational n) (fst B)
      (ℚ.≤max' (fst pairB) (naturalRational n)))
  where
  pairWitness : JointNaturalAbsBounds x y
  pairWitness = fst w

  zWitness : NaturalAbsBound z
  zWitness = snd w

  pairB : ℚ₊
  pairB = jointBound {x = x} {y = y} pairWitness

  n : ℕ₊₁
  n = fst zWitness

  B : ℚ₊
  B = tripleBound {x = x} {y = y} {z = z} w

  zAbs<n : absℝ z <ℝ rat (naturalRational n)
  zAbs<n = snd zWitness
