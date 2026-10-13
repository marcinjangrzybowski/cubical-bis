module Cubical.Analysis.Real.Functions.SquareRoot.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
private
  module Algebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)

    squareExpansion : ∀ x y → (x + y) · (x + y) ≡
      (x · x + y · y) + (x · y + x · y)
    squareExpansion x y = solve! R

    addSubtract : ∀ x y → (x + y) - x ≡ y
    addSubtract x y = solve! R


open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Functions.SquareRoot.Order

open Algebra ℝCommRing using (squareExpansion; addSubtract)

squareSumBound : ∀ x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y →
  x · x + y · y ≤ℝ (x + y) · (x + y)
squareSumBound x y xp yp = subst2 _≤ℝ_ (addIdR (x · x + y · y))
  (sym (squareExpansion x y))
  (addPres≤L 0ℝ (x · y + x · y) (x · x + y · y)
    (isNonnegative→0≤ (x · y + x · y)
      (addPresIsNonnegative (x · y) (x · y) xy xy)))
  where
  xy : IsNonnegative (x · y)
  xy = mulPresIsNonnegative x y (0≤→isNonnegative x xp) (0≤→isNonnegative y yp)

-- The square root is uniformly Holder continuous, including at zero.
-- This one-sided estimate suffices for the decreasing approximants below.
nonnegativeSquareDifferenceBound : ∀ u v r →
  0ℝ ≤ℝ v → v ≤ℝ u → 0ℝ ≤ℝ r →
  u · u ≤ℝ v · v + r · r → absℝ (v - u) ≤ℝ r
nonnegativeSquareDifferenceBound u v r vp ordered rp squares =
  subst (_≤ℝ r) (sym (absSubComm v u ∙ absOfNonnegative (u - v)
    (nonnegativeSub v u ordered)))
    (subst (u - v ≤ℝ_) (addSubtract v r)
      (addPres≤R u (v + r) (- v)
        (squareReflects≤Nonnegative u (v + r)
          (isNonnegative→0≤ (v + r)
            (addPresIsNonnegative v r (0≤→isNonnegative v vp) (0≤→isNonnegative r rp)))
          (≤ℝ-trans (u · u) (v · v + r · r) ((v + r) · (v + r))
            squares (squareSumBound v r vp rp)))))
