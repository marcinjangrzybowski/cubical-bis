module Cubical.Analysis.Real.Sequence.Squeeze where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Metric
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually

open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)


private
  LimitTail : (ℕ → ℝ) → ℝ → ℚ₊ → Type₀
  LimitTail x l ε =
    Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ∼[ ε ] l)


-- A point between two points that are ε/2-close to the same centre is
-- ε-close to that centre.  This order formulation is useful independently
-- of sequences (for interval and enclosure arguments, for example).
betweenCloseEndpoints : ∀ {x y z l} ε →
  x ≤ℝ y → y ≤ℝ z →
  x ∼[ ε /2₊ ] l → z ∼[ ε /2₊ ] l →
  y ∼[ ε ] l
betweenCloseEndpoints {x} {y} {z} {l} ε x≤y y≤z x∼l z∼l =
  absDifference<→closeness y l ε
    (≤<ℝ-trans
      (absℝ (y - l)) half (rat (fst ε))
      absoluteBound
      (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)))
  where
  half : ℝ
  half = rat (fst (ε /2₊))

  y≤l+half : y ≤ℝ l + half
  y≤l+half = ≤ℝ-trans y z (l + half) y≤z
    (close→upperBound z l (ε /2₊) z∼l)

  upperRightPath : (l + half) + (- l) ≡ half
  upperRightPath =
    cong (_+ (- l)) (addComm l half)
    ∙ sym (addAssoc half l (- l))
    ∙ cong (half +_) (addInvR l)
    ∙ addIdR half

  upperDifference : y - l ≤ℝ half
  upperDifference =
    subst ((y - l) ≤ℝ_) upperRightPath
      (addPres≤R y (l + half) (- l) y≤l+half)

  l-half≤y : l - half ≤ℝ y
  l-half≤y = ≤ℝ-trans (l - half) x y
    (close→lowerBound x l (ε /2₊) x∼l) x≤y

  lowerRightPath : l + (- (l - half)) ≡ half
  lowerRightPath =
    cong (l +_) (
      negAdd l (- half)
      ∙ cong ((- l) +_) (negInvol half))
    ∙ addAssoc l (- l) half
    ∙ cong (_+ half) (addInvR l)
    ∙ addIdL half

  negDifferencePath : - (y - l) ≡ l - y
  negDifferencePath =
    negAdd y (- l)
    ∙ cong ((- y) +_) (negInvol l)
    ∙ addComm (- y) l

  lowerDifference : (- (y - l)) ≤ℝ half
  lowerDifference =
    subst2 _≤ℝ_ (sym negDifferencePath) lowerRightPath
      (addPres≤L (- y) (- (l - half)) l
        (negPres≤ (l - half) y l-half≤y))

  absoluteBound : absℝ (y - l) ≤ℝ half
  absoluteBound =
    absLeastUpperBound (y - l) half
      upperDifference lowerDifference


-- Constructive squeeze theorem.  All four existential cutoffs are truncated,
-- so the proof combines them only under propositional truncation.
eventuallySqueezePresIsLimitSequence : ∀ {x y z l} →
  EventuallyLeSequence x y →
  EventuallyLeSequence y z →
  isLimitSequence x l →
  isLimitSequence z l →
  isLimitSequence y l
eventuallySqueezePresIsLimitSequence {x} {y} {z} {l}
    x≤y y≤z x→l z→l ε =
  PT.map2 combine
    (PT.map2 (λ left right → left , right) x≤y y≤z)
    (PT.map2 (λ left right → left , right)
      (x→l (ε /2₊)) (z→l (ε /2₊)))
  where
  combine :
    (EventuallyLeTail x y × EventuallyLeTail y z) →
    (LimitTail x l (ε /2₊) × LimitTail z l (ε /2₊)) →
    LimitTail y l ε
  combine ((K , left) , (L , right))
      ((M , x-close) , (N , z-close)) =
    ℕ.max (ℕ.max K L) (ℕ.max M N) , λ n cutoff≤n →
      betweenCloseEndpoints ε
        (left n
          (ℕ.≤-trans
            (ℕ.left-≤-max {m = K} {n = L})
            (ℕ.≤-trans
              (ℕ.left-≤-max {m = ℕ.max K L} {n = ℕ.max M N})
              cutoff≤n)))
        (right n
          (ℕ.≤-trans
            (ℕ.right-≤-max {n = L} {m = K})
            (ℕ.≤-trans
              (ℕ.left-≤-max {m = ℕ.max K L} {n = ℕ.max M N})
              cutoff≤n)))
        (x-close n
          (ℕ.≤-trans
            (ℕ.left-≤-max {m = M} {n = N})
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = ℕ.max M N} {m = ℕ.max K L})
              cutoff≤n)))
        (z-close n
          (ℕ.≤-trans
            (ℕ.right-≤-max {n = N} {m = M})
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = ℕ.max M N} {m = ℕ.max K L})
              cutoff≤n)))


pointwiseSqueezePresIsLimitSequence : ∀ {x y z l} →
  (∀ n → x n ≤ℝ y n) →
  (∀ n → y n ≤ℝ z n) →
  isLimitSequence x l →
  isLimitSequence z l →
  isLimitSequence y l
pointwiseSqueezePresIsLimitSequence {x} {y} {z} {l} left right =
  eventuallySqueezePresIsLimitSequence
    {x = x} {y = y} {z = z} {l = l}
    (pointwiseLe→eventuallyLe {x = x} {y = y} left)
    (pointwiseLe→eventuallyLe {x = y} {y = z} right)
