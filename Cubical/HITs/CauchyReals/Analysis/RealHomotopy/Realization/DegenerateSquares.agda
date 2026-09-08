module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.DegenerateSquares where

open import Cubical.Foundations.Prelude

-- Fill a square whose horizontal edges agree and whose vertical edges
-- have specified contractions to reflexivity. The target may have any
-- higher homotopy: only these particular identity edges are contracted.
module _ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
  {u : x ≡ x} {v : y ≡ y} (unit-u : u ≡ refl) (unit-v : v ≡ refl) where

  horizontalSquare : Square u v p p
  horizontalSquare i j = hcomp (λ k → λ
    { (i = i0) → unit-u (~ k) j
    ; (i = i1) → unit-v (~ k) j
    ; (j = i0) → p i
    ; (j = i1) → p i
    }) (p i)

  verticalSquare : Square p p u v
  verticalSquare i j = horizontalSquare j i

-- At the overlap of the two degeneracies all four edges are the same
-- designated identity. Path induction takes place in the loop type;
-- it does not truncate the ambient type or its spaces of squares.
constantSquare-coherence : ∀ {ℓ} {A : Type ℓ} {x : A}
  (u : x ≡ x) (unit-u : u ≡ refl) →
  horizontalSquare u unit-u unit-u ≡ verticalSquare u unit-u unit-u
constantSquare-coherence u unit-u =
  J (λ v p → horizontalSquare v (sym p) (sym p) ≡
               verticalSquare v (sym p) (sym p)) refl (sym unit-u)

-- Keep the propositional computation rule for later overlap inductions.
constantSquare-coherence-refl : ∀ {ℓ} {A : Type ℓ} {x : A} →
  constantSquare-coherence (refl {x = x}) refl ≡ refl
constantSquare-coherence-refl {x = x} =
  JRefl {x = refl {x = x}}
    (λ v p → horizontalSquare v (sym p) (sym p) ≡
               verticalSquare v (sym p) (sym p)) refl
