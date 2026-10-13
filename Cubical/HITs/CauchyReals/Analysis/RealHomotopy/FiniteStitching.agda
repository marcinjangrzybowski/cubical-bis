module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using (Dichotomyℝ')
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric using (ℝPremetricSpace)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Stitching
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

cut : ℕ → ℚ
cut zero = 0
cut (suc n) = cut n ℚ.+ 2

-- Width-one overlaps are separated by width-one transition intervals.
-- Adjacent plateaus must leave room for a nonconstant interpolation.
upper : ℕ → ℚ
upper n = cut n ℚ.+ 1

cut-increases : (n : ℕ) → rat (cut n) <ᵣ rat (cut (suc n))
cut-increases n = <ℚ→<ᵣ (cut n) (cut n ℚ.+ 2) <≤ℚ!

overlap-positive : (n : ℕ) → rat (cut n) <ᵣ rat (upper n)
overlap-positive n = <ℚ→<ᵣ (cut n) (cut n ℚ.+ 1) <≤ℚ!

-- Finitely many branches with actual agreement on positive-width
-- overlaps. The arbitrary parameter Y retains all other coordinates.
module FinitePaste {ℓX ℓX' ℓY ℓY'}
  (X : PremetricSpace ℓX ℓX') (Y : PremetricSpace ℓY ℓY') where

  Branch : Type _
  Branch = UC[ PremetricProduct ℝPremetricSpace Y , X ]

  Overlap : ℕ → Branch → Branch → Type _
  Overlap n f g = (t : ℝ) (y : fst Y) →
    rat (cut n) <ᵣ t → t <ᵣ rat (upper n) → fst f (t , y) ≡ fst g (t , y)

  Chain : ℕ → Type _
  last : (n : ℕ) → Chain n → Branch
  Chain zero = Branch
  Chain (suc n) = Σ[ c ∈ Chain n ] Σ[ g ∈ Branch ] Overlap n (last n c) g
  last zero c = c
  last (suc n) (c , g , agrees) = g

  paste : (n : ℕ) → Chain n → Branch
  last-after : (n : ℕ) (c : Chain n) (t : ℝ) (y : fst Y) →
    rat (cut n) <ᵣ t → fst (paste n c) (t , y) ≡ fst (last n c) (t , y)
  paste zero c = c
  paste (suc n) (c , g , agrees) = Stitch.stitchedUC X Y (cut n) (paste n c) g
    (λ t y lo hi → last-after n c t y lo ∙ agrees t y lo hi)
  last-after zero c t y lo = refl
  last-after (suc n) (c , g , agrees) t y lo =
    Stitch.stitched-right X Y (cut n) (paste n c) g
      (λ t y lo hi → last-after n c t y lo ∙ agrees t y lo hi)
      t y (isTrans<ᵣ _ _ _ (cut-increases n) lo)

  -- A single invariant transports error estimates or constant boundary
  -- laws through the whole finite chain. Q need only be a proposition
  -- at each value; no target completeness or choice is used.
  module Property {ℓQ} (Q : ℝ × fst Y → fst X → Type ℓQ)
    (Q-prop : (u : ℝ × fst Y) (z : fst X) → isProp (Q u z)) where

    Branchwise : (n : ℕ) → Chain n → Type (ℓ-max ℓY ℓQ)
    Branchwise zero f = (t : ℝ) (y : fst Y) →
      t <ᵣ rat (upper zero) → Q (t , y) (fst f (t , y))
    Branchwise (suc n) (c , g , agrees) = Branchwise n c ×
      ((t : ℝ) (y : fst Y) → rat (cut n) <ᵣ t →
        t <ᵣ rat (upper (suc n)) → Q (t , y) (fst g (t , y)))

    paste-property : (n : ℕ) (c : Chain n) → Branchwise n c →
      (t : ℝ) (y : fst Y) → t <ᵣ rat (upper n) → Q (t , y) (fst (paste n c) (t , y))
    paste-property zero f good t y hi = good t y hi
    paste-property (suc n) (c , g , agrees) (previous , good) t y hi =
      PT.rec (Q-prop (t , y) _) (λ where
        (inl left) → subst (Q (t , y)) (sym (S.stitched-left t y left))
          (paste-property n c previous t y left)
        (inr right) → subst (Q (t , y)) (sym (S.stitched-right t y right))
          (good t y right hi))
        (Dichotomyℝ' (rat (cut n)) t (rat (upper n)) (overlap-positive n))
      where
      module S = Stitch X Y (cut n) (paste n c) g
        (λ t y lo hi → last-after n c t y lo ∙ agrees t y lo hi)
