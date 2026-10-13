module Cubical.Analysis.Circle.Winding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (_∘UC_)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Circle.Base
open import Cubical.Analysis.Circle.Metric
open import Cubical.Analysis.Circle.Winding.Loop public
open import Cubical.Analysis.Circle.Winding.Lift public

cover-endpoints : cover (rat 0) ≡ cover (rat 1)
cover-endpoints = sym (cover-integer (pos 1))

windingNumber : UC[ CirclePremetricSpace , CirclePremetricSpace ] → ℤ
windingNumber f = windingLoop (f ∘UC coverUC) (cong (fst f) cover-endpoints)

windingNumber-spec : (f : UC[ CirclePremetricSpace , CirclePremetricSpace ]) →
  HasWinding (fst f ∘ cover) (windingNumber f)
windingNumber-spec f = windingLoop-spec (f ∘UC coverUC) (cong (fst f) cover-endpoints)

windingNumber-lift : (f : UC[ CirclePremetricSpace , CirclePremetricSpace ]) →
  (g : UC[ ℝPremetricSpace , ℝPremetricSpace ]) →
  (∀ x y → fst f (cover x) +ᶜ cover (fst g y - fst g x) ≡ fst f (cover y)) →
  integer (windingNumber f) ≡ fst g (rat 1) - fst g (rat 0)
windingNumber-lift f = windingLoop-lift (f ∘UC coverUC) (cong (fst f) cover-endpoints)

windingNumber-cong : (f g : UC[ CirclePremetricSpace , CirclePremetricSpace ]) →
  (∀ x → fst f x ≡ fst g x) → windingNumber f ≡ windingNumber g
windingNumber-cong f g equal = windingLoop-cong (f ∘UC coverUC) (g ∘UC coverUC)
  (cong (fst f) cover-endpoints) (cong (fst g) cover-endpoints) (equal ∘ cover)
