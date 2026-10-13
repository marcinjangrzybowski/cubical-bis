module Cubical.Analysis.Circle.Winding.Loop where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; isSetℤ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Circle.Base
open import Cubical.Analysis.Circle.Metric
open import Cubical.Analysis.Circle.Winding.Subdivision
open import Cubical.Analysis.Circle.Winding.Continuity

WindingWitness : (ℝ → Circle) → ℤ → Type
WindingWitness f k = Σ[ n ∈ ℕ ] Σ[ fine ∈ SD.Fine n 0 1 ]
  SD.turns n 0 1 unit-order fine ≡ integer k
  where module SD = Subdivision (f ∘ rat)

HasWinding : (ℝ → Circle) → ℤ → Type
HasWinding f k = ∥ WindingWitness f k ∥₁

hasWinding-unique : ∀ f k l → HasWinding f k → HasWinding f l → k ≡ l
hasWinding-unique f k l = PT.rec2 (isSetℤ k l) unique
  where
  unique : WindingWitness f k → WindingWitness f l → k ≡ l
  unique (n , fine , p) (m , fine' , q) = integer-injective
    (sym p ∙ Subdivision.turns-unique (f ∘ rat)
      n m 0 1 unit-order fine fine' ∙ q)

isPropWinding : ∀ f → isProp (Σ ℤ (HasWinding f))
isPropWinding f (k , p) (l , q) =
  Σ≡Prop (λ _ → squash₁) (hasWinding-unique f k l p q)

subdivision-integer : (f : ℚ → Circle) → f 0 ≡ f 1 →
  ∀ n (fine : Subdivision.Fine f n 0 1) →
  Σ[ k ∈ ℤ ] Subdivision.turns f n 0 1 unit-order fine ≡ integer k
subdivision-integer f loop n fine = cover-kernel
  (Subdivision.turns f n 0 1 unit-order fine)
  (CircleGroup.1gUniqueR (f 0) {e = cover (Subdivision.turns f n 0 1 unit-order fine)}
    (Subdivision.turns-cover f n 0 1 unit-order fine ∙ sym loop))

-- The integer together with its complete specification is a proposition.
-- This is the precise reason elimination of the continuity truncation is
-- valid, despite the integer type itself not being a proposition.
windingLoop-result : (f : UC[ ℝPremetricSpace , CirclePremetricSpace ]) →
  fst f (rat 0) ≡ fst f (rat 1) → Σ ℤ (HasWinding (fst f))
windingLoop-result f loop = PT.rec (isPropWinding (fst f))
  (λ (n , fine) → let k = subdivision-integer (fst f ∘ rat) loop n fine
    in fst k , ∣ n , fine , snd k ∣₁)
  (fine-uniform f)

opaque
  windingLoop : (f : UC[ ℝPremetricSpace , CirclePremetricSpace ]) →
    fst f (rat 0) ≡ fst f (rat 1) → ℤ
  windingLoop f loop = fst (windingLoop-result f loop)

  windingLoop-spec : ∀ f loop → HasWinding (fst f) (windingLoop f loop)
  windingLoop-spec f loop = snd (windingLoop-result f loop)

windingLoop-subdivision : ∀ f loop n fine →
  Subdivision.turns (fst f ∘ rat) n 0 1 unit-order fine ≡ integer (windingLoop f loop)
windingLoop-subdivision f loop n fine = PT.rec (isSetℝ _ _)
  (λ (m , fine' , p) →
    Subdivision.turns-unique (fst f ∘ rat) n m 0 1 unit-order fine fine' ∙ p)
  (windingLoop-spec f loop)

windingLoop-cong : (f g : UC[ ℝPremetricSpace , CirclePremetricSpace ]) →
  (fl : fst f (rat 0) ≡ fst f (rat 1)) (gl : fst g (rat 0) ≡ fst g (rat 1)) →
  (∀ x → fst f x ≡ fst g x) → windingLoop f fl ≡ windingLoop g gl
windingLoop-cong f g fl gl equal =
  hasWinding-unique (fst g) (windingLoop f fl) (windingLoop g gl)
    (subst (λ h → HasWinding h (windingLoop f fl)) (funExt equal)
      (windingLoop-spec f fl))
    (windingLoop-spec g gl)
