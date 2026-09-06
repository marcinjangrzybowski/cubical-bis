module Cubical.HITs.CauchyReals.Circle.Winding.Loop where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; isSetℤ)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (<≤ℚ!)
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using (injFromNatℚ)
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.Relation.Premetric.Mappings

-- A winding number is witnessed by the sum of the short angular
-- increments on a sufficiently fine dyadic subdivision of [0,1].
WindingWitness : (ℝ → distCircle) → ℤ → Type
WindingWitness f k = Σ[ n ∈ ℕ ] Σ[ fine ∈ S.Fine n 0 1 ]
  S.turns n 0 1 unit-order fine ≡ rat [ k / 1 ]
  where
  module S = Subdivision (f ∘ rat)

HasWinding : (ℝ → distCircle) → ℤ → Type
HasWinding f k = ∥ WindingWitness f k ∥₁

hasWinding-unique : ∀ f k l → HasWinding f k → HasWinding f l → k ≡ l
hasWinding-unique f k l = PT.rec2 (isSetℤ k l) unique
  where
  unique : WindingWitness f k → WindingWitness f l → k ≡ l
  unique (n , fine , p) (m , fine' , q) = injFromNatℚ k l
    (inj-rat _ _ (sym p ∙ Subdivision.turns-unique (f ∘ rat)
      n m 0 1 unit-order fine fine' ∙ q))

isPropWinding : ∀ f → isProp (Σ ℤ (HasWinding f))
isPropWinding f (k , p) (l , q) =
  Σ≡Prop (λ _ → squash₁) (hasWinding-unique f k l p q)

private
  opaque
    cancel-unit : ∀ p q → p ℝS¹.+ q ≡ p → q ≡ circle0
    cancel-unit p q closes = ℝS¹.1gUniqueR p {e = q} closes

  opaque
    loop-integer : ∀ t p → p ℝS¹.+ cover t ≡ p → circle-rel t 0
    loop-integer t p closes = cover-effective t 0
      (cancel-unit p (cover t) closes ∙ sym cover-zero)

  opaque
    subdivision-integer : ∀ (f : ℚ → distCircle) → f 0 ≡ f 1 →
      ∀ n (fine : Subdivision.Fine f n 0 1) →
      Σ[ k ∈ ℤ ] Subdivision.turns f n 0 1 unit-order fine ≡ rat [ k / 1 ]
    subdivision-integer f loop n fine = fst k ,
      sym (cong (t +ᵣ_) (-ᵣ-rat 0) ∙ Rℝ.+IdR t) ∙ snd k
      where
      t : ℝ
      t = Subdivision.turns f n 0 1 unit-order fine
      k : circle-rel t 0
      k = loop-integer (Subdivision.turns f n 0 1 unit-order fine) (f 0)
        (Subdivision.turns-cover f n 0 1 unit-order fine ∙ sym loop)

-- Elimination of truncation is justified by uniqueness of the complete
-- (integer, winding proof) pair. No choice of a modulus is made.
windingLoop-result : (f : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
  fst f 0 ≡ fst f 1 → Σ ℤ (HasWinding (fst f))
windingLoop-result f loop = PT.rec (isPropWinding (fst f))
  (λ (n , fine) → let k = subdivision-integer (fst f ∘ rat) loop n fine
    in fst k , ∣ n , fine , snd k ∣₁)
  (fine-uniform f)

opaque
  windingLoop : (f : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
    fst f 0 ≡ fst f 1 → ℤ
  windingLoop f loop = fst (windingLoop-result f loop)

  windingLoop-spec : ∀ f loop → HasWinding (fst f) (windingLoop f loop)
  windingLoop-spec f loop = snd (windingLoop-result f loop)

windingLoop-subdivision : ∀ f loop n fine →
  Subdivision.turns (fst f ∘ rat) n 0 1 unit-order fine ≡ rat [ windingLoop f loop / 1 ]
windingLoop-subdivision f loop n fine = PT.rec (isSetℝ _ _)
  (λ (m , fine' , p) →
    Subdivision.turns-unique (fst f ∘ rat) n m 0 1 unit-order fine fine' ∙ p)
  (windingLoop-spec f loop)

windingLoop-cong : (f g : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
  (fl : fst f 0 ≡ fst f 1) (gl : fst g 0 ≡ fst g 1) →
  (∀ x → fst f x ≡ fst g x) → windingLoop f fl ≡ windingLoop g gl
windingLoop-cong f g fl gl equal = cong
  (λ (z : Σ[ h ∈ UC[ ℝPremetricSpace , distCirclePremetricSpace ] ] fst h 0 ≡ fst h 1) →
    windingLoop (fst z) (snd z))
  (Σ≡Prop (λ _ → isSetDistCircle _ _) maps)
  where
  maps : f ≡ g
  maps = Σ≡Prop (λ _ → squash₁) (funExt equal)
