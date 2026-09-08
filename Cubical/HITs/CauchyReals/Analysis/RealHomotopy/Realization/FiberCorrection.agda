module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.FiberCorrection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPathr-cancel; compPath→Square)
open import Cubical.Data.Sigma

-- This lemma is independent of a choice of cubical realization. The
-- hypothesis records all compatibility with the map to the base; it
-- cannot be inferred merely from a homotopy in the total space.
module _ {ℓE ℓB} {E : Type ℓE} {B : Type ℓB} (p : E → B)
         {b : B} (u v : fiber p b)
         (h : fst u ≡ fst v) (d : fst v ≡ fst v)
         (projection : cong p h ≡ (snd u ∙ sym (snd v)) ∙ cong p d)
         where

  correctedPath : fst u ≡ fst v
  correctedPath = h ∙ sym d

  correctedProjection : cong p correctedPath ≡ snd u ∙ sym (snd v)
  correctedProjection =
    cong-∙ p h (sym d)
    ∙ cong (_∙ sym (cong p d)) projection
    ∙ compPathr-cancel (sym (cong p d)) (snd u ∙ sym (snd v))

  correctedFiberPath : u ≡ v
  correctedFiberPath = ΣPathP (correctedPath , compPath→Square
    (cong (_∙ snd v) correctedProjection
      ∙ compPathr-cancel (snd v) (snd u)
      ∙ rUnit (snd u)))

  correctedFiberPath-fst : cong fst correctedFiberPath ≡ correctedPath
  correctedFiberPath-fst = refl

-- Quantification over an arbitrary type includes families in every
-- dimension. No truncation or dimension-dependent fillers are used.
module _ {ℓA ℓE ℓB} {A : Type ℓA} {E : Type ℓE} {B : Type ℓB}
         (p : E → B) {b : B} (f g : A → fiber p b)
         (h : (a : A) → fst (f a) ≡ fst (g a))
         (d : (a : A) → fst (g a) ≡ fst (g a))
         (projection : (a : A) →
           cong p (h a) ≡ (snd (f a) ∙ sym (snd (g a))) ∙ cong p (d a))
         where

  correctedFiberHomotopy : f ≡ g
  correctedFiberHomotopy = funExt λ a →
    correctedFiberPath p (f a) (g a) (h a) (d a) (projection a)
