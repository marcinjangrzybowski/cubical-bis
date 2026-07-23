module Cubical.HITs.CauchyReals.Analysis.Lipschitz.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core


opaque
 unfolding fromLipschitz

 fromLipschitz' : ∀ f → ∃[ L ∈ ℚ₊ ] (Lipschitz-ℚ→ℝ L f)
   → Σ[ f' ∈ (ℝ → ℝ) ] ∃[ L ∈ ℚ₊ ] (Lipschitz-ℝ→ℝ L f')
 fromLipschitz' f = PT.elim→Set
   (λ _ → isSetΣ (isSet→ isSetℝ)
     λ _ → isProp→isSet squash₁)
   (λ (L , lip) →
     map-snd (∣_∣₁ ∘ (L ,_)) $ fromLipschitz L (f , lip))
   λ (L , lip) (L' , lip') →
     Σ≡Prop (λ _ → squash₁)
       (funExt (≡Continuous _ _
         (Lipschitz→IsContinuous L _
           (snd (fromLipschitz L (f , lip))))
         (Lipschitz→IsContinuous L' _
           (snd (fromLipschitz L' (f , lip'))))
         (λ _ → refl)))


 fromLipschitz'-rat : ∀ f isL q →
   fst (fromLipschitz' (f ∘S rat) isL) (rat q) ≡ f (rat q)
 fromLipschitz'-rat f = PT.elim
  (λ _ → isPropΠ λ _ → isSetℝ _ _)
  λ (L , lip) q →
    fromLipschitz-rat {L = L} {lf = (f ∘S rat , lip)} {q = q}
