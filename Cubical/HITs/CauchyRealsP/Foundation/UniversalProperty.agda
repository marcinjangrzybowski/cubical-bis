module Cubical.HITs.CauchyRealsP.Foundation.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation.Closeness public
open import Cubical.HITs.CauchyRealsP.Foundation.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Properties.Lift

private
  variable
    ℓ ℓ' : Level

-- Quantitative maps out of ℝ are determined by their rational values.  This
-- uniqueness half does not require the codomain itself to be complete.
nonExpandingExtensionality :
  (N' : PremetricSpace ℓ ℓ')
  (f g : ℝ → fst N')
  → IsNonExpanding (snd ℝPremetricSpace) f (snd N')
  → IsNonExpanding (snd ℝPremetricSpace) g (snd N')
  → (∀ q → f (rat q) ≡ g (rat q))
  → f ≡ g
nonExpandingExtensionality N' f g f-ne g-ne on-rat =
  cong fst
    (nonExpanding≡ ℚPremetricSpace N'
      (f , f-ne) (g , g-ne) (funExt on-rat))

continuousExtensionality :
  (N' : PremetricSpace ℓ ℓ')
  (f g : ℝ → fst N')
  → isContinuous (snd ℝPremetricSpace) f (snd N')
  → isContinuous (snd ℝPremetricSpace) g (snd N')
  → (∀ q → f (rat q) ≡ g (rat q))
  → f ≡ g
continuousExtensionality N' f g f-cont g-cont on-rat =
  cong fst
    (continuous≡ ℚPremetricSpace N'
      (f , f-cont) (g , g-cont) (funExt on-rat))

lipschitzExtensionality :
  (N' : PremetricSpace ℓ ℓ')
  (f g : ℝ → fst N')
  → isLipschitz (snd ℝPremetricSpace) f (snd N')
  → isLipschitz (snd ℝPremetricSpace) g (snd N')
  → (∀ q → f (rat q) ≡ g (rat q))
  → f ≡ g
lipschitzExtensionality N' f g f-lip g-lip on-rat =
  cong fst
    (lipschitz≡ ℚPremetricSpace N'
      (f , f-lip) (g , g-lip) (funExt on-rat))

-- The completion is free into a complete codomain for quantitative maps.
-- Keeping existence and uniqueness separate is convenient when defining
-- operations; the contractible formulation below packages the full property.
module CompleteCodomain
  (N' : PremetricSpace ℓ ℓ')
  (N-complete : PremetricTheory.isComplete N')
  where

  private
    module N = PremetricStr (snd N')
    module Ext = LiftCompleteCodomain
      ℚPremetricSpace N' N-complete

  nonExpandingExtension :
    (f : NE[ ℚPremetricSpace , N' ])
    → Σ[ g ∈ NE[ ℝPremetricSpace , N' ] ]
        fst g ∘ rat ≡ fst f
  nonExpandingExtension = Ext.liftNonExpandingExtension

  nonExpandingExtensionUnique :
    (f : NE[ ℚPremetricSpace , N' ])
    (g h : NE[ ℝPremetricSpace , N' ])
    → fst g ∘ rat ≡ fst f
    → fst h ∘ rat ≡ fst f
    → g ≡ h
  nonExpandingExtensionUnique f g h g-rat h-rat =
    nonExpanding≡ ℚPremetricSpace N' g h
      (g-rat ∙ sym h-rat)

  nonExpandingUniversalProperty :
    (f : NE[ ℚPremetricSpace , N' ])
    → isContr
        (Σ[ g ∈ NE[ ℝPremetricSpace , N' ] ]
          fst g ∘ rat ≡ fst f)
  nonExpandingUniversalProperty f =
    center , λ candidate →
      Σ≡Prop
        (λ g → isSetΠ (λ _ → N.isSetM)
          (fst g ∘ rat) (fst f))
        (nonExpandingExtensionUnique f
          (fst center) (fst candidate)
          (snd center) (snd candidate))
    where
    center :
      Σ[ g ∈ NE[ ℝPremetricSpace , N' ] ]
        fst g ∘ rat ≡ fst f
    center = nonExpandingExtension f
