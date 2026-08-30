module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (ℚ)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


private
  variable
    ℓ ℓ' : Level


-- Maps out of the Cauchy-sequence reals are determined by their rational
-- values as soon as they are pointwise continuous.  This is the uniqueness
-- principle needed by local constructions; it uses only rational density,
-- not a comparison with another completion.

continuousExtensionality :
  (N' : PremetricSpace ℓ ℓ')
  (f g : Real.ℝ → fst N') →
  isContinuous (snd Real.ℝPremetricSpace) f (snd N') →
  isContinuous (snd Real.ℝPremetricSpace) g (snd N') →
  (∀ q → f (Real.ιℚ q) ≡ g (Real.ιℚ q)) →
  f ≡ g
continuousExtensionality N' f g f-cont g-cont on-rational =
  funExt equalAt
  where
  module N = PremetricStr (snd N')

  equalAt : ∀ x → f x ≡ g x
  equalAt x = N.isSeparated≈ (f x) (g x) closeAt
    where
    closeAt : ∀ ε → f x N.≈[ ε ] g x
    closeAt ε =
      PT.rec2 (N.isProp≈ (f x) (g x) ε)
        useContinuity
        (f-cont x .IsContinuousAt.pres≈ (ε /2₊))
        (g-cont x .IsContinuousAt.pres≈ (ε /2₊))
      where
      useContinuity :
        (Σ[ δf ∈ ℚ₊ ]
          (∀ y → x Real.Base.≈ᶜ[ δf ] y →
            f x N.≈[ ε /2₊ ] f y)) →
        (Σ[ δg ∈ ℚ₊ ]
          (∀ y → x Real.Base.≈ᶜ[ δg ] y →
            g x N.≈[ ε /2₊ ] g y)) →
        f x N.≈[ ε ] g x
      useContinuity (δf , f-close) (δg , g-close) =
        PT.rec (N.isProp≈ (f x) (g x) ε)
          useApproximation
          (Real.rationalsDense x ρ)
        where
        ρ : ℚ₊
        ρ = min₊ δf δg /2₊

        x-close-rational : ∀ q →
          Real.ιℚ q Real.Base.≈ᶜ[ ρ ] x →
          (x Real.Base.≈ᶜ[ δf ] Real.ιℚ q) ×
          (x Real.Base.≈ᶜ[ δg ] Real.ιℚ q)
        x-close-rational q ιq∼x =
          Real.Base.isMonotone≈ᶜ< x (Real.ιℚ q) ρ δf
            (min/2₊<L δf δg)
            (Real.Base.sym≈ᶜ (Real.ιℚ q) x ρ ιq∼x)
          ,
          Real.Base.isMonotone≈ᶜ< x (Real.ιℚ q) ρ δg
            (min/2₊<R δf δg)
            (Real.Base.sym≈ᶜ (Real.ιℚ q) x ρ ιq∼x)

        useApproximation :
          (Σ[ q ∈ ℚ ] Real.ιℚ q Real.Base.≈ᶜ[ ρ ] x) →
          f x N.≈[ ε ] g x
        useApproximation (q , ιq∼x) =
          N.subst≈ (f x) (g x) (/2+/2≡id (fst ε))
            (N.isTriangular≈
              (f x) (g (Real.ιℚ q)) (g x)
              (ε /2₊) (ε /2₊)
              (subst (f x N.≈[ ε /2₊ ]_)
                (on-rational q)
                (f-close (Real.ιℚ q)
                  (fst (x-close-rational q ιq∼x))))
              (N.isSym≈
                (g x) (g (Real.ιℚ q)) (ε /2₊)
                (g-close (Real.ιℚ q)
                  (snd (x-close-rational q ιq∼x)))))


lipschitzExtensionality :
  (N' : PremetricSpace ℓ ℓ')
  (f g : Real.ℝ → fst N') →
  isLipschitz (snd Real.ℝPremetricSpace) f (snd N') →
  isLipschitz (snd Real.ℝPremetricSpace) g (snd N') →
  (∀ q → f (Real.ιℚ q) ≡ g (Real.ιℚ q)) →
  f ≡ g
lipschitzExtensionality N' f g f-lip g-lip =
  continuousExtensionality N' f g
    (isLipschitz→isContinuous
      (snd Real.ℝPremetricSpace) f (snd N') f-lip)
    (isLipschitz→isContinuous
      (snd Real.ℝPremetricSpace) g (snd N') g-lip)


nonExpandingExtensionality :
  (N' : PremetricSpace ℓ ℓ')
  (f g : Real.ℝ → fst N') →
  IsNonExpanding (snd Real.ℝPremetricSpace) f (snd N') →
  IsNonExpanding (snd Real.ℝPremetricSpace) g (snd N') →
  (∀ q → f (Real.ιℚ q) ≡ g (Real.ιℚ q)) →
  f ≡ g
nonExpandingExtensionality N' f g f-ne g-ne =
  continuousExtensionality N' f g
    (isNonExpanding→isContinuous
      (snd Real.ℝPremetricSpace) f (snd N') f-ne)
    (isNonExpanding→isContinuous
      (snd Real.ℝPremetricSpace) g (snd N') g-ne)
