module Cubical.HITs.CauchyRealsP.Algebra.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

-- Separately non-expanding real functions are determined by their values on
-- rational tuples.  These small arity lemmas keep algebraic density arguments
-- independent of the particular construction of an operation.

composeRealLipschitzWith :
  (f g : ℝ → ℝ) (L K : ℚ₊) →
  IsLipschitzWith
    (snd ℝPremetricSpace) f
    (snd ℝPremetricSpace) L →
  IsLipschitzWith
    (snd ℝPremetricSpace) g
    (snd ℝPremetricSpace) K →
  IsLipschitzWith
    (snd ℝPremetricSpace) (f ∘ g)
    (snd ℝPremetricSpace) (L ·₊ K)
composeRealLipschitzWith f g L K f-lip g-lip
  .IsLipschitzWith.pres≈ x y ε x∼y =
    subst∼
      (f (g x)) (f (g y))
      {ε = L ·₊ (K ·₊ ε)}
      {ε' = (L ·₊ K) ·₊ ε}
      ℚ!
      (IsLipschitzWith.pres≈ f-lip
        (g x) (g y) (K ·₊ ε)
        (IsLipschitzWith.pres≈ g-lip x y ε x∼y))

lipschitzExtensionality₂ :
  (f g : ℝ → ℝ → ℝ)
  → (∀ y → isLipschitz (snd ℝPremetricSpace)
      (λ x → f x y) (snd ℝPremetricSpace))
  → (∀ x → isLipschitz (snd ℝPremetricSpace)
      (f x) (snd ℝPremetricSpace))
  → (∀ y → isLipschitz (snd ℝPremetricSpace)
      (λ x → g x y) (snd ℝPremetricSpace))
  → (∀ x → isLipschitz (snd ℝPremetricSpace)
      (g x) (snd ℝPremetricSpace))
  → (∀ p q → f (rat p) (rat q) ≡ g (rat p) (rat q))
  → ∀ x y → f x y ≡ g x y
lipschitzExtensionality₂ f g f-lip₁ f-lip₂ g-lip₁ g-lip₂ on-rat x y =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      (λ u → f u y) (λ u → g u y)
      (f-lip₁ y) (g-lip₁ y)
      λ p →
        funExt⁻
          (lipschitzExtensionality ℝPremetricSpace
            (f (rat p)) (g (rat p))
            (f-lip₂ (rat p)) (g-lip₂ (rat p))
            (on-rat p))
          y)
    x

lipschitzExtensionality₃ :
  (f g : ℝ → ℝ → ℝ → ℝ)
  → (∀ y z → isLipschitz (snd ℝPremetricSpace)
      (λ x → f x y z) (snd ℝPremetricSpace))
  → (∀ x z → isLipschitz (snd ℝPremetricSpace)
      (λ y → f x y z) (snd ℝPremetricSpace))
  → (∀ x y → isLipschitz (snd ℝPremetricSpace)
      (f x y) (snd ℝPremetricSpace))
  → (∀ y z → isLipschitz (snd ℝPremetricSpace)
      (λ x → g x y z) (snd ℝPremetricSpace))
  → (∀ x z → isLipschitz (snd ℝPremetricSpace)
      (λ y → g x y z) (snd ℝPremetricSpace))
  → (∀ x y → isLipschitz (snd ℝPremetricSpace)
      (g x y) (snd ℝPremetricSpace))
  → (∀ p q r →
      f (rat p) (rat q) (rat r) ≡
      g (rat p) (rat q) (rat r))
  → ∀ x y z → f x y z ≡ g x y z
lipschitzExtensionality₃
  f g f-lip₁ f-lip₂ f-lip₃ g-lip₁ g-lip₂ g-lip₃
  on-rat x y z =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      (λ u → f u y z) (λ u → g u y z)
      (f-lip₁ y z) (g-lip₁ y z)
      λ p →
        funExt⁻
          (lipschitzExtensionality ℝPremetricSpace
            (λ v → f (rat p) v z)
            (λ v → g (rat p) v z)
            (f-lip₂ (rat p) z) (g-lip₂ (rat p) z)
            λ q →
              funExt⁻
                (lipschitzExtensionality ℝPremetricSpace
                  (f (rat p) (rat q))
                  (g (rat p) (rat q))
                  (f-lip₃ (rat p) (rat q))
                  (g-lip₃ (rat p) (rat q))
                  (on-rat p q))
                z)
          y)
    x

nonExpandingExtensionality₂ :
  (f g : ℝ → ℝ → ℝ)
  → (∀ y → IsNonExpanding (snd ℝPremetricSpace)
      (λ x → f x y) (snd ℝPremetricSpace))
  → (∀ x → IsNonExpanding (snd ℝPremetricSpace)
      (f x) (snd ℝPremetricSpace))
  → (∀ y → IsNonExpanding (snd ℝPremetricSpace)
      (λ x → g x y) (snd ℝPremetricSpace))
  → (∀ x → IsNonExpanding (snd ℝPremetricSpace)
      (g x) (snd ℝPremetricSpace))
  → (∀ p q → f (rat p) (rat q) ≡ g (rat p) (rat q))
  → ∀ x y → f x y ≡ g x y
nonExpandingExtensionality₂ f g f-ne₁ f-ne₂ g-ne₁ g-ne₂ on-rat x y =
  funExt⁻
    (nonExpandingExtensionality ℝPremetricSpace
      (λ u → f u y) (λ u → g u y)
      (f-ne₁ y) (g-ne₁ y)
      λ p →
        funExt⁻
          (nonExpandingExtensionality ℝPremetricSpace
            (f (rat p)) (g (rat p))
            (f-ne₂ (rat p)) (g-ne₂ (rat p))
            (on-rat p))
          y)
    x

nonExpandingExtensionality₃ :
  (f g : ℝ → ℝ → ℝ → ℝ)
  → (∀ y z → IsNonExpanding (snd ℝPremetricSpace)
      (λ x → f x y z) (snd ℝPremetricSpace))
  → (∀ x z → IsNonExpanding (snd ℝPremetricSpace)
      (λ y → f x y z) (snd ℝPremetricSpace))
  → (∀ x y → IsNonExpanding (snd ℝPremetricSpace)
      (f x y) (snd ℝPremetricSpace))
  → (∀ y z → IsNonExpanding (snd ℝPremetricSpace)
      (λ x → g x y z) (snd ℝPremetricSpace))
  → (∀ x z → IsNonExpanding (snd ℝPremetricSpace)
      (λ y → g x y z) (snd ℝPremetricSpace))
  → (∀ x y → IsNonExpanding (snd ℝPremetricSpace)
      (g x y) (snd ℝPremetricSpace))
  → (∀ p q r →
      f (rat p) (rat q) (rat r) ≡
      g (rat p) (rat q) (rat r))
  → ∀ x y z → f x y z ≡ g x y z
nonExpandingExtensionality₃
  f g f-ne₁ f-ne₂ f-ne₃ g-ne₁ g-ne₂ g-ne₃ on-rat x y z =
  funExt⁻
    (nonExpandingExtensionality ℝPremetricSpace
      (λ u → f u y z) (λ u → g u y z)
      (f-ne₁ y z) (g-ne₁ y z)
      λ p →
        funExt⁻
          (nonExpandingExtensionality ℝPremetricSpace
            (λ v → f (rat p) v z)
            (λ v → g (rat p) v z)
            (f-ne₂ (rat p) z) (g-ne₂ (rat p) z)
            λ q →
              funExt⁻
                (nonExpandingExtensionality ℝPremetricSpace
                  (f (rat p) (rat q))
                  (g (rat p) (rat q))
                  (f-ne₃ (rat p) (rat q))
                  (g-ne₃ (rat p) (rat q))
                  (on-rat p q))
                z)
          y)
    x
