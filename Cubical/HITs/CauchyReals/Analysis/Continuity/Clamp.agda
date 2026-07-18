module Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.OrderedCommRing.Clamp
open import Cubical.Relation.Binary.Order.Pseudolattice.Clamp

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using
  (ℝ≤Pseudolattice; ℝOrderedCommRing)

private
  module ℝClamp = PseudolatticeClamp ℝ≤Pseudolattice
  module ℝRingClamp = OrderedCommRingClamp ℝOrderedCommRing


clampᵣ∈intervalℙ : ∀ a b → a ≤ᵣ b → ∀ x → clampᵣ a b x ∈ intervalℙ a b
clampᵣ∈intervalℙ a b a≤b x =
  ≤clampᵣ a b x a≤b , clamp≤ᵣ a b x

-- Compatibility name: the endpoints and clamped value are Cauchy reals.
clampᵣ∈ℚintervalℙ : ∀ a b → a ≤ᵣ b → ∀ x → clampᵣ a b x ∈ intervalℙ a b
clampᵣ∈ℚintervalℙ = clampᵣ∈intervalℙ

≡clampᵣ→∈intervalℙ : ∀ a b → a ≤ᵣ b → ∀ x →
  x ≡ clampᵣ a b x → x ∈ intervalℙ a b
≡clampᵣ→∈intervalℙ a b a≤b x p =
  subst-∈ (intervalℙ a b) (sym p) (clampᵣ∈intervalℙ a b a≤b x)

elimIntervalByClampᵣ : ∀ {ℓ} {P : ℝ → Type ℓ} a b →
  (∀ x → P (clampᵣ a b x)) →
  ∀ x → x ∈ intervalℙ a b → P x
elimIntervalByClampᵣ {P = P} a b inClamp x (a≤x , x≤b) =
  ℝClamp.elimIntervalByClamp {A = P} a b inClamp x a≤x x≤b


opaque
  x≤→clampᵣ≡ : ∀ a b x → a ≤ᵣ b → x ≤ᵣ a → clampᵣ a b x ≡ a
  x≤→clampᵣ≡ = ℝClamp.belowLower→clamp≡Lower

  ≤x→clampᵣ≡ : ∀ a b x → a ≤ᵣ b → b ≤ᵣ x → clampᵣ a b x ≡ b
  ≤x→clampᵣ≡ = ℝClamp.aboveUpper→clamp≡Upper

  min-monotone-≤ᵣ : ∀ a x y → x ≤ᵣ y → minᵣ x a ≤ᵣ minᵣ y a
  min-monotone-≤ᵣ a x y x≤y =
    ℝClamp.∧Isotone x≤y (≤ᵣ-refl a)

  max-monotone-≤ᵣ : ∀ a x y → x ≤ᵣ y → maxᵣ a x ≤ᵣ maxᵣ a y
  max-monotone-≤ᵣ a x y x≤y =
    ℝClamp.∨Isotone (≤ᵣ-refl a) x≤y


clamp-monotone-≤ᵣ : ∀ a b x y → x ≤ᵣ y → clampᵣ a b x ≤ᵣ clampᵣ a b y
clamp-monotone-≤ᵣ = ℝClamp.clampIsotone


clampDistᵣ : ∀ lower upper x y →
  absᵣ (clampᵣ lower upper y -ᵣ clampᵣ lower upper x) ≤ᵣ
  absᵣ (y -ᵣ x)
clampDistᵣ lower upper x y =
  subst2 _≤ᵣ_
    (sym (abs-max (clampᵣ lower upper y -ᵣ clampᵣ lower upper x)))
    (sym (abs-max (y -ᵣ x)))
    (ℝRingClamp.clampDist lower upper x y)


opaque
  clampDistᵣ-rat : ∀ L L' x y →
    absᵣ (clampᵣ (rat L) (rat L') y -ᵣ clampᵣ (rat L) (rat L') x)
      ≤ᵣ absᵣ (y -ᵣ x)
  clampDistᵣ-rat L L' = clampDistᵣ (rat L) (rat L')

  -- Compatibility name retained for existing inverse-module consumers.
  clampDistᵣ' : ∀ L L' x y →
    absᵣ (clampᵣ (rat L) (rat L') y -ᵣ clampᵣ (rat L) (rat L') x)
      ≤ᵣ absᵣ (y -ᵣ x)
  clampDistᵣ' = clampDistᵣ-rat
