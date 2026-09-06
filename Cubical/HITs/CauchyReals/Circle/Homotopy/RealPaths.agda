module Cubical.HITs.CauchyReals.Circle.Homotopy.RealPaths where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice
open import Cubical.HITs.CauchyReals.Analysis.Uniform using (clampᵣ∼)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core using (IsContinuous; ≡Continuous)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

RealPath : Type
RealPath = UC[ ℝPremetricSpace , ℝPremetricSpace ]

CirclePath : Type
CirclePath = UC[ ℝPremetricSpace , distCirclePremetricSpace ]

clampUC : ℝ → ℝ → RealPath
clampUC a b = IsUContinuous→ℝUC (clampᵣ a b)
  (λ ε → ε , λ x y → clampᵣ∼)

negateRealUC : RealPath
negateRealUC = IsUContinuous→ℝUC -ᵣ_
  (λ ε → ε , λ x y → -ᵣ-nonExpanding x y ε)

module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  private
    module P = PremetricStr (snd M)

  addRealUC : (f g : UC[ M , ℝPremetricSpace ]) → UC[ M , ℝPremetricSpace ]
  addRealUC f g = (λ x → fst f x +ᵣ fst g x) , PT.map2 combine (snd f) (snd g)
    where
    combine :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M) (fst f) (snd ℝPremetricSpace) μ) →
      (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M) (fst g) (snd ℝPremetricSpace) ν) →
      Σ[ κ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M)
        (λ x → fst f x +ᵣ fst g x) (snd ℝPremetricSpace) κ
    combine (μ , fc) (ν , gc) = (λ ε → min₊ (μ (ε /2₊)) (ν (ε /2₊))) , preserves
      where
      preserves : IsUniformlyContinuousWith (snd M)
        (λ x → fst f x +ᵣ fst g x) (snd ℝPremetricSpace)
        (λ ε → min₊ (μ (ε /2₊)) (ν (ε /2₊)))
      IsUniformlyContinuousWith.pres≈ preserves x y ε close = ∼→≈ℝ _ _ ε
        (subst∼ {0<ε = snd ((ε /2₊) +₊ (ε /2₊))} {0<ε' = snd ε} ℚ!
          (+ᵣ-ne₂ (ε /2₊) (ε /2₊)
            (≈ℝ→∼ _ _ (ε /2₊) (IsUniformlyContinuousWith.pres≈ fc x y (ε /2₊)
              (P.isMonotone≈≤ x y _ _ (min₊≤L (μ (ε /2₊)) (ν (ε /2₊))) close)))
            (≈ℝ→∼ _ _ (ε /2₊) (IsUniformlyContinuousWith.pres≈ gc x y (ε /2₊)
              (P.isMonotone≈≤ x y _ _ (min₊≤R (μ (ε /2₊)) (ν (ε /2₊))) close)))))

  subRealUC : (f g : UC[ M , ℝPremetricSpace ]) → UC[ M , ℝPremetricSpace ]
  subRealUC f g = addRealUC f (negateRealUC ∘UC g)

realPath-continuous : (f : RealPath) → IsContinuous (fst f)
realPath-continuous f x ε = PT.map
  (λ (μ , fc) → μ ε , λ y xy → ≈ℝ→∼ _ _ ε
    (IsUniformlyContinuousWith.pres≈ fc x y ε (∼→≈ℝ _ _ (μ ε) xy))) (snd f)

realPath-ext : (f g : RealPath) → (∀ q → fst f (rat q) ≡ fst g (rat q)) →
  ∀ x → fst f x ≡ fst g x
realPath-ext f g = ≡Continuous (fst f) (fst g) (realPath-continuous f) (realPath-continuous g)

circlePath-ext : (f g : CirclePath) → (∀ q → fst f (rat q) ≡ fst g (rat q)) →
  ∀ x → fst f x ≡ fst g x
circlePath-ext f g same x = distCircle≡
  (realPath-ext (productFstUC ∘UC (distCircleInclusionUC ∘UC f))
    (productFstUC ∘UC (distCircleInclusionUC ∘UC g)) (λ q → cong (fst ∘ fst) (same q)) x)
  (realPath-ext (productSndUC ∘UC (distCircleInclusionUC ∘UC f))
    (productSndUC ∘UC (distCircleInclusionUC ∘UC g)) (λ q → cong (snd ∘ fst) (same q)) x)

-- Rational case splitting, followed by continuity, suffices for pasting
-- equations. This is not a decision procedure for the order of reals.
realPath-split : (m : ℚ) (f g : RealPath) →
  (∀ x → x ≤ᵣ rat m → fst f x ≡ fst g x) →
  (∀ x → rat m ≤ᵣ x → fst f x ≡ fst g x) → ∀ x → fst f x ≡ fst g x
realPath-split m f g left right = realPath-ext f g λ q →
  PT.rec (isSetℝ _ _)
    (λ { (inl qm) → left (rat q) (≤ℚ→≤ᵣ q m qm)
       ; (inr mq) → right (rat q) (≤ℚ→≤ᵣ m q mq) }) (ℚ.isTotal≤ q m)

circlePath-split : (m : ℚ) (f g : CirclePath) →
  (∀ x → x ≤ᵣ rat m → fst f x ≡ fst g x) →
  (∀ x → rat m ≤ᵣ x → fst f x ≡ fst g x) → ∀ x → fst f x ≡ fst g x
circlePath-split m f g left right = circlePath-ext f g λ q →
  PT.rec (isSetDistCircle _ _)
    (λ { (inl qm) → left (rat q) (≤ℚ→≤ᵣ q m qm)
       ; (inr mq) → right (rat q) (≤ℚ→≤ᵣ m q mq) }) (ℚ.isTotal≤ q m)

circlePath-ext-interval : (a b : ℚ) → a ℚ.≤ b → (f g : CirclePath) →
  (∀ q → a ℚ.≤ q → q ℚ.≤ b → fst f (rat q) ≡ fst g (rat q)) →
  ∀ x → rat a ≤ᵣ x → x ≤ᵣ rat b → fst f x ≡ fst g x
circlePath-ext-interval a b ab f g same x ax xb =
  cong (fst f) (∈ℚintervalℙ→clampᵣ≡ (rat a) (rat b) x (ax , xb))
  ∙ circlePath-ext (f ∘UC clampUC (rat a) (rat b)) (g ∘UC clampUC (rat a) (rat b))
    (λ q → cong (fst f) (clampᵣ-rat a b q)
      ∙ same (ℚ.clamp a b q)
        (≤ᵣ→≤ℚ a (ℚ.clamp a b q)
          (subst (rat a ≤ᵣ_) (clampᵣ-rat a b q) (≤clampᵣ (rat a) (rat b) (rat q) (≤ℚ→≤ᵣ a b ab))))
        (≤ᵣ→≤ℚ (ℚ.clamp a b q) b
          (subst (_≤ᵣ rat b) (clampᵣ-rat a b q) (clamp≤ᵣ (rat a) (rat b) (rat q))))
      ∙ cong (fst g) (sym (clampᵣ-rat a b q))) x
  ∙ cong (fst g) (sym (∈ℚintervalℙ→clampᵣ≡ (rat a) (rat b) x (ax , xb)))

opaque
  clamp-left : ∀ a m b x → a ≤ᵣ m → m ≤ᵣ b → x ≤ᵣ m →
    clampᵣ a m x ≡ clampᵣ a b x
  clamp-left a m b x am mb xm = ≤→minᵣ (maxᵣ a x) m (max≤-lem a x m am xm)
    ∙ sym (≤→minᵣ (maxᵣ a x) b
      (isTrans≤ᵣ _ m b (max≤-lem a x m am xm) mb))

  clamp-right : ∀ a m b x → a ≤ᵣ m → m ≤ᵣ b → m ≤ᵣ x →
    clampᵣ m b x ≡ clampᵣ a b x
  clamp-right a m b x am mb mx = cong (λ z → minᵣ z b)
    (≤ᵣ→≡ mx ∙ sym (≤ᵣ→≡ (isTrans≤ᵣ a m x am mx)))
