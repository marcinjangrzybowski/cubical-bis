module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  half-sum : (ε : ℚ₊) → fst ((ε /2₊) +₊ (ε /2₊)) ≡ fst ε
  half-sum ε = ℚ!

module _ {ℓ ℓ'} {X : PremetricSpace ℓ ℓ'} where
  private
    module P = PremetricStr (snd X)
    module R = PremetricStr (snd ℝPremetricSpace)

  -- Continuity and separatedness extend equations from rational arguments.
  real-ext : (f g : UC[ ℝPremetricSpace , X ]) →
    (∀ q → fst f (rat q) ≡ fst g (rat q)) → ∀ t → fst f t ≡ fst g t
  real-ext f g same = Elimℝ-Prop.go induction
    where
    induction : Elimℝ-Prop (λ t → fst f t ≡ fst g t)
    Elimℝ-Prop.ratA induction = same
    Elimℝ-Prop.isPropA induction _ = P.isSetM _ _
    Elimℝ-Prop.limA induction s sc equal = P.isSeparated≈ _ _ λ ε →
      PT.rec2 (P.isProp≈ _ _ ε) (compare ε) (snd f) (snd g)
      where
      compare : (ε : ℚ₊) →
        (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd ℝPremetricSpace) (fst f) (snd X) μ) →
        (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd ℝPremetricSpace) (fst g) (snd X) ν) →
        fst f (lim s sc) P.≈[ ε ] fst g (lim s sc)
      compare ε (μ , fc) (ν , gc) = P.subst≈ _ _ {ε = (ε /2₊) +₊ (ε /2₊)} {ε' = ε} (half-sum ε)
        (P.isTriangular≈ (fst f (lim s sc)) (fst g (s δ)) (fst g (lim s sc)) (ε /2₊) (ε /2₊)
          (subst (fst f (lim s sc) P.≈[ ε /2₊ ]_) (equal δ) first)
          (P.isSym≈ (fst g (lim s sc)) (fst g (s δ)) (ε /2₊) second))
        where
        κ : ℚ₊
        κ = min₊ (μ (ε /2₊)) (ν (ε /2₊))
        δ : ℚ₊
        δ = κ /2₊
        near : lim s sc ∼[ δ +₊ δ ] s δ
        near = sym∼ _ _ _ (𝕣-lim-self s sc δ δ)
        nearMetric : lim s sc ≈ℝ[ κ ] s δ
        nearMetric = R.subst≈ (lim s sc) (s δ) {ε = δ +₊ δ} {ε' = κ} (half-sum κ)
          (∼→≈ℝ (lim s sc) (s δ) (δ +₊ δ) near)
        first : fst f (lim s sc) P.≈[ ε /2₊ ] fst f (s δ)
        first = IsUniformlyContinuousWith.pres≈ fc (lim s sc) (s δ) (ε /2₊)
          (R.isMonotone≈≤ (lim s sc) (s δ) κ (μ (ε /2₊))
            (min₊≤L (μ (ε /2₊)) (ν (ε /2₊))) nearMetric)
        second : fst g (lim s sc) P.≈[ ε /2₊ ] fst g (s δ)
        second = IsUniformlyContinuousWith.pres≈ gc (lim s sc) (s δ) (ε /2₊)
          (R.isMonotone≈≤ (lim s sc) (s δ) κ (ν (ε /2₊))
            (min₊≤R (μ (ε /2₊)) (ν (ε /2₊))) nearMetric)

  real-split : (m : ℚ) (f g : UC[ ℝPremetricSpace , X ]) →
    (∀ t → t ≤ᵣ rat m → fst f t ≡ fst g t) →
    (∀ t → rat m ≤ᵣ t → fst f t ≡ fst g t) → ∀ t → fst f t ≡ fst g t
  real-split m f g left right = real-ext f g λ q → PT.rec (P.isSetM _ _)
    (λ { (inl qm) → left (rat q) (≤ℚ→≤ᵣ q m qm)
       ; (inr mq) → right (rat q) (≤ℚ→≤ᵣ m q mq) }) (ℚ.isTotal≤ q m)
