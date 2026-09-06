module Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Invariance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos; isSetℤ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Invariance using (comparison-radius; windingLoop-close)
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Base
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open CategoryStructures using (_∘UC_)

private
  RealSquare = PremetricProduct ℝPremetricSpace ℝPremetricSpace
  module R = PremetricStr (snd ℝPremetricSpace)
  module D = PremetricStr (snd distCirclePremetricSpace)

  opaque
    slice : UC[ RealSquare , distCirclePremetricSpace ] → ℝ → UC[ ℝPremetricSpace , distCirclePremetricSpace ]
    slice H s = H ∘UC leftInsertionUC ℝPremetricSpace ℝPremetricSpace s

    slice-β : ∀ H s t → fst (slice H s) t ≡ fst H (s , t)
    slice-β H s t = refl

  uniform-slices : (H : UC[ RealSquare , distCirclePremetricSpace ]) (μ : ℚ₊ → ℚ₊) →
    IsUniformlyContinuousWith (snd RealSquare) (fst H) (snd distCirclePremetricSpace) μ →
    ∀ s u ε → s ≈ℝ[ μ ε ] u → ∀ t → fst (slice H s) t D.≈[ ε ] fst (slice H u) t
  uniform-slices H μ hc s u ε close t = subst2 (λ a b → a D.≈[ ε ] b)
    (sym (slice-β H s t)) (sym (slice-β H u t))
    (IsUniformlyContinuousWith.pres≈ hc (s , t) (u , t) ε (close , R.isRefl≈ t (μ ε)))

  -- A finite dyadic chain replaces any connectedness or choice axiom.
  locally-constant : (k : ℚ → ℤ) (δ : ℚ₊) →
    (∀ a b → abs (a ℚ.- b) ℚ.< fst δ → k a ≡ k b) → k 0 ≡ k 1
  locally-constant k δ close = chain n 0 1 unit-order bound
    where
    n : ℕ
    n = fst (ℚ.1/2ⁿ<ε δ)
    bound : mesh n 0 1 ℚ.< fst δ
    bound = subst (ℚ._< fst δ) (sym (ℚ.·IdL _)) (snd (ℚ.1/2ⁿ<ε δ))
    chain : ∀ n a b → a ℚ.≤ b → mesh n a b ℚ.< fst δ → k a ≡ k b
    chain zero a b a≤b bound = close a b
      (ℚ.isTrans≤< _ (b ℚ.- a) _
        (ℚ.absFrom≤×≤ (b ℚ.- a) (a ℚ.- b) <≤ℚ! <≤ℚ![ a≤b ])
        (subst (ℚ._< fst δ) (ℚ.·IdR _) bound))
    chain (suc n) a b a≤b bound =
      chain n a (mid a b) (mid-left a b a≤b)
        (subst (ℚ._< fst δ) (sym (mesh-left n a b)) bound)
      ∙ chain n (mid a b) b (mid-right a b a≤b)
        (subst (ℚ._< fst δ) (sym (mesh-right n a b)) bound)

loopWinding-homotopy : (p q : Loop) → PathHomotopy p q → loopWinding p ≡ loopWinding q
loopWinding-homotopy p q h = sym start ∙ PT.rec (isSetℤ _ _) compare (snd H) ∙ end
  where
  open PathHomotopy
  H : UC[ RealSquare , distCirclePremetricSpace ]
  H = Circle→distCircleUC ∘UC (deformation h ∘UC
    pairUC (clipUC ∘UC productFstUC) (clipUC ∘UC productSndUC))

  closes : ∀ s → fst (slice H s) 0 ≡ fst (slice H s) 1
  closes s = slice-β H s 0 ∙ cong Circle→distCircle
    ((cong (λ t → fst (deformation h) (clip s , t)) (clip-fixes 𝟘) ∙ fixes-start h (clip s))
      ∙ sym (cong (λ t → fst (deformation h) (clip s , t)) (clip-fixes 𝟙) ∙ fixes-end h (clip s)))
    ∙ sym (slice-β H s 1)

  start : windingLoop (slice H 0) (closes 0) ≡ loopWinding p
  start = windingLoop-cong (slice H 0) (extendedLoop p) (closes 0) (extended-closes p)
    (λ t → slice-β H 0 t ∙ cong Circle→distCircle
      (cong (λ s → fst (deformation h) (s , clip t)) (clip-fixes 𝟘) ∙ at-start h (clip t)))
  end : windingLoop (slice H 1) (closes 1) ≡ loopWinding q
  end = windingLoop-cong (slice H 1) (extendedLoop q) (closes 1) (extended-closes q)
    (λ t → slice-β H 1 t ∙ cong Circle→distCircle
      (cong (λ s → fst (deformation h) (s , clip t)) (clip-fixes 𝟙) ∙ at-end h (clip t)))

  compare : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
    (snd RealSquare) (fst H) (snd distCirclePremetricSpace) μ) →
    windingLoop (slice H 0) (closes 0) ≡ windingLoop (slice H 1) (closes 1)
  compare (μ , hc) = locally-constant (λ r → windingLoop (slice H (rat r)) (closes (rat r)))
    (μ comparison-radius) λ a b close → windingLoop-close
      (slice H (rat a)) (slice H (rat b)) (closes (rat a)) (closes (rat b))
      (uniform-slices H μ hc (rat a) (rat b) comparison-radius
        (∼→≈ℝ (rat a) (rat b) (μ comparison-radius)
          (rat-rat-fromAbs a b (μ comparison-radius) close)))
