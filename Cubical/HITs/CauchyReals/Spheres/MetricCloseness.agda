module Cubical.HITs.CauchyReals.Spheres.MetricCloseness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict using (≤absᵣ)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.HITs.CauchyReals.Spheres.CoordinateBounds
open import Cubical.HITs.CauchyReals.Spheres.Interpolation
open import Cubical.HITs.CauchyReals.Spheres.UniformNormalization using (CoordinateBound)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

private
  opaque
    twice-commutes : (z : ℝ) → 2 -ᵣ z ·ᵣ 2 ≡ 2 -ᵣ 2 ·ᵣ z
    twice-commutes z = ℝ!

    twice-one : 2 -ᵣ 2 ·ᵣ 1 ≡ 0
    twice-one = ℝ!

    difference-zero : (d : ℝ) → d -ᵣ 0 ≡ d
    difference-zero d = ℝ!

    near-zero-upper-bound : (d : ℝ) → d ≈ℝ[ 1 ] 0 → d ≤ᵣ 2
    near-zero-upper-bound d near-zero = isTrans≤ᵣ d 1 2
      (<ᵣWeaken≤ᵣ d 1 distance<1) decℚ≤ᵣ?
      where
      distance<1 : d <ᵣ 1
      distance<1 = isTrans≤<ᵣ d (absᵣ d) 1 (≤absᵣ d)
        (isTrans≡<ᵣ (absᵣ d) (absᵣ (d -ᵣ 0)) 1
          (sym (cong absᵣ (difference-zero d)))
          (fst (∼≃abs<ε d 0 1) (≈ℝ→∼ d 0 1 near-zero)))

  module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
    dotUC : (n : ℕ) (f g : UC[ M , Euclidean n ]) →
      (∀ u → CoordinateBound n 1 (fst f u)) →
      (∀ u → CoordinateBound n 1 (fst g u)) → UC[ M , ℝPremetricSpace ]
    dotUC zero f g f-bound g-bound = constantUC 0
    dotUC (suc zero) f g f-bound g-bound = boundedMultiplyUC f g 1 1 f-bound g-bound
    dotUC (suc (suc n)) f g f-bound g-bound = addRealUC
      (boundedMultiplyUC (productFstUC ∘UC f) (productFstUC ∘UC g) 1 1
        (λ u → fst (f-bound u)) (λ u → fst (g-bound u)))
      (dotUC (suc n) (productSndUC ∘UC f) (productSndUC ∘UC g)
        (λ u → snd (f-bound u)) (λ u → snd (g-bound u)))

    dotUC-β : (n : ℕ) (f g : UC[ M , Euclidean n ])
      (f-bound : ∀ u → CoordinateBound n 1 (fst f u))
      (g-bound : ∀ u → CoordinateBound n 1 (fst g u)) (u : fst M) →
      fst (dotUC n f g f-bound g-bound) u ≡ dot n (fst f u) (fst g u)
    dotUC-β zero f g f-bound g-bound u = refl
    dotUC-β (suc zero) f g f-bound g-bound u = refl
    dotUC-β (suc (suc n)) f g f-bound g-bound u =
      cong (fst (fst f u) ·ᵣ fst (fst g u) +ᵣ_)
        (dotUC-β (suc n) (productSndUC ∘UC f) (productSndUC ∘UC g)
          (λ u → snd (f-bound u)) (λ u → snd (g-bound u)) u)

module SphereCloseness (m : ℕ) where
  private
    S : PremetricSpace ℓ-zero ℓ-zero
    S = RealSphereSpace m
    module PS = PremetricStr (snd S)

    inclusion : UC[ S , Euclidean (suc m) ]
    inclusion = subspaceInclusionUC (Euclidean (suc m))
      (λ x → (norm² (suc m) x ≡ 1) , isSetℝ _ _)

    left right : UC[ PremetricProduct S S , Euclidean (suc m) ]
    left = inclusion ∘UC productFstUC
    right = inclusion ∘UC productSndUC

    left-bound : ∀ u → CoordinateBound (suc m) 1 (fst left u)
    left-bound u = sphere-coordinate-bound m (fst u)

    right-bound : ∀ u → CoordinateBound (suc m) 1 (fst right u)
    right-bound u = sphere-coordinate-bound m (snd u)

    opaque
      raw : UC[ PremetricProduct S S , ℝPremetricSpace ]
      raw = subRealUC (constantUC 2) (scaleUC 2 ∘UC dotUC (suc m) left right left-bound right-bound)

      raw-β : (x y : RealSphere m) → fst raw (x , y) ≡ squaredDistance (suc m) (fst x) (fst y)
      raw-β x y = cong (λ z → 2 -ᵣ z ·ᵣ 2)
        (dotUC-β (suc m) left right left-bound right-bound (x , y)) ∙
        twice-commutes (dot (suc m) (fst x) (fst y)) ∙ sym (squaredDistance-sphere m x y)

  -- Bounded coordinate multiplication gives a modulus on the entire
  -- product of spheres, not a separate modulus at each diagonal point.
  squaredDistanceUC : UC[ PremetricProduct S S , ℝPremetricSpace ]
  fst squaredDistanceUC (x , y) = squaredDistance (suc m) (fst x) (fst y)
  snd squaredDistanceUC = subst
    (λ f → isUniformlyContinuous (snd (PremetricProduct S S)) f (snd ℝPremetricSpace))
    (funExt (λ (x , y) → raw-β x y)) (snd raw)

  squaredDistance-diagonal : (x : RealSphere m) → squaredDistance (suc m) (fst x) (fst x) ≡ 0
  squaredDistance-diagonal x = squaredDistance-sphere m x x ∙
    cong (λ z → 2 -ᵣ 2 ·ᵣ z) (dot-self (suc m) (fst x) ∙ snd x) ∙ twice-one

  SafeRadius : ℚ₊ → Type
  SafeRadius δ = (x y : RealSphere m) → x PS.≈[ δ ] y →
    squaredDistance (suc m) (fst x) (fst y) ≤ᵣ 2

  -- One merely existing radius works everywhere on this sphere.
  -- Only one value of one existing UC modulus is used; no choice is added.
  safeRadius : ∥ Σ[ δ ∈ ℚ₊ ] SafeRadius δ ∥₁
  safeRadius = PT.map build (snd raw)
    where
    build : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd (PremetricProduct S S)) (fst raw) (snd ℝPremetricSpace) μ) →
      Σ[ δ ∈ ℚ₊ ] SafeRadius δ
    build (μ , uc) = μ 1 , safe
      where
      safe : SafeRadius (μ 1)
      safe x y close = near-zero-upper-bound d near-zero
        where
        d : ℝ
        d = squaredDistance (suc m) (fst x) (fst y)

        near-zero : d ≈ℝ[ 1 ] 0
        near-zero = subst2 (λ a b → a ≈ℝ[ 1 ] b)
          (raw-β x y) (raw-β x x ∙ squaredDistance-diagonal x)
          (IsUniformlyContinuousWith.pres≈
            {M = snd (PremetricProduct S S)} {f = fst raw} {N = snd ℝPremetricSpace} {μ = μ}
            uc (x , y) (x , x) 1
            (PS.isRefl≈ x (μ 1) , PS.isSym≈ x y (μ 1) close))
