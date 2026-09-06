module Cubical.HITs.CauchyReals.Circle.Homotopy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos; isSetℤ)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ using (eq/)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊; [_/_]₊)
import Cubical.HITs.CauchyReals.Foundation.Rationals as QR
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Invariance
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.OrderedReflection
open CategoryStructures using (_∘UC_)

CircleMap : Type
CircleMap = UC[ CirclePremetricSpace , CirclePremetricSpace ]

CircleCylinder : PremetricSpace ℓ-zero ℓ-zero
CircleCylinder = PremetricProduct ℝPremetricSpace CirclePremetricSpace

-- The real parameter runs from 0 to 1. Using all of ℝ permits constant
-- extension by clamping, and makes finite pasting convenient.
UniformHomotopy : CircleMap → CircleMap → Type
UniformHomotopy f g = Σ[ H ∈ UC[ CircleCylinder , CirclePremetricSpace ] ]
  (∀ x → fst H (0 , x) ≡ fst f x) × (∀ x → fst H (1 , x) ≡ fst g x)

opaque
  slice : UC[ CircleCylinder , CirclePremetricSpace ] → ℝ → CircleMap
  slice H t = H ∘UC leftInsertionUC ℝPremetricSpace CirclePremetricSpace t

  slice-β : (H : UC[ CircleCylinder , CirclePremetricSpace ]) → ∀ t x →
    fst (slice H t) x ≡ fst H (t , x)
  slice-β H t x = refl

private
  module C = PremetricStr (snd CirclePremetricSpace)

windingNumber-close : (f g : CircleMap) →
  (∀ x → fst f x C.≈[ comparison-radius ] fst g x) → windingNumber f ≡ windingNumber g
windingNumber-close f g close = windingLoop-close
  (Circle→distCircleUC ∘UC (f ∘UC injCircleUC))
  (Circle→distCircleUC ∘UC (g ∘UC injCircleUC))
  (cong (Circle→distCircle ∘ fst f) (eq/ 0 1 (-1 , -ᵣ-rat₂ 0 1)))
  (cong (Circle→distCircle ∘ fst g) (eq/ 0 1 (-1 , -ᵣ-rat₂ 0 1)))
  (λ x → subst2 (λ p q → PremetricStr._≈[_]_ (snd distCirclePremetricSpace) p comparison-radius q)
    (β f x) (β g x) (close (injCircle x)))
  where
  β : (f : CircleMap) (x : ℝ) → Circle→distCircle (fst f (injCircle x)) ≡
    fst (Circle→distCircleUC ∘UC (f ∘UC injCircleUC)) x
  β f x = refl

private
  uniform-slices : (H : UC[ CircleCylinder , CirclePremetricSpace ]) (μ : ℚ₊ → ℚ₊) →
    IsUniformlyContinuousWith (snd CircleCylinder) (fst H) (snd CirclePremetricSpace) μ →
    ∀ t u ε → t ≈ℝ[ μ ε ] u → ∀ x → fst (slice H t) x C.≈[ ε ] fst (slice H u) x
  uniform-slices H μ uc t u ε close x =
    subst2 (λ p q → p C.≈[ ε ] q) (sym (slice-β H t x)) (sym (slice-β H u x))
      (IsUniformlyContinuousWith.pres≈ uc (t , x) (u , x) ε (close , C.isRefl≈ x (μ ε)))

  locally-constant : (k : ℚ → ℤ) (δ : ℚ₊) →
    (∀ a b → QR.abs (a ℚ.- b) ℚ.< fst δ → k a ≡ k b) → k 0 ≡ k 1
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

  opaque
    slice-winding : (H : UC[ CircleCylinder , CirclePremetricSpace ]) →
      windingNumber (slice H 0) ≡ windingNumber (slice H 1)
    slice-winding H = PT.rec (isSetℤ _ _) compare (snd H)
      where
      compare : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
        (snd CircleCylinder) (fst H) (snd CirclePremetricSpace) μ) →
        windingNumber (slice H 0) ≡ windingNumber (slice H 1)
      compare (μ , uc) = locally-constant (λ q → windingNumber (slice H (rat q)))
        (μ (comparison-radius))
        (λ a b close → windingNumber-close (slice H (rat a)) (slice H (rat b))
          (uniform-slices H μ uc (rat a) (rat b) (comparison-radius)
              (∼→≈ℝ (rat a) (rat b) (μ (comparison-radius))
                (rat-rat-fromAbs a b (μ (comparison-radius)) close))))

windingNumber-homotopy : (f g : CircleMap) →
  UniformHomotopy f g → windingNumber f ≡ windingNumber g
windingNumber-homotopy f g h =
  sym (cong windingNumber start)
  ∙ slice-winding (fst h)
  ∙ cong windingNumber end
  where
  start : slice (fst h) 0 ≡ f
  start = Σ≡Prop (λ _ → squash₁) (funExt (λ x → slice-β (fst h) 0 x ∙ fst (snd h) x))
  end : slice (fst h) 1 ≡ g
  end = Σ≡Prop (λ _ → squash₁) (funExt (λ x → slice-β (fst h) 1 x ∙ snd (snd h) x))
