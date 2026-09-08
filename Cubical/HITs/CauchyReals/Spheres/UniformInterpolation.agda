module Cubical.HITs.CauchyReals.Spheres.UniformInterpolation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using
  (Interval; 𝟘; 𝟙; coordinateUC; reverseTime; reverseTimeUC; interval-bound)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.HITs.CauchyReals.Spheres.CoordinateBounds
open import Cubical.HITs.CauchyReals.Spheres.Interpolation
open import Cubical.HITs.CauchyReals.Spheres.Normalization
open import Cubical.HITs.CauchyReals.Spheres.UniformNormalization
open CategoryStructures using (_∘UC_)

module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  coordinateBlendUC : (n : ℕ) (t : UC[ M , Interval ]) (f g : UC[ M , Euclidean n ]) →
    (∀ u → CoordinateBound n 1 (fst f u)) →
    (∀ u → CoordinateBound n 1 (fst g u)) → UC[ M , Euclidean n ]
  coordinateBlendUC zero t f g f-bound g-bound = constantUC tt
  coordinateBlendUC (suc zero) t f g f-bound g-bound = addRealUC
    (boundedMultiplyUC (coordinateUC ∘UC (reverseTimeUC ∘UC t)) f 1 1
      (λ u → interval-bound (reverseTime (fst t u))) f-bound)
    (boundedMultiplyUC (coordinateUC ∘UC t) g 1 1
      (λ u → interval-bound (fst t u)) g-bound)
  coordinateBlendUC (suc (suc n)) t f g f-bound g-bound = pairUC
    (coordinateBlendUC 1 t (productFstUC ∘UC f) (productFstUC ∘UC g)
      (λ u → fst (f-bound u)) (λ u → fst (g-bound u)))
    (coordinateBlendUC (suc n) t (productSndUC ∘UC f) (productSndUC ∘UC g)
      (λ u → snd (f-bound u)) (λ u → snd (g-bound u)))

  coordinateBlendUC-β : (n : ℕ) (t : UC[ M , Interval ]) (f g : UC[ M , Euclidean n ])
    (f-bound : ∀ u → CoordinateBound n 1 (fst f u))
    (g-bound : ∀ u → CoordinateBound n 1 (fst g u)) (u : fst M) →
    fst (coordinateBlendUC n t f g f-bound g-bound) u ≡ blend n (fst (fst t u)) (fst f u) (fst g u)
  coordinateBlendUC-β zero t f g f-bound g-bound u = refl
  coordinateBlendUC-β (suc zero) t f g f-bound g-bound u = refl
  coordinateBlendUC-β (suc (suc n)) t f g f-bound g-bound u = cong
    ((1 -ᵣ fst (fst t u)) ·ᵣ fst (fst f u) +ᵣ fst (fst t u) ·ᵣ fst (fst g u) ,_)
    (coordinateBlendUC-β (suc n) t (productSndUC ∘UC f) (productSndUC ∘UC g)
      (λ u → snd (f-bound u)) (λ u → snd (g-bound u)) u)

private
  normalize-equal-sphere : (m : ℕ) (v : fst (Euclidean (suc m)))
    (positive : 0 <ᵣ norm² (suc m) v) (x : RealSphere m) → fst x ≡ v → normalize m v positive ≡ x
  normalize-equal-sphere m v positive x same =
    subst (λ v → (p : 0 <ᵣ norm² (suc m) v) → normalize m v p ≡ x)
      same (normalize-fixes-sphere m x) positive

-- Parameters may themselves form a product or a rounded uniform mapping
-- space. This packages one jointly UC operation, not just pointwise paths.
module SphereInterpolation {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} (m : ℕ)
  (t : UC[ M , Interval ]) (f g : UC[ M , RealSphereSpace m ])
  (nonnegative : ∀ u → 0 ≤ᵣ dot (suc m) (fst (fst f u)) (fst (fst g u))) where

  private
    inclusion : UC[ RealSphereSpace m , Euclidean (suc m) ]
    inclusion = subspaceInclusionUC (Euclidean (suc m)) (λ x → (norm² (suc m) x ≡ 1) , isSetℝ _ _)

    raw : UC[ M , Euclidean (suc m) ]
    raw = coordinateBlendUC (suc m) t (inclusion ∘UC f) (inclusion ∘UC g)
      (λ u → sphere-coordinate-bound m (fst f u)) (λ u → sphere-coordinate-bound m (fst g u))

    raw-β : ∀ u → fst raw u ≡ blend (suc m) (fst (fst t u)) (fst (fst f u)) (fst (fst g u))
    raw-β = coordinateBlendUC-β (suc m) t (inclusion ∘UC f) (inclusion ∘UC g)
      (λ u → sphere-coordinate-bound m (fst f u)) (λ u → sphere-coordinate-bound m (fst g u))

    bound : ∀ u → CoordinateBound (suc m) 1 (fst raw u)
    bound u = subst (CoordinateBound (suc m) 1) (sym (raw-β u))
      (blend-coordinate-bound (suc m) (fst t u) _ _
        (sphere-coordinate-bound m (fst f u)) (sphere-coordinate-bound m (fst g u)))

    lower-bound : ∀ u → rat [ 1 / 2 ] ≤ᵣ norm² (suc m) (fst raw u)
    lower-bound u = subst (λ v → rat [ 1 / 2 ] ≤ᵣ norm² (suc m) v) (sym (raw-β u))
      (norm²-blend-lower-bound m (fst t u) (fst f u) (fst g u) (nonnegative u))

    module N = BoundedNormalization m raw 1 (rat [ 1 / 2 ] , decℚ<ᵣ?) bound lower-bound

  interpolateUC : UC[ M , RealSphereSpace m ]
  interpolateUC = N.normalizeUC

  interpolate-start : ∀ u → fst t u ≡ 𝟘 → fst interpolateUC u ≡ fst f u
  interpolate-start u at0 = normalize-equal-sphere m _ (N.positive u) (fst f u)
    (sym (raw-β u ∙ cong (λ s → blend (suc m) (fst s) _ _) at0 ∙ blend-start (suc m) _ _))

  interpolate-end : ∀ u → fst t u ≡ 𝟙 → fst interpolateUC u ≡ fst g u
  interpolate-end u at1 = normalize-equal-sphere m _ (N.positive u) (fst g u)
    (sym (raw-β u ∙ cong (λ s → blend (suc m) (fst s) _ _) at1 ∙ blend-end (suc m) _ _))

  interpolate-same : ∀ u → fst f u ≡ fst g u → fst interpolateUC u ≡ fst f u
  interpolate-same u same = normalize-equal-sphere m _ (N.positive u) (fst f u)
    (sym (raw-β u ∙ cong (λ y → blend (suc m) (fst (fst t u)) _ y) (sym (cong fst same)) ∙
      blend-same (suc m) (fst (fst t u)) _))
