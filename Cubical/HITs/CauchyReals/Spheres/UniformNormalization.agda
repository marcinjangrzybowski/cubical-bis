module Cubical.HITs.CauchyReals.Spheres.UniformNormalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Foundations.Powerset
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (absᵣPos)
open import Cubical.HITs.CauchyReals.Algebra.Inverse using (invℝ₊; invℝ₊-≤-invℝ₊)
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base using (root)
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core using (uContRoot; ₙ√-Monotone)
open import Cubical.HITs.CauchyReals.ArcSin.Positive.Core using (invℝ₊UC)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Predicate using (IsUContinuousℙ→ℝSubspaceUC)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.HITs.CauchyReals.Spheres.Normalization
open CategoryStructures using (_∘UC_)

CoordinateBound : (n : ℕ) → ℝ → fst (Euclidean n) → Type
CoordinateBound zero B x = Unit
CoordinateBound (suc zero) B x = absᵣ x ≤ᵣ B
CoordinateBound (suc (suc n)) B (x , xs) =
  (absᵣ x ≤ᵣ B) × CoordinateBound (suc n) B xs

private
  intoSubspaceUC : ∀ {ℓ ℓ' ℓN ℓN'} {M : PremetricSpace ℓ ℓ'} {N : PremetricSpace ℓN ℓN'}
    (P : ℙ (fst N)) (f : UC[ M , N ]) → (∀ x → fst f x ∈ P) →
    UC[ M , PremetricSubspace N P ]
  fst (intoSubspaceUC P f bounds) x = fst f x , bounds x
  snd (intoSubspaceUC P f bounds) = PT.map
    (λ (μ , c) → μ , isuniformlycontinuouswith (IsUniformlyContinuousWith.pres≈ c)) (snd f)

  inverseAboveUC : (c : ℝ₊) →
    UC[ PremetricSubspace ℝPremetricSpace (pred≥ (fst c)) , ℝPremetricSpace ]
  fst (inverseAboveUC c) (x , lower) =
    fst (invℝ₊ (x , isTrans<≤ᵣ _ _ _ (snd c) lower))
  snd (inverseAboveUC c) = PT.rec squash₁
    (λ uc → snd (IsUContinuousℙ→ℝSubspaceUC (pred≥ (fst c)) _ uc))
    (invℝ₊UC (fst c) (snd c))

module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  boundedNorm²UC : (n : ℕ) (f : UC[ M , Euclidean n ]) (B : ℝ₊) →
    (∀ x → CoordinateBound n (fst B) (fst f x)) → UC[ M , ℝPremetricSpace ]
  boundedNorm²UC zero f B bound = constantUC 0
  boundedNorm²UC (suc zero) f B bound = boundedMultiplyUC f f B B bound bound
  boundedNorm²UC (suc (suc n)) f B bound = addRealUC
    (boundedMultiplyUC (productFstUC ∘UC f) (productFstUC ∘UC f) B B
      (λ x → fst (bound x)) (λ x → fst (bound x)))
    (boundedNorm²UC (suc n) (productSndUC ∘UC f) B (λ x → snd (bound x)))

  boundedNorm²UC-β : (n : ℕ) (f : UC[ M , Euclidean n ]) (B : ℝ₊)
    (bound : ∀ x → CoordinateBound n (fst B) (fst f x)) (x : fst M) →
    fst (boundedNorm²UC n f B bound) x ≡ norm² n (fst f x)
  boundedNorm²UC-β zero f B bound x = refl
  boundedNorm²UC-β (suc zero) f B bound x = refl
  boundedNorm²UC-β (suc (suc n)) f B bound x =
    cong (fst (fst f x) ·ᵣ fst (fst f x) +ᵣ_)
      (boundedNorm²UC-β (suc n) (productSndUC ∘UC f) B (λ x → snd (bound x)) x)

  boundedScaleUC : (n : ℕ) (a : UC[ M , ℝPremetricSpace ]) (f : UC[ M , Euclidean n ])
    (A B : ℝ₊) → (∀ x → absᵣ (fst a x) ≤ᵣ fst A) →
    (∀ x → CoordinateBound n (fst B) (fst f x)) → UC[ M , Euclidean n ]
  boundedScaleUC zero a f A B a-bound f-bound = constantUC tt
  boundedScaleUC (suc zero) a f A B a-bound f-bound =
    boundedMultiplyUC a f A B a-bound f-bound
  boundedScaleUC (suc (suc n)) a f A B a-bound f-bound = pairUC
    (boundedMultiplyUC a (productFstUC ∘UC f) A B a-bound (λ x → fst (f-bound x)))
    (boundedScaleUC (suc n) a (productSndUC ∘UC f) A B a-bound (λ x → snd (f-bound x)))

  boundedScaleUC-β : (n : ℕ) (a : UC[ M , ℝPremetricSpace ]) (f : UC[ M , Euclidean n ])
    (A B : ℝ₊) (a-bound : ∀ x → absᵣ (fst a x) ≤ᵣ fst A)
    (f-bound : ∀ x → CoordinateBound n (fst B) (fst f x)) (x : fst M) →
    fst (boundedScaleUC n a f A B a-bound f-bound) x ≡ scale n (fst a x) (fst f x)
  boundedScaleUC-β zero a f A B a-bound f-bound x = refl
  boundedScaleUC-β (suc zero) a f A B a-bound f-bound x = refl
  boundedScaleUC-β (suc (suc n)) a f A B a-bound f-bound x =
    cong (fst a x ·ᵣ fst (fst f x) ,_)
      (boundedScaleUC-β (suc n) a (productSndUC ∘UC f) A B a-bound
        (λ x → snd (f-bound x)) x)

  -- A compositional UC proof on bounded vectors bounded away from zero.
  -- No sharp Euclidean Lipschitz estimate is assumed.
  module BoundedNormalization (m : ℕ) (f : UC[ M , Euclidean (suc m) ]) (B c : ℝ₊)
    (bound : ∀ x → CoordinateBound (suc m) (fst B) (fst f x))
    (lower : ∀ x → fst c ≤ᵣ norm² (suc m) (fst f x)) where

    positive : ∀ x → 0 <ᵣ norm² (suc m) (fst f x)
    positive x = isTrans<≤ᵣ _ _ _ (snd c) (lower x)

    private
      squared : UC[ M , ℝPremetricSpace ]
      squared = boundedNorm²UC (suc m) f B bound

      squared-β : ∀ x → fst squared x ≡ norm² (suc m) (fst f x)
      squared-β = boundedNorm²UC-β (suc m) f B bound

      positiveSquared : UC[ M , PremetricSubspace ℝPremetricSpace (pred> 0) ]
      positiveSquared = intoSubspaceUC (pred> 0) squared
        (λ x → subst (0 <ᵣ_) (sym (squared-β x)) (positive x))

      length : UC[ M , ℝPremetricSpace ]
      length = IsUContinuousℙ→ℝSubspaceUC (pred> 0) _ (uContRoot 2) ∘UC positiveSquared

      length-β : ∀ x → fst length x ≡ fst (positiveLength (suc m) (fst f x) (positive x))
      length-β x = cong (λ z → fst (root 2 z)) (ℝ₊≡ (squared-β x))

      length-lower : ∀ x → fst (root 2 c) ≤ᵣ fst length x
      length-lower x = subst (fst (root 2 c) ≤ᵣ_) (sym (length-β x))
        (ₙ√-Monotone 2 (lower x))

      factor : UC[ M , ℝPremetricSpace ]
      factor = inverseAboveUC (root 2 c) ∘UC
        intoSubspaceUC (pred≥ (fst (root 2 c))) length length-lower

      factor-β : ∀ x → fst factor x ≡ inverseLength (suc m) (fst f x) (positive x)
      factor-β x = cong (λ z → fst (invℝ₊ z)) (ℝ₊≡ (length-β x))

      factor-bound : ∀ x → absᵣ (fst factor x) ≤ᵣ fst (invℝ₊ (root 2 c))
      factor-bound x = isTrans≡≤ᵣ _ _ _
        (absᵣPos _ (snd (invℝ₊ (fst length x , isTrans<≤ᵣ _ _ _ (snd (root 2 c)) (length-lower x)))))
        (invEq (invℝ₊-≤-invℝ₊ _ _) (length-lower x))

      scaled : UC[ M , Euclidean (suc m) ]
      scaled = boundedScaleUC (suc m) factor f (invℝ₊ (root 2 c)) B factor-bound bound

      scaled-β : ∀ x → fst scaled x ≡ normalizeCoordinates (suc m) (fst f x) (positive x)
      scaled-β x = boundedScaleUC-β (suc m) factor f (invℝ₊ (root 2 c)) B factor-bound bound x ∙
        cong (λ a → scale (suc m) a (fst f x)) (factor-β x)

    normalizeUC : UC[ M , RealSphereSpace m ]
    fst normalizeUC x = normalize m (fst f x) (positive x)
    snd normalizeUC = PT.map (λ (μ , uc) → μ , isuniformlycontinuouswith
      (λ x y ε close → subst2 (λ u v → PremetricStr._≈[_]_ (snd (Euclidean (suc m))) u ε v)
        (scaled-β x) (scaled-β y) (IsUniformlyContinuousWith.pres≈ uc x y ε close))) (snd scaled)
