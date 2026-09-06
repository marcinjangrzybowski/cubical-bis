module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.Uniform using (clampᵣ∼)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

Interval : PremetricSpace ℓ-zero ℓ-zero
Interval = PremetricSubspace ℝPremetricSpace (intervalℙ 0 1)

𝕀 : Type
𝕀 = fst Interval

𝟘 𝟙 : 𝕀
𝟘 = 0 , decℚ≤ᵣ? , decℚ≤ᵣ?
𝟙 = 1 , decℚ≤ᵣ? , decℚ≤ᵣ?

interval-ext : {s t : 𝕀} → fst s ≡ fst t → s ≡ t
interval-ext = Σ≡Prop (∈-isProp (intervalℙ 0 1))

coordinateUC : UC[ Interval , ℝPremetricSpace ]
coordinateUC = subspaceInclusionUC ℝPremetricSpace (intervalℙ 0 1)

clip : ℝ → 𝕀
clip t = clampᵣ 0 1 t , clampᵣ∈intervalℙ 0 1 decℚ≤ᵣ? t

private
  intoSubspaceUC : ∀ {ℓ ℓ' ℓN ℓN'} {M : PremetricSpace ℓ ℓ'} {N : PremetricSpace ℓN ℓN'}
    (P : ℙ (fst N)) (f : UC[ M , N ]) → (∀ x → fst f x ∈ P) →
    UC[ M , PremetricSubspace N P ]
  fst (intoSubspaceUC P f bounds) x = fst f x , bounds x
  snd (intoSubspaceUC P f bounds) = PT.map
    (λ (μ , c) → μ , isuniformlycontinuouswith (IsUniformlyContinuousWith.pres≈ c)) (snd f)

clipUC : UC[ ℝPremetricSpace , Interval ]
clipUC = intoSubspaceUC (intervalℙ 0 1) (clampUC 0 1)
  (clampᵣ∈intervalℙ 0 1 decℚ≤ᵣ?)

clip-fixes : (t : 𝕀) → clip (fst t) ≡ t
clip-fixes (t , bounds) = interval-ext (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 t bounds))

clip-below : ∀ t → t ≤ᵣ 0 → clip t ≡ 𝟘
clip-below t below = interval-ext (x≤→clampᵣ≡ 0 1 t decℚ≤ᵣ? below)

clip-above : ∀ t → 1 ≤ᵣ t → clip t ≡ 𝟙
clip-above t above = interval-ext (≤x→clampᵣ≡ 0 1 t decℚ≤ᵣ? above)

reverseTime : 𝕀 → 𝕀
reverseTime t = 1 -ᵣ fst t , lower-bound , upper-bound
  where
  lower-bound : 0 ≤ᵣ 1 -ᵣ fst t
  lower-bound = isTrans≡≤ᵣ _ _ _ ℝ! (≤ᵣ-+o (fst t) 1 (-ᵣ fst t) (snd (snd t)))
  upper-bound : 1 -ᵣ fst t ≤ᵣ 1
  upper-bound = isTrans≤≡ᵣ _ _ _ (≤ᵣ-o+ (-ᵣ fst t) (-ᵣ 0) 1
    (-ᵣ≤ᵣ 0 (fst t) (fst (snd t)))) ℝ!

reverseTimeUC : UC[ Interval , Interval ]
reverseTimeUC = intoSubspaceUC (intervalℙ 0 1)
  (subRealUC (constantUC 1) coordinateUC) (λ t → snd (reverseTime t))

reverseTime-0 : reverseTime 𝟘 ≡ 𝟙
reverseTime-0 = interval-ext ℝ!
reverseTime-1 : reverseTime 𝟙 ≡ 𝟘
reverseTime-1 = interval-ext ℝ!
reverseTime-involutive : ∀ t → reverseTime (reverseTime t) ≡ t
reverseTime-involutive t = interval-ext ℝ!

interval-bound : (t : 𝕀) → absᵣ (fst t) ≤ᵣ 1
interval-bound t = isTrans≡≤ᵣ _ _ _
  (absᵣNonNeg (fst t) (fst (snd t))) (snd (snd t))

IntervalSquare : PremetricSpace ℓ-zero ℓ-zero
IntervalSquare = PremetricProduct Interval Interval

-- Convex interpolation is used only in the real parameter, never in X.
module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  blendUC : (s f g : UC[ M , Interval ]) → UC[ M , Interval ]
  blendUC s f g = clipUC ∘UC addRealUC
    (boundedMultiplyUC (coordinateUC ∘UC (reverseTimeUC ∘UC s)) (coordinateUC ∘UC f)
      1 1 (λ x → interval-bound (reverseTime (fst s x))) (λ x → interval-bound (fst f x)))
    (boundedMultiplyUC (coordinateUC ∘UC s) (coordinateUC ∘UC g)
      1 1 (λ x → interval-bound (fst s x)) (λ x → interval-bound (fst g x)))

  blend-β : ∀ s f g x → fst (blendUC s f g) x ≡
    clip ((1 -ᵣ fst (fst s x)) ·ᵣ fst (fst f x) +ᵣ fst (fst s x) ·ᵣ fst (fst g x))
  blend-β s f g x = refl

  blend-0 : ∀ s f g x → fst s x ≡ 𝟘 → fst (blendUC s f g) x ≡ fst f x
  blend-0 s f g x at0 = cong
    (λ t → clip ((1 -ᵣ fst t) ·ᵣ fst (fst f x) +ᵣ fst t ·ᵣ fst (fst g x))) at0
    ∙ cong clip ℝ! ∙ clip-fixes (fst f x)

  blend-1 : ∀ s f g x → fst s x ≡ 𝟙 → fst (blendUC s f g) x ≡ fst g x
  blend-1 s f g x at1 = cong
    (λ t → clip ((1 -ᵣ fst t) ·ᵣ fst (fst f x) +ᵣ fst t ·ᵣ fst (fst g x))) at1
    ∙ cong clip ℝ! ∙ clip-fixes (fst g x)

  blend-same : ∀ s f g x → fst f x ≡ fst g x → fst (blendUC s f g) x ≡ fst f x
  blend-same s f g x same = cong
    (λ t → clip ((1 -ᵣ fst (fst s x)) ·ᵣ fst (fst f x) +ᵣ fst (fst s x) ·ᵣ fst t)) (sym same)
    ∙ cong clip ℝ! ∙ clip-fixes (fst f x)
