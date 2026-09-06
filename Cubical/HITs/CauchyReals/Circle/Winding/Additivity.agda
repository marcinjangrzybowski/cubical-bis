module Cubical.HITs.CauchyReals.Circle.Winding.Additivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos; isSetℤ)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.Algebra.AbGroup.Properties using (module AbGroupTheory)
open import Cubical.Algebra.CommRing.Base using (CommRing→AbGroup)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊; min₊; min₊≤L; min₊≤R)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Multiplication using (ℝcommRing)
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Winding.Loop
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using (injFromNatℚ)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

opaque
  shortAngle-product : ∀ p q r s pq rs product-near →
    shortAngle p q pq +ᵣ shortAngle r s rs ≡
    shortAngle (p ℝS¹.+ r) (q ℝS¹.+ s) product-near
  shortAngle-product p q r s pq rs product-near =
    cover-injective-near _ _ bound image
    where
    a : ℝ
    a = shortAngle p q pq
    b : ℝ
    b = shortAngle r s rs
    c : ℝ
    c = shortAngle (p ℝS¹.+ r) (q ℝS¹.+ s) product-near

    bound : absᵣ ((a +ᵣ b) -ᵣ c) <ᵣ 1
    bound = isTrans≤<ᵣ _ _ _ (absᵣ-triangle'' _ _)
      (isTrans≤<ᵣ _ _ _ (≤ᵣ-+o _ _ _ (absᵣ-triangle a b))
        (isTrans<ᵣ _ (rat [ 1 / 4 ] +ᵣ rat [ 1 / 4 ] +ᵣ rat [ 1 / 4 ]) _
          (<ᵣMonotone+ᵣ _ _ _ _
            (<ᵣMonotone+ᵣ _ _ _ _ (shortAngle-bound p q pq) (shortAngle-bound r s rs))
            (shortAngle-bound (p ℝS¹.+ r) (q ℝS¹.+ s) product-near))
          (isTrans≡<ᵣ _ _ _
            (cong (_+ᵣ rat [ 1 / 4 ]) (+ᵣ-rat _ _) ∙ +ᵣ-rat _ _)
            decℚ<ᵣ?)))

    image : cover (a +ᵣ b) ≡ cover c
    image = ℝS¹.·CancelL (p ℝS¹.+ r)
      (cong ((p ℝS¹.+ r) ℝS¹.+_) (cover-add a b)
        ∙ AbGroupTheory.comm-4 ℝS¹AbGroup p r (cover a) (cover b)
        ∙ cong₂ ℝS¹._+_ (shortAngle-step p q pq) (shortAngle-step r s rs)
        ∙ sym (shortAngle-step (p ℝS¹.+ r) (q ℝS¹.+ s) product-near))

module ProductSubdivision (f g : ℚ → distCircle) where
  private
    module F = Subdivision f
    module G = Subdivision g
    module H = Subdivision (λ x → f x ℝS¹.+ g x)

  turns-product : ∀ n a b a≤b ff gf hf →
    F.turns n a b a≤b ff +ᵣ G.turns n a b a≤b gf ≡ H.turns n a b a≤b hf
  turns-product zero a b a≤b ff gf hf = shortAngle-product (f a) (f b) (g a) (g b) _ _ _
  turns-product (suc n) a b a≤b ff gf hf = AbGroupTheory.comm-4 (CommRing→AbGroup ℝcommRing) _ _ _ _
    ∙ cong₂ _+ᵣ_
      (turns-product n a (mid a b) (mid-left a b a≤b) (fst ff) (fst gf) (fst hf))
      (turns-product n (mid a b) b (mid-right a b a≤b) (snd ff) (snd gf) (snd hf))

windingLoop-add : (f g : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
  (sum-cont : isUniformlyContinuous (snd ℝPremetricSpace)
    (λ x → fst f x ℝS¹.+ fst g x) (snd distCirclePremetricSpace)) →
  (fl : fst f 0 ≡ fst f 1) (gl : fst g 0 ≡ fst g 1) →
  windingLoop ((λ x → fst f x ℝS¹.+ fst g x) , sum-cont) (cong₂ ℝS¹._+_ fl gl) ≡
  windingLoop f fl ℤ.+ windingLoop g gl
windingLoop-add f g sum-cont fl gl = PT.rec3 (isSetℤ _ _) compare (snd f) (snd g) sum-cont
  where
  h : UC[ ℝPremetricSpace , distCirclePremetricSpace ]
  h = (λ x → fst f x ℝS¹.+ fst g x) , sum-cont
  hl : fst h 0 ≡ fst h 1
  hl = cong₂ ℝS¹._+_ fl gl
  module F = Subdivision (fst f ∘ rat)
  module G = Subdivision (fst g ∘ rat)
  module H = Subdivision (fst h ∘ rat)

  compare :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd ℝPremetricSpace) (fst f) (snd distCirclePremetricSpace) μ) →
    (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd ℝPremetricSpace) (fst g) (snd distCirclePremetricSpace) ν) →
    (Σ[ ξ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd ℝPremetricSpace) (fst h) (snd distCirclePremetricSpace) ξ) →
    windingLoop h hl ≡ windingLoop f fl ℤ.+ windingLoop g gl
  compare (μ , fc) (ν , gc) (ξ , hc) = injFromNatℚ _ _ (inj-rat _ _
    (sym (windingLoop-subdivision h hl n hf)
      ∙ sym (ProductSubdivision.turns-product (fst f ∘ rat) (fst g ∘ rat)
          n 0 1 unit-order ff gf hf)
      ∙ cong₂ _+ᵣ_ (windingLoop-subdivision f fl n ff) (windingLoop-subdivision g gl n gf)
      ∙ +ᵣ-rat _ _ ∙ cong rat (ℚ.ℤ+→ℚ+ (windingLoop f fl) (windingLoop g gl))))
    where
    δ : ℚ₊
    δ = min₊ (μ 1) (min₊ (ν 1) (ξ 1))
    n : ℕ
    n = fst (ℚ.1/2ⁿ<ε δ)
    bound : mesh n 0 1 ℚ.< fst δ
    bound = subst (ℚ._< fst δ) (sym (ℚ.·IdL _)) (snd (ℚ.1/2ⁿ<ε δ))
    boundf : mesh n 0 1 ℚ.< fst (μ 1)
    boundf = ℚ.isTrans<≤ _ _ _ bound (min₊≤L (μ 1) (min₊ (ν 1) (ξ 1)))
    boundg : mesh n 0 1 ℚ.< fst (ν 1)
    boundg = ℚ.isTrans<≤ _ _ _ bound (ℚ.isTrans≤ _ _ _
      (min₊≤R (μ 1) (min₊ (ν 1) (ξ 1))) (min₊≤L (ν 1) (ξ 1)))
    boundh : mesh n 0 1 ℚ.< fst (ξ 1)
    boundh = ℚ.isTrans<≤ _ _ _ bound (ℚ.isTrans≤ _ _ _
      (min₊≤R (μ 1) (min₊ (ν 1) (ξ 1))) (min₊≤R (ν 1) (ξ 1)))
    ff : F.Fine n 0 1
    ff = F.fine-from-mesh n 0 1 unit-order (μ 1)
      (λ x y close → metric-close→Near (fst f (rat x)) (fst f (rat y))
        (IsUniformlyContinuousWith.pres≈ fc (rat x) (rat y) 1
          (∼→≈ℝ (rat x) (rat y) (μ 1) (rat-rat-fromAbs x y (μ 1) close)))) boundf
    gf : G.Fine n 0 1
    gf = G.fine-from-mesh n 0 1 unit-order (ν 1)
      (λ x y close → metric-close→Near (fst g (rat x)) (fst g (rat y))
        (IsUniformlyContinuousWith.pres≈ gc (rat x) (rat y) 1
          (∼→≈ℝ (rat x) (rat y) (ν 1) (rat-rat-fromAbs x y (ν 1) close)))) boundg
    hf : H.Fine n 0 1
    hf = H.fine-from-mesh n 0 1 unit-order (ξ 1)
      (λ x y close → metric-close→Near (fst h (rat x)) (fst h (rat y))
        (IsUniformlyContinuousWith.pres≈ hc (rat x) (rat y) 1
          (∼→≈ℝ (rat x) (rat y) (ξ 1) (rat-rat-fromAbs x y (ξ 1) close)))) boundh
