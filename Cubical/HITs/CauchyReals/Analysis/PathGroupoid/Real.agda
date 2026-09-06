module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Uniform using (clampᵣ∼)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base using (IsUContinuous·ᵣR)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

RealMap : Type
RealMap = UC[ ℝPremetricSpace , ℝPremetricSpace ]

constantUC : ∀ {ℓ ℓ' ℓ₁ ℓ₁'} {M : PremetricSpace ℓ ℓ'} {N : PremetricSpace ℓ₁ ℓ₁'} →
  fst N → UC[ M , N ]
constantUC {M = M} {N = N} x = NE→UC ((λ _ → x) , isnonexpanding
  (λ _ _ ε _ → PremetricStr.isRefl≈ (snd N) x ε))

clampUC : ℝ → ℝ → RealMap
clampUC a b = IsUContinuous→ℝUC (clampᵣ a b)
  (λ ε → ε , λ x y → clampᵣ∼)

negateRealUC : RealMap
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

private
  scalarUC : ℝ → UC[ ℝPremetricSpace , ℝPremetricSpace ]
  scalarUC a = (_·ᵣ a) , PT.rec squash₁
    (λ c → snd (IsUContinuous→ℝUC (_·ᵣ a) c)) (IsUContinuous·ᵣR a)

  opaque
    bounded-factor : ∀ a (B : ℝ₊) → absᵣ a ≤ᵣ fst B → ∀ x y ε →
      (x ·ᵣ fst B) ∼[ ε ] (y ·ᵣ fst B) → (x ·ᵣ a) ∼[ ε ] (y ·ᵣ a)
    bounded-factor a B bound x y ε close = invEq (∼≃abs<ε _ _ ε)
      (isTrans≡<ᵣ _ _ _
        (cong absᵣ (sym (Rℝ.·DistL- x y a)) ∙ ·absᵣ (x -ᵣ y) a)
        (isTrans≤<ᵣ _ _ _
          (≤ᵣ-o·ᵣ (absᵣ a) (fst B) (absᵣ (x -ᵣ y)) (0≤absᵣ _) bound)
          (isTrans≡<ᵣ _ _ _
            (cong (absᵣ (x -ᵣ y) ·ᵣ_) (sym (absᵣPos (fst B) (snd B)))
              ∙ sym (·absᵣ (x -ᵣ y) (fst B))
              ∙ cong absᵣ (Rℝ.·DistL- x y (fst B)))
            (equivFun (∼≃abs<ε _ _ ε) close))))

module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  private
    module P = PremetricStr (snd M)

  -- Joint uniform continuity of a product uses bounds on both factors.
  boundedMultiplyUC : (f g : UC[ M , ℝPremetricSpace ]) (Bf Bg : ℝ₊) →
    (∀ x → absᵣ (fst f x) ≤ᵣ fst Bf) → (∀ x → absᵣ (fst g x) ≤ᵣ fst Bg) →
    UC[ M , ℝPremetricSpace ]
  boundedMultiplyUC f g Bf Bg bf bg = (λ x → fst f x ·ᵣ fst g x) ,
    PT.map2 combine (snd (scalarUC (fst Bg) ∘UC f)) (snd (scalarUC (fst Bf) ∘UC g))
    where
    combine :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M)
        (λ x → fst f x ·ᵣ fst Bg) (snd ℝPremetricSpace) μ) →
      (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M)
        (λ x → fst g x ·ᵣ fst Bf) (snd ℝPremetricSpace) ν) →
      Σ[ κ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M)
        (λ x → fst f x ·ᵣ fst g x) (snd ℝPremetricSpace) κ
    combine (μ , fc) (ν , gc) = (λ ε → min₊ (μ (ε /2₊)) (ν (ε /2₊))) , preserves
      where
      preserves : IsUniformlyContinuousWith (snd M)
        (λ x → fst f x ·ᵣ fst g x) (snd ℝPremetricSpace)
        (λ ε → min₊ (μ (ε /2₊)) (ν (ε /2₊)))
      IsUniformlyContinuousWith.pres≈ preserves x y ε close = ∼→≈ℝ _ _ ε
        (subst∼ {0<ε = snd ((ε /2₊) +₊ (ε /2₊))} {0<ε' = snd ε} ℚ!
          (triangle∼ first second))
        where
        first : (fst f x ·ᵣ fst g x) ∼[ ε /2₊ ] (fst f y ·ᵣ fst g x)
        first = bounded-factor (fst g x) Bg (bg x) (fst f x) (fst f y) (ε /2₊)
          (≈ℝ→∼ _ _ (ε /2₊) (IsUniformlyContinuousWith.pres≈ fc x y (ε /2₊)
            (P.isMonotone≈≤ x y _ _ (min₊≤L (μ (ε /2₊)) (ν (ε /2₊))) close)))
        second : (fst f y ·ᵣ fst g x) ∼[ ε /2₊ ] (fst f y ·ᵣ fst g y)
        second = subst2 (λ a b → a ∼[ ε /2₊ ] b) (·ᵣComm _ _) (·ᵣComm _ _)
          (bounded-factor (fst f y) Bf (bf y) (fst g x) (fst g y) (ε /2₊)
            (≈ℝ→∼ _ _ (ε /2₊) (IsUniformlyContinuousWith.pres≈ gc x y (ε /2₊)
              (P.isMonotone≈≤ x y _ _ (min₊≤R (μ (ε /2₊)) (ν (ε /2₊))) close))))

scaleUC : ℝ → RealMap
scaleUC = scalarUC

translateUC : ℝ → RealMap
translateUC a = addRealUC (CategoryStructures.idᵘᶜ) (constantUC a)

-- Affine clocks are uniformly continuous on the whole real line.
affineUC : ℝ → ℝ → RealMap
affineUC a b = translateUC b ∘UC scaleUC a
