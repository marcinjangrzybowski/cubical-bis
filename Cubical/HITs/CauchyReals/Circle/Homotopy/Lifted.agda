module Cubical.HITs.CauchyReals.Circle.Homotopy.Lifted where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.Uniform using (clampᵣ∼)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base using (IsUContinuous·ᵣR)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Compatibility.Base
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

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

private
  unitTimeUC : UC[ ℝPremetricSpace , ℝPremetricSpace ]
  unitTimeUC = IsUContinuous→ℝUC (clampᵣ 0 1)
    (λ ε → ε , λ x y → clampᵣ∼)

  time-bound : ∀ t → absᵣ (clampᵣ 0 1 t) ≤ᵣ 1
  time-bound t = isTrans≡≤ᵣ _ _ _
    (absᵣNonNeg _ (≤clampᵣ 0 1 t decℚ≤ᵣ?)) (clamp≤ᵣ 0 1 t)

-- A bounded uniformly continuous real logarithm gives an explicit
-- uniform null-homotopy, t ↦ injCircle (clamp 0 1 t · g x).
liftedHomotopy : (f : CircleMap) (g : UC[ CirclePremetricSpace , ℝPremetricSpace ]) →
  (B : ℝ₊) → (∀ x → absᵣ (fst g x) ≤ᵣ fst B) →
  (∀ x → injCircle (fst g x) ≡ fst f x) → UniformHomotopy zeroCircleMap f
liftedHomotopy f g B bound lifts = deformation , start , end
  where
  interpolation : UC[ CircleCylinder , ℝPremetricSpace ]
  interpolation = boundedMultiplyUC (unitTimeUC ∘UC productFstUC) (g ∘UC productSndUC)
    1 B (λ x → time-bound (fst x)) (λ x → bound (snd x))
  deformation : UC[ CircleCylinder , CirclePremetricSpace ]
  deformation = injCircleUC ∘UC interpolation
  start : ∀ x → fst deformation (0 , x) ≡ fst zeroCircleMap x
  start x = cong injCircle
    (cong (_·ᵣ fst g x) (x≤→clampᵣ≡ 0 1 0 decℚ≤ᵣ? (≤ᵣ-refl 0)) ∙ Rℝ.0LeftAnnihilates _)
  end : ∀ x → fst deformation (1 , x) ≡ fst f x
  end x = cong injCircle
    (cong (_·ᵣ fst g x) (≤x→clampᵣ≡ 0 1 1 decℚ≤ᵣ? (≤ᵣ-refl 1)) ∙ Rℝ.·IdL _)
    ∙ lifts x

lifted-null : (f : CircleMap) (g : UC[ CirclePremetricSpace , ℝPremetricSpace ]) →
  (B : ℝ₊) → (∀ x → absᵣ (fst g x) ≤ᵣ fst B) →
  (∀ x → injCircle (fst g x) ≡ fst f x) → Homotopic f zeroCircleMap
lifted-null f g B bound lifts = ∣ homotopy-sym zeroCircleMap f (liftedHomotopy f g B bound lifts) ∣₁

-- Quotient induction supplies an angle only inside a proposition;
-- no global choice of angles is made.
constant-null : (p : Circle) → Homotopic (constantUC p) zeroCircleMap
constant-null = SQ.elimProp (λ _ → squash₁) contract
  where
  contract : ∀ a → Homotopic (constantUC (injCircle a)) zeroCircleMap
  contract a = lifted-null (constantUC (injCircle a)) (constantUC a)
    (absᵣ a +ᵣ 1 , isTrans≤<ᵣ 0 (absᵣ a) _ (0≤absᵣ a) grows)
    (λ _ → <ᵣWeaken≤ᵣ _ _ grows) (λ _ → refl)
    where
    grows : absᵣ a <ᵣ absᵣ a +ᵣ 1
    grows = isTrans≡<ᵣ _ _ _ (sym (+IdR (absᵣ a)))
      (<ᵣ-o+ 0 1 (absᵣ a) decℚ<ᵣ?)
