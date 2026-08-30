module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
  using (add-pres≈)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
  using (mulIsLipschitzLeftAtBound ; mulIsLipschitzRightAtBound)
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity


constantIsRadiuswiseUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) c →
  IsRadiuswiseUniformlyContinuous
    source (λ _ → c) (snd Real.ℝPremetricSpace)
constantIsRadiuswiseUniformlyContinuous source c ε =
  ∣ ε , (λ _ _ _ → Real.Base.isRefl≈ᶜ c ε) ∣₁


radiuswiseUniformlyContinuous-cong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (f g : A → Real.ℝ) →
  (∀ x → f x ≡ g x) →
  IsRadiuswiseUniformlyContinuous
    source f (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source g (snd Real.ℝPremetricSpace)
radiuswiseUniformlyContinuous-cong source f g agrees uniform ε =
  PT.map
    (λ { (δ , close) →
      δ , λ x y x≈y →
        subst2 (Real.Base._≈ᶜ[ ε ]_)
          (agrees x) (agrees y) (close x y x≈y) })
    (uniform ε)


addIsRadiuswiseUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (f g : A → Real.ℝ) →
  IsRadiuswiseUniformlyContinuous
    source f (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source g (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source (λ x → f x Add.+ g x) (snd Real.ℝPremetricSpace)
addIsRadiuswiseUniformlyContinuous source f g f-uniform g-uniform ε =
  PT.map2 combine (f-uniform (ε /2₊)) (g-uniform (ε /2₊))
  where
  combine :
    (Σ[ δf ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δf y →
        f x Real.Base.≈ᶜ[ ε /2₊ ] f y)) →
    (Σ[ δg ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δg y →
        g x Real.Base.≈ᶜ[ ε /2₊ ] g y)) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δ y →
        (f x Add.+ g x) Real.Base.≈ᶜ[ ε ]
          (f y Add.+ g y))
  combine (δf , f-close) (δg , g-close) =
    min₊ δf δg , λ x y x≈y →
      subst
        (λ radius →
          (f x Add.+ g x) Real.Base.≈ᶜ[ radius ]
            (f y Add.+ g y))
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (add-pres≈
          (f x) (f y) (g x) (g y)
          (ε /2₊) (ε /2₊)
          (f-close x y
            (PremetricStr.isMonotone≈≤ source x y
              (min₊ δf δg) δf (min₊≤L δf δg) x≈y))
          (g-close x y
            (PremetricStr.isMonotone≈≤ source x y
              (min₊ δf δg) δg (min₊≤R δf δg) x≈y)))


negIsRadiuswiseUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (f : A → Real.ℝ) →
  IsRadiuswiseUniformlyContinuous
    source f (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source (Neg.-_ ∘ f) (snd Real.ℝPremetricSpace)
negIsRadiuswiseUniformlyContinuous source f uniform ε =
  PT.map
    (λ { (δ , close) →
      δ , λ x y x≈y →
        Neg.neg-pres≈ (f x) (f y) ε (close x y x≈y) })
    (uniform ε)


subIsRadiuswiseUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (f g : A → Real.ℝ) →
  IsRadiuswiseUniformlyContinuous
    source f (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source g (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source (λ x → f x Group.- g x) (snd Real.ℝPremetricSpace)
subIsRadiuswiseUniformlyContinuous source f g f-uniform g-uniform =
  addIsRadiuswiseUniformlyContinuous source f (Neg.-_ ∘ g)
    f-uniform (negIsRadiuswiseUniformlyContinuous source g g-uniform)


scaleIsRadiuswiseUniformlyContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) c (f : A → Real.ℝ) →
  IsRadiuswiseUniformlyContinuous
    source f (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source (λ x → c Mul.· f x) (snd Real.ℝPremetricSpace)
scaleIsRadiuswiseUniformlyContinuous source c f uniform ε =
  PT.rec squash₁ bounded-scale (∃rationalBound c)
  where
  bounded-scale : RationalBound c →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δ y →
        (c Mul.· f x) Real.Base.≈ᶜ[ ε ] (c Mul.· f y))
  bounded-scale (B , absc≤B) =
    PT.map
      (λ { (δ , close) →
        δ , λ x y x≈y →
          subst
            (λ radius →
              (c Mul.· f x) Real.Base.≈ᶜ[ radius ]
                (c Mul.· f y))
            (ℚ₊≡ (·／ B ε))
            (mulIsLipschitzLeftAtBound B c absc≤B
              .IsLipschitzWith.pres≈
                (f x) (f y) (ε ₊／₊ B)
                (close x y x≈y)) })
      (uniform (ε ₊／₊ B))


-- Multiplication is uniformly continuous on uniformly bounded families.  A
-- common rational bound is the correct constructive hypothesis: it supplies
-- both Lipschitz estimates without choosing any point-dependent bounds.

mulOfBoundedRadiuswiseUniformlyContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (B : ℚ₊)
  (f g : A → Real.ℝ) →
  (∀ x → Abs.absℝ (f x) ≤ℝ Real.ιℚ (fst B)) →
  (∀ x → Abs.absℝ (g x) ≤ℝ Real.ιℚ (fst B)) →
  IsRadiuswiseUniformlyContinuous
    source f (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source g (snd Real.ℝPremetricSpace) →
  IsRadiuswiseUniformlyContinuous
    source (λ x → f x Mul.· g x) (snd Real.ℝPremetricSpace)
mulOfBoundedRadiuswiseUniformlyContinuous
  source B f g f-bounded g-bounded f-uniform g-uniform ε =
  PT.map2 combine
    (f-uniform ((ε /2₊) ₊／₊ B))
    (g-uniform ((ε /2₊) ₊／₊ B))
  where
  combine :
    (Σ[ δf ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δf y →
        f x Real.Base.≈ᶜ[ (ε /2₊) ₊／₊ B ] f y)) →
    (Σ[ δg ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δg y →
        g x Real.Base.≈ᶜ[ (ε /2₊) ₊／₊ B ] g y)) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δ y →
        (f x Mul.· g x) Real.Base.≈ᶜ[ ε ]
          (f y Mul.· g y))
  combine (δf , f-close) (δg , g-close) =
    min₊ δf δg , λ x y x≈y →
      subst
        (λ radius →
          (f x Mul.· g x) Real.Base.≈ᶜ[ radius ]
            (f y Mul.· g y))
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (Real.Premetric.tri≈ᶜ
          (f x Mul.· g x)
          (f y Mul.· g x)
          (f y Mul.· g y)
          (ε /2₊) (ε /2₊)
          (subst
            (λ radius →
              (f x Mul.· g x) Real.Base.≈ᶜ[ radius ]
                (f y Mul.· g x))
            (ℚ₊≡ (·／ B (ε /2₊)))
            (mulIsLipschitzRightAtBound B (g x) (g-bounded x)
              .IsLipschitzWith.pres≈
                (f x) (f y) ((ε /2₊) ₊／₊ B)
                (f-close x y
                  (PremetricStr.isMonotone≈≤ source x y
                    (min₊ δf δg) δf
                    (min₊≤L δf δg) x≈y))))
          (subst
            (λ radius →
              (f y Mul.· g x) Real.Base.≈ᶜ[ radius ]
                (f y Mul.· g y))
            (ℚ₊≡ (·／ B (ε /2₊)))
            (mulIsLipschitzLeftAtBound B (f y) (f-bounded y)
              .IsLipschitzWith.pres≈
                (g x) (g y) ((ε /2₊) ₊／₊ B)
                (g-close x y
                  (PremetricStr.isMonotone≈≤ source x y
                    (min₊ δf δg) δg
                    (min₊≤R δf δg) x≈y)))))


partialSumFamilyIsRadiuswiseUniformlyContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  (terms : A → RealSequence) →
  (∀ n → IsRadiuswiseUniformlyContinuous
    source (λ x → terms x n) (snd Real.ℝPremetricSpace)) →
  ∀ n → IsRadiuswiseUniformlyContinuous
    source (λ x → partialSum (terms x) n)
    (snd Real.ℝPremetricSpace)
partialSumFamilyIsRadiuswiseUniformlyContinuous
  source terms term-uniform zero =
  constantIsRadiuswiseUniformlyContinuous source zeroℝ
partialSumFamilyIsRadiuswiseUniformlyContinuous
  source terms term-uniform (suc n) =
  addIsRadiuswiseUniformlyContinuous source
    (λ x → partialSum (terms x) n)
    (λ x → terms x n)
    (partialSumFamilyIsRadiuswiseUniformlyContinuous
      source terms term-uniform n)
    (term-uniform n)
