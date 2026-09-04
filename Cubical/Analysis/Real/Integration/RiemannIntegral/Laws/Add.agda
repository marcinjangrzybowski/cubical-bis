module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ using (_/2₊)
open 1/2∈ℚ using (/2+/2≡id)

open import Cubical.Relation.Premetric.Base using (PremetricStr)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)


addHasRiemannIntegral : ∀ {a b} (f g : ℝ → ℝ) value value' →
  HasRiemannIntegralOn f a b value →
  HasRiemannIntegralOn g a b value' →
  HasRiemannIntegralOn (λ x → f x + g x) a b (value + value')
addHasRiemannIntegral {a} {b} f g value value' hasValue hasValue' ε =
  PT.map2
    (λ { (δ , closeToValue) (δ' , closeToValue') →
      min₊ δ δ' , λ tagged fine →
        closeness→absDifference<
          (riemannSum tagged (λ x → f x + g x))
          (value + value') ε
          (subst (_∼[ ε ] value + value')
            (sym (riemannSum-add tagged f g))
            (Pℝ.subst≈
              (riemannSum tagged f + riemannSum tagged g)
              (value + value')
              (/2+/2≡id (fst ε))
              (add-pres∼
                (riemannSum tagged f) value
                (riemannSum tagged g) value'
                (ε /2₊) (ε /2₊)
                (absDifference<→closeness
                  (riemannSum tagged f) value (ε /2₊)
                  (closeToValue tagged
                    (meshBelowMonotone
                      (TaggedPartition.partition tagged)
                      (min₊ δ δ') δ (min₊≤L δ δ') fine)))
                (absDifference<→closeness
                  (riemannSum tagged g) value' (ε /2₊)
                  (closeToValue' tagged
                    (meshBelowMonotone
                      (TaggedPartition.partition tagged)
                      (min₊ δ δ') δ' (min₊≤R δ δ') fine)))))) })
    (hasValue (ε /2₊))
    (hasValue' (ε /2₊))


addIsRiemannIntegrable : ∀ {a b} (f g : ℝ → ℝ) →
  IsRiemannIntegrableOn f a b →
  IsRiemannIntegrableOn g a b →
  IsRiemannIntegrableOn (λ x → f x + g x) a b
addIsRiemannIntegrable f g (value , hasValue) (value' , hasValue') =
  value + value'
  , addHasRiemannIntegral f g value value' hasValue hasValue'


integral-add : ∀ {a b} (f g : ℝ → ℝ)
  (f-integrable : IsRiemannIntegrableOn f a b)
  (g-integrable : IsRiemannIntegrableOn g a b) →
  integral
    {f = λ x → f x + g x} {a = a} {b = b}
    (addIsRiemannIntegrable f g f-integrable g-integrable) ≡
  integral {f = f} {a = a} {b = b} f-integrable +
  integral {f = g} {a = a} {b = b} g-integrable
integral-add f g (value , hasValue) (value' , hasValue') = refl
