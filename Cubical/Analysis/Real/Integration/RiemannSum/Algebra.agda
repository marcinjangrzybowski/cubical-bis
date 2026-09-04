module Cubical.Analysis.Real.Integration.RiemannSum.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


module _ {a b : ℝ} (tagged : TaggedPartition[ a , b ]) where
  private
    p = TaggedPartition.partition tagged

  open Partition p
  open TaggedPartition tagged

  riemannSum : (ℝ → ℝ) → ℝ
  riemannSum f = ∑ (λ i → width p i · f (tags i))

  riemannSum-cong : (f g : ℝ → ℝ) →
    (∀ i → f (tags i) ≡ g (tags i)) →
    riemannSum f ≡ riemannSum g
  riemannSum-cong f g agree =
    finiteSumExt (λ i → cong (width p i ·_) (agree i))

  riemannSum-add : (f g : ℝ → ℝ) →
    riemannSum (λ x → f x + g x) ≡ riemannSum f + riemannSum g
  riemannSum-add f g =
    finiteSumExt (λ i → mulDistR (width p i) (f (tags i)) (g (tags i)))
    ∙ finiteSumAdd
      (λ i → width p i · f (tags i))
      (λ i → width p i · g (tags i))

  riemannSum-sub : (f g : ℝ → ℝ) →
    riemannSum (λ x → f x - g x) ≡ riemannSum f - riemannSum g
  riemannSum-sub f g =
    finiteSumExt (λ i →
      ℝRing.·DistR-
        (width p i) (f (tags i)) (g (tags i)))
    ∙ finiteSumSub
      (λ i → width p i · f (tags i))
      (λ i → width p i · g (tags i))

  riemannSum-neg : (f : ℝ → ℝ) →
    riemannSum (λ x → - f x) ≡ - (riemannSum f)
  riemannSum-neg f =
    finiteSumExt (λ i →
      ℝRing.-DistR· (width p i) (f (tags i)))
    ∙ finiteSumNeg (λ i → width p i · f (tags i))

  riemannSum-scale : (c : ℝ) (f : ℝ → ℝ) →
    riemannSum (λ x → c · f x) ≡ c · riemannSum f
  riemannSum-scale c f =
    finiteSumExt (λ i →
      mulAssoc (width p i) c (f (tags i))
      ∙ cong (_· f (tags i)) (mulComm (width p i) c)
      ∙ sym (mulAssoc c (width p i) (f (tags i))))
    ∙ sym
      (finiteSumMulLeft c
        (λ i → width p i · f (tags i)))

  riemannSum-constant : (c : ℝ) →
    riemannSum (λ (_ : ℝ) → c) ≡ (b - a) · c
  riemannSum-constant c =
    sym (finiteSumMulRight c (width p))
    ∙ cong (_· c) (totalWidth p)
