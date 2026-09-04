module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


constantHasRiemannIntegral : ∀ a b c →
  HasRiemannIntegralOn (λ (_ : ℝ) → c) a b ((b - a) · c)
constantHasRiemannIntegral a b c ε =
  ∣ (1 , λ tagged _ →
    subst
      (λ sum → absℝ (sum - ((b - a) · c)) <ℝ rat (fst ε))
      (sym (constantSum tagged))
      (zeroErrorSmall ε)) ∣₁
  where
  constantSum : ∀ (tagged : TaggedPartition[ a , b ]) →
    riemannSum tagged (λ (_ : ℝ) → c) ≡ (b - a) · c
  constantSum tagged = riemannSum-constant tagged c

  zeroErrorSmall : ∀ (ε : ℚ₊) →
    absℝ (((b - a) · c) - ((b - a) · c)) <ℝ rat (fst ε)
  zeroErrorSmall ε =
    subst (_<ℝ rat (fst ε))
      (sym
        (cong absℝ (subSelf ((b - a) · c))
        ∙ absZero))
      (<ℚ→<ℝ 0 (fst ε) (snd ε))


constantIsRiemannIntegrable : ∀ a b c →
  IsRiemannIntegrableOn (λ (_ : ℝ) → c) a b
constantIsRiemannIntegrable a b c =
  (b - a) · c , constantHasRiemannIntegral a b c


integral-constant : ∀ a b c →
  integral
    {f = λ (_ : ℝ) → c} {a = a} {b = b}
    (constantIsRiemannIntegrable a b c) ≡
  (b - a) · c
integral-constant a b c = refl
