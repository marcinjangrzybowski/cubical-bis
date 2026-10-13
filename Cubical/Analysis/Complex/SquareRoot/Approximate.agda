module Cubical.Analysis.Complex.SquareRoot.Approximate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.SquareRoot.HalfPlane

-- Squares are dense. A single use of located order moves the target into
-- an open half-plane by less than the requested tolerance. Truncated choices
-- are eliminated only into the truncated approximate-root proposition.
approximateSquareRoot : (z : ℂ) (ε : ℚ₊) →
  ∥ Σ[ w ∈ ℂ ] ((w ·ℂ w) ∼ℂ[ ε ] z) ∥₁
approximateSquareRoot z ε = PT.rec squash₁ (Sum.rec left right)
  (dichotomyℝ (- shift) (re z) shift
    (<ℝ-trans (- shift) 0ℝ shift (negationOfPositiveNegative shift-positive) shift-positive))
  where
  shift : ℝ
  shift = rat (fst (ε /2₊))

  shift-positive : 0ℝ <ℝ shift
  shift-positive = <ℚ→<ℝ 0 (fst (ε /2₊)) (snd (ε /2₊))

  shift-close : shift ∼[ ε ] 0ℝ
  shift-close = absDifference<→closeness shift 0ℝ ε
    (subst (_<ℝ rat (fst ε))
      (sym (cong absℝ (subZero shift)
        ∙ absOfNonnegative shift (<ℝ-weaken 0ℝ shift shift-positive)))
      (<ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)))

  negative-shift-close : (- shift) ∼[ ε ] 0ℝ
  negative-shift-close = subst ((- shift) ∼[ ε ]_) negZero
    (IsNonExpanding.pres≈ neg-isNonExpanding shift 0ℝ ε shift-close)

  left : re z <ℝ shift → ∥ Σ[ w ∈ ℂ ] ((w ·ℂ w) ∼ℂ[ ε ] z) ∥₁
  left below = ∣ root ,
    subst (λ w → w ∼ℂ[ ε ] z) (sym (leftHalfPlaneSqrt-square shifted negative))
      (subst ((re z - shift) ∼[ ε ]_) (addIdR (re z))
        (add-pres∼₂ (re z) (- shift) 0ℝ ε negative-shift-close) , refl∼ (im z) ε) ∣₁
    where
    shifted : ℂ
    shifted = (re z - shift) , im z
    negative : re shifted <ℝ 0ℝ
    negative = subst ((re z - shift) <ℝ_) (subSelf shift)
      (<ℝ-addR (re z) shift (- shift) below)
    root : ℂ
    root = leftHalfPlaneSqrt shifted negative

  right : (- shift) <ℝ re z → ∥ Σ[ w ∈ ℂ ] ((w ·ℂ w) ∼ℂ[ ε ] z) ∥₁
  right above = ∣ root ,
    subst (λ w → w ∼ℂ[ ε ] z) (sym (rightHalfPlaneSqrt-square shifted positive))
      (subst ((re z + shift) ∼[ ε ]_) (addIdR (re z))
        (add-pres∼₂ (re z) shift 0ℝ ε shift-close) , refl∼ (im z) ε) ∣₁
    where
    shifted : ℂ
    shifted = (re z + shift) , im z
    positive : 0ℝ <ℝ re shifted
    positive = subst (_<ℝ (re z + shift)) (addInvL shift)
      (<ℝ-addR (- shift) (re z) shift above)
    root : ℂ
    root = rightHalfPlaneSqrt shifted positive
