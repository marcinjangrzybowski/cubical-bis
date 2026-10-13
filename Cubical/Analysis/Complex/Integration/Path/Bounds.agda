module Cubical.Analysis.Complex.Integration.Path.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addComm)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (addPres≤R)
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absOfNonnegative; nonnegativeSub; 0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤L)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path

module _ {a b : ℝ} (path : UniformComplexPath a b) where
  private module P = UniformComplexPath path

  -- Use the already proved complex Lipschitz bound to bound the whole image.
  -- Keeping the radius opaque prevents expansion of completed arithmetic in
  -- later polynomial estimates.
  opaque
    pathImageNormBound : ℝ
    pathImageNormBound = normℂ (P.curve a) + rat (fst (P.speedBound +₊ P.speedBound)) · (b - a)

  opaque
    unfolding pathImageNormBound

    pathImageIsBounded : ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (P.curve t) ≤ℝ pathImageNormBound
    pathImageIsBounded t lower upper =
      subst2 _≤ℝ_ (cong normℂ (ℂRing.minusPlus (P.curve t) (P.curve a)))
        (addComm (rat (fst (P.speedBound +₊ P.speedBound)) · (b - a)) (normℂ (P.curve a)))
        (normℂ-addBound (P.curve t -ℂ P.curve a) (P.curve a)
          (rat (fst (P.speedBound +₊ P.speedBound)) · (b - a)) (normℂ (P.curve a))
          (≤ℝ-trans (normℂ (P.curve t -ℂ P.curve a))
            (rat (fst (P.speedBound +₊ P.speedBound)) · absℝ (t - a))
            (rat (fst (P.speedBound +₊ P.speedBound)) · (b - a))
            (uniformComplexCurveLipschitzOn P.curve P.velocity a b P.speedBound P.differentiable P.boundedSpeed
              (a , ≤ℝ-refl a , P.ordered) (t , lower , upper))
            (mulPres≤L (absℝ (t - a)) (b - a) (rat (fst (P.speedBound +₊ P.speedBound)))
              (0≤→isNonnegative (rat (fst (P.speedBound +₊ P.speedBound)))
                (<ℝ-weaken 0ℝ (rat (fst (P.speedBound +₊ P.speedBound))) (positiveSlack (P.speedBound +₊ P.speedBound))))
              (subst (_≤ℝ (b - a)) (sym (absOfNonnegative (t - a) (nonnegativeSub a t lower)))
                (addPres≤R t b (- a) upper))))
          (≤ℝ-refl (normℂ (P.curve a))))
