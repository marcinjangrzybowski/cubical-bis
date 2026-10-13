module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties

opaque
  twiceSquareBound : ∀ h s → 0ℝ ≤ℝ h → h ≤ℝ s →
    h · h ≤ℝ (s · s) + (s · s)
  twiceSquareBound h s hp hs = ≤ℝ-trans (h · h) (s · s) ((s · s) + (s · s))
    (mulPres≤ h s h s (≤ℝ-trans 0ℝ h s hp hs) hp hs hs)
    (subst (_≤ℝ (s · s) + (s · s)) (addIdR (s · s))
      (addPres≤L 0ℝ (s · s) (s · s)
        (isNonnegative→0≤ (s · s) (squareIsNonnegative s))))

opaque
  squareRadius : ℚ₊ → ℚ₊
  squareRadius q = q ·₊ q

  squareRadius-value : ∀ q → rat (fst (squareRadius q)) ≡ rat (fst q) · rat (fst q)
  squareRadius-value q = sym (mul-rat (fst q) (fst q))

opaque
  rationalSquareBound : ∀ (q : ℚ₊) s → rat (fst q) ≤ℝ s →
    rat (fst (squareRadius q)) ≤ℝ (s · s) + (s · s)
  rationalSquareBound q s lower =
    subst {x = rat (fst q) · rat (fst q)}
      {y = rat (fst (squareRadius q))}
      (_≤ℝ (s · s) + (s · s))
      (sym (squareRadius-value q))
      (twiceSquareBound (rat (fst q)) s
        (<ℝ-weaken 0ℝ (rat (fst q))
          (<ℚ→<ℝ 0 (fst q) (snd q))) lower)

opaque
  halfRadius : ℚ₊ → ℚ₊
  halfRadius q = q /2₊

  halfRadius-value : ∀ q → rat (fst (halfRadius q)) ≡ rat (fst (q /2₊))
  halfRadius-value q = refl

opaque
  rationalSquareBoundFor : ∀ (f : ℝ → ℝ) →
    (∀ (q : ℚ₊) → rat (fst q) ≤ℝ 1ℝ → rat (fst (q /2₊)) ≤ℝ f (rat (fst q))) →
    ∀ (q : ℚ₊) → rat (fst q) ≤ℝ 1ℝ →
    rat (fst (squareRadius (halfRadius q))) ≤ℝ
      (f (rat (fst q)) · f (rat (fst q))) + (f (rat (fst q)) · f (rat (fst q)))
  rationalSquareBoundFor f lower q upper =
    rationalSquareBound (halfRadius q) (f (rat (fst q)))
      (subst {x = rat (fst (q /2₊))} {y = rat (fst (halfRadius q))}
        (_≤ℝ f (rat (fst q))) (sym (halfRadius-value q)) (lower q upper))
