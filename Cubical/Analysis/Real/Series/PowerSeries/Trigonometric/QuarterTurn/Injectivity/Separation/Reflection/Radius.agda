module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Radius where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference


open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using
  (_/2₊; _/4₊; /2₊<id)


opaque
  doubledRadiusAbsoluteBound→closeness :
    ∀ (small large : ℚ₊) (x y : ℝ) →
    rat (fst small) + rat (fst small) <ℝ rat (fst large) →
    absℝ (x - y) ≤ℝ rat (fst small) + rat (fst small) →
    x ∼[ large ] y
  doubledRadiusAbsoluteBound→closeness
      small large x y doubled-small<large absolute-bound =
    absDifference<→closeness x y large
      (≤<ℝ-trans
        (absℝ (x - y))
        (rat (fst small) + rat (fst small))
        (rat (fst large))
        absolute-bound doubled-small<large)


  quarterRadiusDouble<radius : ∀ (radius : ℚ₊) →
    rat (fst (radius /4₊)) + rat (fst (radius /4₊))
      <ℝ rat (fst radius)
  quarterRadiusDouble<radius radius =
    subst (λ point → point <ℝ rat (fst radius))
      (sym double-quarter≡half)
      (<ℚ→<ℝ
        (fst (radius /2₊)) (fst radius) (/2₊<id radius))
    where
    double-quarter≡half :
      rat (fst (radius /4₊)) + rat (fst (radius /4₊))
        ≡ rat (fst (radius /2₊))
    double-quarter≡half =
      rat+rat (fst (radius /4₊)) (fst (radius /4₊))
      ∙ cong rat (1/2∈ℚ./4+/4≡/2 (fst radius))


  quarterRadiusAbsoluteBound→closeness :
    ∀ (radius : ℚ₊) (x y : ℝ) →
    absℝ (x - y)
      ≤ℝ rat (fst (radius /4₊)) + rat (fst (radius /4₊)) →
    x ∼[ radius ] y
  quarterRadiusAbsoluteBound→closeness radius x y absolute-bound =
    doubledRadiusAbsoluteBound→closeness
      (radius /4₊) radius x y
      (quarterRadiusDouble<radius radius) absolute-bound
