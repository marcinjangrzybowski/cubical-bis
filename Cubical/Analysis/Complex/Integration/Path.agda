module Cubical.Analysis.Complex.Integration.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Integration.Curve
import Cubical.Analysis.Complex.Integration.Path.Structure as Structure

-- A quantitative class of differentiable paths. The speed bound is supplied
-- once; the derivative's radii remain separately truncated. This does not
-- assume regularity (the velocity may vanish) or injectivity of the path.
private
  module Data = Structure.PathStructure ℝ ℂ ℚ₊ _≤ℝ_ IsUniformComplexCurveDerivativeOn
    (λ velocity a b B → ∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (velocity t) ≤ℝ rat (fst B))

open Data public using () renaming (UniformPath to UniformComplexPath)

module _ {a b : ℝ} (path : UniformComplexPath a b) where
  private module P = UniformComplexPath path

  pathStart pathFinish : ℂ
  pathStart = P.curve a
  pathFinish = P.curve b

