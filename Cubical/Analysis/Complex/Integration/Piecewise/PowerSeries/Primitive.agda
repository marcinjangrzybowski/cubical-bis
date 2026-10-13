module Cubical.Analysis.Complex.Integration.Piecewise.PowerSeries.Primitive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Domain
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.PowerSeries.Primitive
open import Cubical.Analysis.Complex.Integration.Piecewise.Base
open import Cubical.Analysis.Complex.Integration.Piecewise.Concatenation
import Cubical.Analysis.Complex.Modulus.DistanceAlgebra as Algebra

private module C = Algebra.DistanceAlgebra ℂCommRing

-- A single native convergent series gives its own common primitive on a
-- centered closed norm ball. Unlike arbitrary local primitive certificates,
-- no ambient primitive or matching constants at the corners are supplied.
module _ (center : ℂ) (coefficients : ComplexSequence) (radius : ℝ)
  (nonnegative : 0ℝ ≤ℝ radius)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients radius))
  (constant : ℂ) (f : ℂ → ℂ) where

  ConvergentPowerSeriesPieceData : ∀ {a b} → UniformComplexPath a b → Type₀
  ConvergentPowerSeriesPieceData {a} {b} path =
    (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (UniformComplexPath.curve path t -ℂ center) ≤ℝ radius) ×
    (∀ t → a ≤ℝ t → t ≤ℝ b → HasComplexSum
      (powerSeriesTermsℂ coefficients (UniformComplexPath.curve path t -ℂ center)) (f (UniformComplexPath.curve path t)))

  convergentPowerSeriesPiecewiseIntegrable : ∀ {z w} (chain : PiecewiseComplexPath z w) →
    AllComplexPieces ConvergentPowerSeriesPieceData chain → IsPiecewiseComplexLineIntegrable f chain
  convergentPowerSeriesPiecewiseIntegrable chain = mapAllComplexPieces ConvergentPowerSeriesPieceData
    (IsComplexLineIntegrable f)
    (λ path certificate → convergentPowerSeriesComplexLineIntegrable path center coefficients radius nonnegative
      (fst certificate) witness constant f (snd certificate)) chain

  private
    integrated : ComplexSequence
    integrated = formalPrimitiveℂ constant coefficients

  opaque
    convergentPowerSeriesPiecewiseIntegralFromEndpointSums : ∀ {z w} (chain : PiecewiseComplexPath z w) →
      AllComplexPieces ConvergentPowerSeriesPieceData chain → ∀ start finish →
      HasComplexSum (powerSeriesTermsℂ integrated (z -ℂ center)) start →
      HasComplexSum (powerSeriesTermsℂ integrated (w -ℂ center)) finish →
      HasPiecewiseComplexLineIntegral f chain (finish -ℂ start)
    convergentPowerSeriesPiecewiseIntegralFromEndpointSums {z} emptyPiecewisePath certificate start finish startSum finishSum =
      tt , (sym (+ℂInvR start) ∙ cong (_-ℂ start)
        (complexSumUnique (powerSeriesTermsℂ integrated (z -ℂ center)) start finish startSum finishSum))
    convergentPowerSeriesPiecewiseIntegralFromEndpointSums
      {z} {w} (prependComplexPiece {x = middle} piece rest) ((bounded , sums) , remaining) start finish startSum finishSum =
      subst (HasPiecewiseComplexLineIntegral f (prependComplexPiece piece rest))
        (+ℂComm (middleValue -ℂ start) (finish -ℂ middleValue) ∙ sym (C.difference-chain finish middleValue start))
        (prependHasPiecewiseComplexLineIntegral f piece rest (middleValue -ℂ start) (finish -ℂ middleValue)
          firstIntegral
          (convergentPowerSeriesPiecewiseIntegralFromEndpointSums rest remaining middleValue finish middleSum finishSum))
      where
      module P = UniformComplexPath (piecePath piece)
      middlePoint : ClosedComplexNormRadius radius
      middlePoint = middle -ℂ center , subst (λ z → normℂ (z -ℂ center) ≤ℝ radius) (pieceFinish piece)
        (bounded (fst (snd piece)) P.ordered (≤ℝ-refl (fst (snd piece))))
      middleValue : ℂ
      middleValue = closedComplexPowerSeriesPrimitive coefficients radius witness constant nonnegative middlePoint
      middleSum : HasComplexSum (powerSeriesTermsℂ integrated (middle -ℂ center)) middleValue
      middleSum = closedComplexPowerSeriesPrimitiveHasSum coefficients radius witness constant nonnegative middlePoint
      firstIntegral : HasComplexLineIntegral f (piecePath piece) (middleValue -ℂ start)
      firstIntegral = convergentPowerSeriesIntegralFromEndpointSums (piecePath piece) center coefficients radius nonnegative bounded witness
        constant f sums start middleValue
        (subst (λ z → HasComplexSum (powerSeriesTermsℂ integrated (z -ℂ center)) start) (sym (pieceStart piece)) startSum)
        (subst (λ z → HasComplexSum (powerSeriesTermsℂ integrated (z -ℂ center)) middleValue) (sym (pieceFinish piece)) middleSum)

  private
    -- Match a chain with independent endpoints; specializing both indices
    -- before matching the empty path would require axiom K.
    closedIntegral : ∀ {z w} (chain : PiecewiseComplexPath z w) →
      AllComplexPieces ConvergentPowerSeriesPieceData chain → w ≡ z →
      HasPiecewiseComplexLineIntegral f chain 0ℂ
    closedIntegral emptyPiecewisePath certificate closed = tt , refl
    closedIntegral {z} {w} (prependComplexPiece piece rest) (first , remaining) closed =
      subst (HasPiecewiseComplexLineIntegral f (prependComplexPiece piece rest)) (+ℂInvR startValue)
        (convergentPowerSeriesPiecewiseIntegralFromEndpointSums (prependComplexPiece piece rest) (first , remaining)
          startValue startValue startSum finishSum)
      where
      module P = UniformComplexPath (piecePath piece)
      startPoint : ClosedComplexNormRadius radius
      startPoint = z -ℂ center , subst (λ z → normℂ (z -ℂ center) ≤ℝ radius) (pieceStart piece)
        (fst first (fst piece) (≤ℝ-refl (fst piece)) P.ordered)
      startValue : ℂ
      startValue = closedComplexPowerSeriesPrimitive coefficients radius witness constant nonnegative startPoint
      startSum : HasComplexSum (powerSeriesTermsℂ integrated (z -ℂ center)) startValue
      startSum = closedComplexPowerSeriesPrimitiveHasSum coefficients radius witness constant nonnegative startPoint
      finishSum : HasComplexSum (powerSeriesTermsℂ integrated (w -ℂ center)) startValue
      finishSum = subst (λ endpoint → HasComplexSum (powerSeriesTermsℂ integrated (endpoint -ℂ center)) startValue)
        (sym closed) startSum

  closedConvergentPowerSeriesHasZeroPiecewiseIntegral : ∀ {z} (chain : PiecewiseComplexPath z z) →
    AllComplexPieces ConvergentPowerSeriesPieceData chain → HasPiecewiseComplexLineIntegral f chain 0ℂ
  closedConvergentPowerSeriesHasZeroPiecewiseIntegral chain certificate = closedIntegral chain certificate refl

  convergentPowerSeriesPiecewisePathIndependent : ∀ {z w} (first second : PiecewiseComplexPath z w) →
    AllComplexPieces ConvergentPowerSeriesPieceData first → AllComplexPieces ConvergentPowerSeriesPieceData second →
    ∀ start finish → HasComplexSum (powerSeriesTermsℂ integrated (z -ℂ center)) start →
    HasComplexSum (powerSeriesTermsℂ integrated (w -ℂ center)) finish →
    ∀ v u → HasPiecewiseComplexLineIntegral f first v → HasPiecewiseComplexLineIntegral f second u → v ≡ u
  convergentPowerSeriesPiecewisePathIndependent first second firstData secondData start finish startSum finishSum v u vi ui =
    piecewiseComplexLineIntegralUnique f first v (finish -ℂ start) vi
      (convergentPowerSeriesPiecewiseIntegralFromEndpointSums first firstData start finish startSum finishSum)
    ∙ sym (piecewiseComplexLineIntegralUnique f second u (finish -ℂ start) ui
      (convergentPowerSeriesPiecewiseIntegralFromEndpointSums second secondData start finish startSum finishSum))
