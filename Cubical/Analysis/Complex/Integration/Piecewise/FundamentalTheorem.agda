module Cubical.Analysis.Complex.Integration.Piecewise.FundamentalTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
import Cubical.Analysis.Complex.Modulus.DistanceAlgebra as Algebra
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Bounded
open import Cubical.Analysis.Complex.Integration.Piecewise.Base

private module C = Algebra.DistanceAlgebra ℂCommRing

-- This finite telescoping argument also works with other ways of proving
-- the individual piece integrals. The common F makes corner values cancel.
private
  PieceIntegrals : (ℂ → ℂ) → (ℂ → ℂ) → ∀ {z w} → PiecewiseComplexPath z w → Type₀
  PieceIntegrals F f = AllComplexPieces (λ path → HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path)))

  integralData : ∀ F f {z w} (chain : PiecewiseComplexPath z w) → PieceIntegrals F f chain → IsPiecewiseComplexLineIntegrable f chain
  integralData F f emptyPiecewisePath proof = tt
  integralData F f (prependComplexPiece piece rest) (first , remaining) =
    (F (pathFinish (piecePath piece)) -ℂ F (pathStart (piecePath piece)) , first) , integralData F f rest remaining

  opaque
    endpointValue : ∀ F f {z w} (chain : PiecewiseComplexPath z w) (proof : PieceIntegrals F f chain) →
      piecewiseComplexLineIntegral f chain (integralData F f chain proof) ≡ F w -ℂ F z
    endpointValue F f {z} emptyPiecewisePath proof = sym (+ℂInvR (F z))
    endpointValue F f {z} {w} (prependComplexPiece {x = m} piece rest) (first , remaining) =
      cong₂ _+ℂ_ (cong₂ _-ℂ_ (cong F (pieceFinish piece)) (cong F (pieceStart piece))) (endpointValue F f rest remaining)
      ∙ +ℂComm (F m -ℂ F z) (F w -ℂ F m)
      ∙ sym (C.difference-chain (F w) (F m) (F z))

piecewisePrimitiveFromPieceIntegrals : ∀ F f {z w} (chain : PiecewiseComplexPath z w) →
  AllComplexPieces (λ path → HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))) chain →
  HasPiecewiseComplexLineIntegral f chain (F w -ℂ F z)
piecewisePrimitiveFromPieceIntegrals F f chain proof = integralData F f chain proof , endpointValue F f chain proof

IsPiecewiseUniformPrimitive : (ℂ → ℂ) → (ℂ → ℂ) → ∀ {z w} → PiecewiseComplexPath z w → Type₀
IsPiecewiseUniformPrimitive F f = AllComplexPieces (IsBoundedUniformPrimitiveAlongPath F f)

private
  primitivePieceIntegrals : ∀ F f {z w} (chain : PiecewiseComplexPath z w) → IsPiecewiseUniformPrimitive F f chain →
    AllComplexPieces (λ path → HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))) chain
  primitivePieceIntegrals F f emptyPiecewisePath proof = tt
  primitivePieceIntegrals F f (prependComplexPiece piece rest) (first , remaining) =
    boundedUniformPrimitiveHasComplexLineIntegral (piecePath piece) F f first , primitivePieceIntegrals F f rest remaining

fundamentalTheoremOfPiecewiseComplexLineIntegrals : ∀ F f {z w} (chain : PiecewiseComplexPath z w) →
  IsPiecewiseUniformPrimitive F f chain → HasPiecewiseComplexLineIntegral f chain (F w -ℂ F z)
fundamentalTheoremOfPiecewiseComplexLineIntegrals F f chain estimates =
  piecewisePrimitiveFromPieceIntegrals F f chain (primitivePieceIntegrals F f chain estimates)

closedPiecewisePrimitiveHasZeroIntegral : ∀ F f {z} (chain : PiecewiseComplexPath z z) →
  IsPiecewiseUniformPrimitive F f chain → HasPiecewiseComplexLineIntegral f chain 0ℂ
closedPiecewisePrimitiveHasZeroIntegral F f {z} chain estimates =
  subst (HasPiecewiseComplexLineIntegral f chain) (+ℂInvR (F z))
    (fundamentalTheoremOfPiecewiseComplexLineIntegrals F f chain estimates)

piecewisePrimitivePathIndependent : ∀ F f {z w} (first second : PiecewiseComplexPath z w) →
  IsPiecewiseUniformPrimitive F f first → IsPiecewiseUniformPrimitive F f second → ∀ v u →
  HasPiecewiseComplexLineIntegral f first v → HasPiecewiseComplexLineIntegral f second u → v ≡ u
piecewisePrimitivePathIndependent F f {z} {w} first second firstEstimate secondEstimate v u vi ui =
  piecewiseComplexLineIntegralUnique f first v (F w -ℂ F z) vi
    (fundamentalTheoremOfPiecewiseComplexLineIntegrals F f first firstEstimate)
  ∙ sym (piecewiseComplexLineIntegralUnique f second u (F w -ℂ F z) ui
    (fundamentalTheoremOfPiecewiseComplexLineIntegrals F f second secondEstimate))
