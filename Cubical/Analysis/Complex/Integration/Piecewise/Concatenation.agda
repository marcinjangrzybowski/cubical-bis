module Cubical.Analysis.Complex.Integration.Piecewise.Concatenation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.Piecewise.Base

concatenateComplexIntegrability : ∀ f {x y z} (first : PiecewiseComplexPath x y) (second : PiecewiseComplexPath y z) →
  IsPiecewiseComplexLineIntegrable f first → IsPiecewiseComplexLineIntegrable f second →
  IsPiecewiseComplexLineIntegrable f (concatenateComplexPaths first second)
concatenateComplexIntegrability f emptyPiecewisePath second firstIntegral secondIntegral = secondIntegral
concatenateComplexIntegrability f (prependComplexPiece piece rest) second (firstIntegral , remaining) secondIntegral =
  firstIntegral , concatenateComplexIntegrability f rest second remaining secondIntegral

piecewiseComplexIntegralConcatenation : ∀ f {x y z} (first : PiecewiseComplexPath x y) (second : PiecewiseComplexPath y z)
  (firstIntegral : IsPiecewiseComplexLineIntegrable f first) (secondIntegral : IsPiecewiseComplexLineIntegrable f second) →
  piecewiseComplexLineIntegral f (concatenateComplexPaths first second)
    (concatenateComplexIntegrability f first second firstIntegral secondIntegral) ≡
  piecewiseComplexLineIntegral f first firstIntegral +ℂ piecewiseComplexLineIntegral f second secondIntegral
piecewiseComplexIntegralConcatenation f emptyPiecewisePath second firstIntegral secondIntegral =
  sym (+ℂComm 0ℂ (piecewiseComplexLineIntegral f second secondIntegral) ∙ +ℂIdR (piecewiseComplexLineIntegral f second secondIntegral))
piecewiseComplexIntegralConcatenation f (prependComplexPiece piece rest) second (firstIntegral , remaining) secondIntegral =
  cong (complexLineIntegral f (piecePath piece) firstIntegral +ℂ_)
    (piecewiseComplexIntegralConcatenation f rest second remaining secondIntegral)
  ∙ +ℂAssoc (complexLineIntegral f (piecePath piece) firstIntegral)
      (piecewiseComplexLineIntegral f rest remaining) (piecewiseComplexLineIntegral f second secondIntegral)

concatenateHasPiecewiseComplexLineIntegral : ∀ f {x y z} (first : PiecewiseComplexPath x y) (second : PiecewiseComplexPath y z) v w →
  HasPiecewiseComplexLineIntegral f first v → HasPiecewiseComplexLineIntegral f second w →
  HasPiecewiseComplexLineIntegral f (concatenateComplexPaths first second) (v +ℂ w)
concatenateHasPiecewiseComplexLineIntegral f first second v w (pi , pe) (qi , qe) =
  concatenateComplexIntegrability f first second pi qi ,
  piecewiseComplexIntegralConcatenation f first second pi qi ∙ cong₂ _+ℂ_ pe qe

singleHasPiecewiseComplexLineIntegral : ∀ f {a b} (path : UniformComplexPath a b) value →
  HasComplexLineIntegral f path value → HasPiecewiseComplexLineIntegral f (singleComplexPath path) value
singleHasPiecewiseComplexLineIntegral f path value proof = ((value , proof) , tt) , +ℂIdR value

-- Add one certified piece to an already integrated tail. Keep the integral
-- data and the equality of values separate, also for domain-local clients.
opaque
  prependHasPiecewiseComplexLineIntegral : ∀ f {x y z} (piece : ComplexPathPiece x y)
    (rest : PiecewiseComplexPath y z) first remaining →
    HasComplexLineIntegral f (piecePath piece) first →
    HasPiecewiseComplexLineIntegral f rest remaining →
    HasPiecewiseComplexLineIntegral f (prependComplexPiece piece rest) (first +ℂ remaining)
  prependHasPiecewiseComplexLineIntegral f piece rest first remaining firstProof (restData , restValue) =
    ((first , firstProof) , restData) , cong (first +ℂ_) restValue
