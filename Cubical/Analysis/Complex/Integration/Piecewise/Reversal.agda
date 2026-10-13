module Cubical.Analysis.Complex.Integration.Piecewise.Reversal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Reversal
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Reversal
open import Cubical.Analysis.Complex.Integration.LineIntegral.Bounded
open import Cubical.Analysis.Complex.Integration.Piecewise.Base
open import Cubical.Analysis.Complex.Integration.Piecewise.Concatenation
open import Cubical.Analysis.Complex.Integration.Piecewise.FundamentalTheorem

reverseComplexPiece : ∀ {z w} → ComplexPathPiece z w → ComplexPathPiece w z
reverseComplexPiece (a , b , path , start , finish) = a , b , reverseComplexPath path ,
  (reverseComplexPathStartsAtFinish path ∙ finish) , (reverseComplexPathFinishesAtStart path ∙ start)

reversePiecewiseComplexPath : ∀ {z w} → PiecewiseComplexPath z w → PiecewiseComplexPath w z
reversePiecewiseComplexPath emptyPiecewisePath = emptyPiecewisePath
reversePiecewiseComplexPath (prependComplexPiece piece rest) =
  concatenateComplexPaths (reversePiecewiseComplexPath rest) (prependComplexPiece (reverseComplexPiece piece) emptyPiecewisePath)

reversePiecewiseConcatenation : ∀ {x y z} (first : PiecewiseComplexPath x y) (second : PiecewiseComplexPath y z) →
  reversePiecewiseComplexPath (concatenateComplexPaths first second) ≡
  concatenateComplexPaths (reversePiecewiseComplexPath second) (reversePiecewiseComplexPath first)
reversePiecewiseConcatenation emptyPiecewisePath second = sym (concatenateComplexPathsRightUnit (reversePiecewiseComplexPath second))
reversePiecewiseConcatenation (prependComplexPiece piece rest) second =
  cong (λ p → concatenateComplexPaths p (prependComplexPiece (reverseComplexPiece piece) emptyPiecewisePath))
    (reversePiecewiseConcatenation rest second)
  ∙ concatenateComplexPathsAssoc (reversePiecewiseComplexPath second) (reversePiecewiseComplexPath rest)
      (prependComplexPiece (reverseComplexPiece piece) emptyPiecewisePath)

private
  ReversalLaw : (ℂ → ℂ) → ∀ {a b} → UniformComplexPath a b → Type₀
  ReversalLaw f path = ∀ v → HasComplexLineIntegral f path v → HasComplexLineIntegral f (reverseComplexPath path) (-ℂ v)

  reverseIntegrableData : ∀ f {z w} (chain : PiecewiseComplexPath z w) → AllComplexPieces (ReversalLaw f) chain →
    IsPiecewiseComplexLineIntegrable f chain → IsPiecewiseComplexLineIntegrable f (reversePiecewiseComplexPath chain)
  reverseIntegrableData f emptyPiecewisePath laws proof = tt
  reverseIntegrableData f (prependComplexPiece piece rest) (firstLaw , restLaws) (first , remaining) =
    concatenateComplexIntegrability f (reversePiecewiseComplexPath rest)
      (prependComplexPiece (reverseComplexPiece piece) emptyPiecewisePath)
      (reverseIntegrableData f rest restLaws remaining) ((-ℂ fst first , firstLaw (fst first) (snd first)) , tt)

  opaque
    reverseIntegralValue : ∀ f {z w} (chain : PiecewiseComplexPath z w) (laws : AllComplexPieces (ReversalLaw f) chain)
      (proof : IsPiecewiseComplexLineIntegrable f chain) →
      piecewiseComplexLineIntegral f (reversePiecewiseComplexPath chain) (reverseIntegrableData f chain laws proof)
        ≡ -ℂ piecewiseComplexLineIntegral f chain proof
    reverseIntegralValue f emptyPiecewisePath laws proof = sym ℂRing.0Selfinverse
    reverseIntegralValue f (prependComplexPiece piece rest) (firstLaw , restLaws) (first , remaining) =
      piecewiseComplexIntegralConcatenation f (reversePiecewiseComplexPath rest)
        (prependComplexPiece (reverseComplexPiece piece) emptyPiecewisePath)
        (reverseIntegrableData f rest restLaws remaining) ((-ℂ fst first , firstLaw (fst first) (snd first)) , tt)
      ∙ cong₂ _+ℂ_ (reverseIntegralValue f rest restLaws remaining) (+ℂIdR (-ℂ fst first))
      ∙ ℂRing.-Dist (piecewiseComplexLineIntegral f rest remaining) (fst first)
      ∙ cong -ℂ_ (+ℂComm (piecewiseComplexLineIntegral f rest remaining) (fst first))

  reverseData : ∀ f {z w} (chain : PiecewiseComplexPath z w) → AllComplexPieces (ReversalLaw f) chain →
    (proof : IsPiecewiseComplexLineIntegrable f chain) →
    HasPiecewiseComplexLineIntegral f (reversePiecewiseComplexPath chain) (-ℂ piecewiseComplexLineIntegral f chain proof)
  reverseData f chain laws proof = reverseIntegrableData f chain laws proof , reverseIntegralValue f chain laws proof

-- Reversal reverses the order of pieces as well as each actual curve.
-- The following assumptions are on the original pieces only.
reverseHasPiecewiseComplexLineIntegral : ∀ f {z w} (chain : PiecewiseComplexPath z w) →
  AllComplexPieces (λ {a} {b} path → isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (complexLineIntegrand f path ∘ fst) (ℂPremetricSpace .snd)) chain →
  ∀ value → HasPiecewiseComplexLineIntegral f chain value →
  HasPiecewiseComplexLineIntegral f (reversePiecewiseComplexPath chain) (-ℂ value)
reverseHasPiecewiseComplexLineIntegral f chain continuous value (proof , equal) =
  subst (HasPiecewiseComplexLineIntegral f (reversePiecewiseComplexPath chain)) (cong -ℂ_ equal)
    (reverseData f chain (mapAllComplexPieces
      (λ {a} {b} path → isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
        (complexLineIntegrand f path ∘ fst) (ℂPremetricSpace .snd)) (ReversalLaw f)
      (λ path near → reverseHasComplexLineIntegral path f near) chain continuous) proof)

reversePrimitiveHasPiecewiseComplexLineIntegral : ∀ F f {z w} (chain : PiecewiseComplexPath z w) →
  IsPiecewiseUniformPrimitive F f chain → ∀ value → HasPiecewiseComplexLineIntegral f chain value →
  HasPiecewiseComplexLineIntegral f (reversePiecewiseComplexPath chain) (-ℂ value)
reversePrimitiveHasPiecewiseComplexLineIntegral F f chain estimates value (proof , equal) =
  subst (HasPiecewiseComplexLineIntegral f (reversePiecewiseComplexPath chain)) (cong -ℂ_ equal)
    (reverseData f chain (mapAllComplexPieces (IsBoundedUniformPrimitiveAlongPath F f) (ReversalLaw f)
      (λ path estimate → reversePrimitiveHasComplexLineIntegral path F f estimate) chain estimates) proof)
