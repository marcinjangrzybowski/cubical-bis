module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent


-- The sum domain records exactly the third local gap needed for tangent:
-- both inputs and their sum have cosine apart from zero.

TangentPair : Type
TangentPair = TangentDomain × TangentDomain


tangentPairSum : TangentPair → ℝ
tangentPairSum points =
  fst (fst points) + fst (snd points)


TangentAdditionDomain : Type
TangentAdditionDomain =
  Σ[ points ∈ TangentPair ]
    0ℝ #ℝ
      cosℝ (fst (fst points) + fst (snd points))


tangentAdditionDomainPoint : (points : TangentPair) →
  0ℝ #ℝ cosℝ (fst (fst points) + fst (snd points)) →
  TangentAdditionDomain
tangentAdditionDomainPoint points sum-apart =
  points , sum-apart


tangentAdditionLeft :
  TangentAdditionDomain → TangentDomain
tangentAdditionLeft addition-data = fst (fst addition-data)


tangentAdditionRight :
  TangentAdditionDomain → TangentDomain
tangentAdditionRight addition-data = snd (fst addition-data)


tangentAdditionSumPoint :
  TangentAdditionDomain → TangentDomain
tangentAdditionSumPoint addition-data =
  (fst (fst (fst addition-data)) +
    fst (snd (fst addition-data))) ,
  snd addition-data


tangentAdditionDenominator :
  TangentDomain → TangentDomain → ℝ
tangentAdditionDenominator left right =
  1ℝ - (tanℝ left · tanℝ right)


tangentAdditionNumerator :
  TangentDomain → TangentDomain → ℝ
tangentAdditionNumerator left right =
  tanℝ left + tanℝ right


secantAdditionNumerator :
  TangentDomain → TangentDomain → ℝ
secantAdditionNumerator left right =
  secℝ left · secℝ right


tangentAdditionCommonCosineFactor :
  TangentDomain → TangentDomain → ℝ
tangentAdditionCommonCosineFactor left right =
  cosℝ (fst left) · cosℝ (fst right)
