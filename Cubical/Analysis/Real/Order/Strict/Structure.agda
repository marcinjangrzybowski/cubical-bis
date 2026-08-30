module Cubical.Analysis.Real.Order.Strict.Structure where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.StrictOrder.Base
  using (IsStrictOrder; StrictOrder; isstrictorder; strictorder)

open import Cubical.Analysis.Real.Base using (ℝ; isSetℝ)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-irrefl; <ℝ-trans; <ℝ-asym)
open import Cubical.Analysis.Real.Order.Strict.Located
  using (isWeaklyLinear<ℝ)


isStrictOrder<ℝ : IsStrictOrder _<ℝ_
isStrictOrder<ℝ = isstrictorder
  isSetℝ isProp<ℝ <ℝ-irrefl <ℝ-trans <ℝ-asym isWeaklyLinear<ℝ

ℝ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℝ<StrictOrder = strictorder ℝ _<ℝ_ isStrictOrder<ℝ
