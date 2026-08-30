module Cubical.Analysis.Real.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Base
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Metric.Distance

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.FunctionSpace

import Cubical.Analysis.Completion.Limit as LimitDefinition
import Cubical.Analysis.Completion.BinaryLimit as BinaryLimitDefinition

private
  module Limit = LimitDefinition ℚPremetricSpace ℚPremetricSpace
  module BinaryLimit = BinaryLimitDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace
  module RealBinary = BinaryNonExpanding
    ℝPremetricSpace ℝPremetricSpace ℝPremetricSpace


negSeqWitness : ∀ {x} → SeqWitness x → SeqWitness (-_ ∘ x)
negSeqWitness = Limit.mapSeqWitnessNonExpanding
  (-_ , neg-isNonExpanding)

neg-lim : ∀ x gx →
  - lim x gx ≡ lim (-_ ∘ x) (negSeqWitness gx)
neg-lim = Limit.nonExpanding-map-lim
  (-_ , neg-isNonExpanding)

absSeqWitness : ∀ {x} → SeqWitness x → SeqWitness (absℝ ∘ x)
absSeqWitness = Limit.mapSeqWitnessNonExpanding
  (absℝ , abs-isNonExpanding)

abs-lim : ∀ x gx →
  absℝ (lim x gx) ≡ lim (absℝ ∘ x) (absSeqWitness gx)
abs-lim = Limit.nonExpanding-map-lim
  (absℝ , abs-isNonExpanding)

private
  addition₂ : RealBinary.NE₂[_,_,_]
  addition₂ .RealBinary.NE₂[_,_,_].fun = _+_
  addition₂ .RealBinary.NE₂[_,_,_].leftNE = add-isNonExpanding₁
  addition₂ .RealBinary.NE₂[_,_,_].rightNE = add-isNonExpanding₂

  distance₂ : RealBinary.NE₂[_,_,_]
  distance₂ .RealBinary.NE₂[_,_,_].fun = distanceℝ
  distance₂ .RealBinary.NE₂[_,_,_].leftNE = distance-isNonExpanding₁
  distance₂ .RealBinary.NE₂[_,_,_].rightNE = distance-isNonExpanding₂

  max₂ : RealBinary.NE₂[_,_,_]
  max₂ .RealBinary.NE₂[_,_,_].fun = maxℝ
  max₂ .RealBinary.NE₂[_,_,_].leftNE = max-isNonExpanding₁
  max₂ .RealBinary.NE₂[_,_,_].rightNE = max-isNonExpanding₂

  min₂ : RealBinary.NE₂[_,_,_]
  min₂ .RealBinary.NE₂[_,_,_].fun = minℝ
  min₂ .RealBinary.NE₂[_,_,_].leftNE = min-isNonExpanding₁
  min₂ .RealBinary.NE₂[_,_,_].rightNE = min-isNonExpanding₂


addSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → x n + y n)
addSeqWitness = BinaryLimit.mapPairSeqWitness addition₂

add-lim-lim : ∀ x gx y gy →
  lim x gx + lim y gy ≡
  lim (λ n → x n + y n) (addSeqWitness gx gy)
add-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim addition₂

distanceSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → distanceℝ (x n) (y n))
distanceSeqWitness = BinaryLimit.mapPairSeqWitness distance₂

distance-lim-lim : ∀ x gx y gy →
  distanceℝ (lim x gx) (lim y gy) ≡
  lim (λ n → distanceℝ (x n) (y n))
    (distanceSeqWitness gx gy)
distance-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim distance₂

maxSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → maxℝ (x n) (y n))
maxSeqWitness = BinaryLimit.mapPairSeqWitness max₂

max-lim-lim : ∀ x gx y gy →
  maxℝ (lim x gx) (lim y gy) ≡
  lim (λ n → maxℝ (x n) (y n)) (maxSeqWitness gx gy)
max-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim max₂

minSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → minℝ (x n) (y n))
minSeqWitness = BinaryLimit.mapPairSeqWitness min₂

min-lim-lim : ∀ x gx y gy →
  minℝ (lim x gx) (lim y gy) ≡
  lim (λ n → minℝ (x n) (y n)) (minSeqWitness gx gy)
min-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim min₂


-- Multiplication is not globally non-expanding, so its synchronized limit
-- rule retains the explicitly supplied image witness from the
-- completion-centered lift.

mul-lim-lim : ∀ x gx y gy imageWitness →
  lim x gx · lim y gy ≡
  lim (λ n → x n · y n) imageWitness
mul-lim-lim = multiplyℝ-lim-lim
