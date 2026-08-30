module Cubical.Analysis.Real.Order.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Order.Base

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

private
  module ℝTheory = PremetricTheory ℝPremetricSpace

  ℝ²PremetricSpace = PremetricProduct ℝPremetricSpace ℝPremetricSpace

  maxOnProductᶜ : C[ ℝ²PremetricSpace , ℝPremetricSpace ]
  maxOnProductᶜ = uncurry maxℝ ,
    maxOfContinuousIsContinuous
      (ℝ²PremetricSpace .snd)
      fst snd (snd productFstC) (snd productSndC)


limitsPres≤ : ∀ x y lx ly →
  ℝTheory.isLimitSeq x lx →
  ℝTheory.isLimitSeq y ly →
  (∀ n → x n ≤ℝ y n) →
  lx ≤ℝ ly
limitsPres≤ x y lx ly x-limit y-limit pointwise =
  cong fst
    (ℝTheory.isPropLimitSeq image
      (maxℝ lx ly , image-limit)
      (ly , y-is-image-limit))
  where
  pairSequence : _
  pairSequence n = x n , y n

  pairLimit : _
  pairLimit = lx , ly

  pair-limit : PremetricTheory.isLimitSeq
    ℝ²PremetricSpace pairSequence pairLimit
  pair-limit = pairPresIsLimitSeq
    {M = ℝPremetricSpace} {N = ℝPremetricSpace}
    x y lx ly x-limit y-limit

  image : _
  image = uncurry maxℝ ∘ pairSequence

  image-limit : ℝTheory.isLimitSeq image (maxℝ lx ly)
  image-limit = C→seqContinuous maxOnProductᶜ
    pairSequence pairLimit pair-limit

  image≡y : image ≡ y
  image≡y = funExt pointwise

  y-is-image-limit : ℝTheory.isLimitSeq image ly
  y-is-image-limit = subst
    (λ sequence → ℝTheory.isLimitSeq sequence ly)
    (sym image≡y) y-limit


limPres≤ : ∀ x gx y gy →
  (∀ n → x n ≤ℝ y n) →
  lim x gx ≤ℝ lim y gy
limPres≤ x gx y gy = limitsPres≤ x y (lim x gx) (lim y gy)
  (lim-isLimitSeq x gx) (lim-isLimitSeq y gy)
