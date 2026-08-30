open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.BinaryLimit
  {ℓM ℓM' ℓN ℓN' ℓT ℓT'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (T' : PremetricSpace ℓT ℓT') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.FunctionSpace

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition

module M = SequentialDefinition M'
module MP = SequentialPropertiesDefinition M'
module N = SequentialDefinition N'
module NP = SequentialPropertiesDefinition N'
module T = SequentialDefinition T'
module TP = SequentialPropertiesDefinition T'

private
  ProductSpace = PremetricProduct
    MP.ℭ̂ₛPremetricSpace NP.ℭ̂ₛPremetricSpace

module Binary = BinaryNonExpanding
  MP.ℭ̂ₛPremetricSpace NP.ℭ̂ₛPremetricSpace TP.ℭ̂ₛPremetricSpace

open PositiveRationals

private
  module TargetP = PremetricStr (TP.ℭ̂ₛPremetricSpace .snd)
  module TTheory = PremetricTheory TP.ℭ̂ₛPremetricSpace

  two : ℚ₊
  two = 1 +₊ 1

  twiceRadius : ∀ ε →
    fst (ε +₊ ε) ≡ fst (two ·₊ ε)
  twiceRadius ε = sym
    (ℚ.·DistR+ 1 1 (fst ε)
      ∙ cong₂ ℚ._+_
          (ℚ.·IdL (fst ε)) (ℚ.·IdL (fst ε)))


module Construction (f₂ : Binary.NE₂[_,_,_]) where

  open Binary.NE₂[_,_,_] f₂

  uncurried : M.ℭ̂ₛ × N.ℭ̂ₛ → T.ℭ̂ₛ
  uncurried p = fun (fst p) (snd p)

  uncurried-isLipschitzWithTwo : IsLipschitzWith
    (ProductSpace .snd) uncurried
    (TP.ℭ̂ₛPremetricSpace .snd) two
  uncurried-isLipschitzWithTwo .IsLipschitzWith.pres≈
    p q ε p≈q =
    TargetP.subst≈ (uncurried p) (uncurried q) (twiceRadius ε)
      (TargetP.isTriangular≈
        (uncurried p)
        (fun (fst q) (snd p))
        (uncurried q)
        ε ε
        (leftNE (snd p) .IsNonExpanding.pres≈
          (fst p) (fst q) ε (fst p≈q))
        (rightNE (fst q) .IsNonExpanding.pres≈
          (snd p) (snd q) ε (snd p≈q)))

  uncurriedᴸ : L[ ProductSpace , TP.ℭ̂ₛPremetricSpace ]
  uncurriedᴸ = uncurried ,
    ∣ two , uncurried-isLipschitzWithTwo ∣₁

  mapPairSeqWitness :
    ∀ {x y} → M.SeqWitness x → N.SeqWitness y →
    T.SeqWitness (λ n → fun (x n) (y n))
  mapPairSeqWitness {x} {y} = PT.map2 λ x-cauchy y-cauchy →
    LWith→presIsCauchySeq
      two uncurried uncurried-isLipschitzWithTwo
      (λ n → x n , y n)
      (pairPresIsCauchySeq
        {M = MP.ℭ̂ₛPremetricSpace}
        {N = NP.ℭ̂ₛPremetricSpace}
        x y x-cauchy y-cauchy)

  map-lim-lim : ∀ x gx y gy →
    fun (M.lim x gx) (N.lim y gy) ≡
    T.lim (λ n → fun (x n) (y n))
      (mapPairSeqWitness gx gy)
  map-lim-lim x gx y gy =
    cong fst
      (TTheory.isPropLimitSeq image
        (fun (M.lim x gx) (N.lim y gy) , image-limit)
        (T.lim image (mapPairSeqWitness gx gy)
          , TP.lim-isLimitSeq image (mapPairSeqWitness gx gy)))
    where
    pairSequence : _
    pairSequence n = x n , y n

    pairLimit : _
    pairLimit = M.lim x gx , N.lim y gy

    pair-limit : PremetricTheory.isLimitSeq
      ProductSpace pairSequence pairLimit
    pair-limit = pairPresIsLimitSeq
      {M = MP.ℭ̂ₛPremetricSpace}
      {N = NP.ℭ̂ₛPremetricSpace}
      x y
      (M.lim x gx) (N.lim y gy)
      (MP.lim-isLimitSeq x gx) (NP.lim-isLimitSeq y gy)

    image : _
    image = uncurried ∘ pairSequence

    image-limit : TTheory.isLimitSeq image (uncurried pairLimit)
    image-limit = L→seqContinuous uncurriedᴸ
      pairSequence pairLimit pair-limit


uncurried-isLipschitz :
  (f₂ : Binary.NE₂[_,_,_]) →
  isLipschitz
    (ProductSpace .snd) (Construction.uncurried f₂)
    (TP.ℭ̂ₛPremetricSpace .snd)
uncurried-isLipschitz f₂ =
  ∣ two , Construction.uncurried-isLipschitzWithTwo f₂ ∣₁

mapPairSeqWitness :
  (f₂ : Binary.NE₂[_,_,_]) →
  ∀ {x y} → M.SeqWitness x → N.SeqWitness y →
  T.SeqWitness
    (λ n → Binary.NE₂[_,_,_].fun f₂ (x n) (y n))
mapPairSeqWitness = Construction.mapPairSeqWitness

binaryNonExpanding-map-lim-lim :
  (f₂ : Binary.NE₂[_,_,_]) →
  ∀ x gx y gy →
  Binary.NE₂[_,_,_].fun f₂ (M.lim x gx) (N.lim y gy) ≡
  T.lim
    (λ n → Binary.NE₂[_,_,_].fun f₂ (x n) (y n))
    (mapPairSeqWitness f₂ gx gy)
binaryNonExpanding-map-lim-lim = Construction.map-lim-lim
