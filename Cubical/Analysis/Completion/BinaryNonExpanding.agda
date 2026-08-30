open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Completion.BinaryNonExpanding
  {ℓM ℓM' ℓN ℓN' ℓT ℓT'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN')
  (T' : PremetricSpace ℓT ℓT') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace

import Cubical.Analysis.Completion.Extensionality
  as ExtensionalityDefinition
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as RegularLiftDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as ComparisonDefinition

module M = SequentialDefinition M'
module MP = SequentialPropertiesDefinition M'
module N = SequentialDefinition N'
module NP = SequentialPropertiesDefinition N'
module T = SequentialDefinition T'
module TP = SequentialPropertiesDefinition T'
module MC = ComparisonDefinition M'
module NC = ComparisonDefinition N'
module TC = ComparisonDefinition T'
module Ext = ExtensionalityDefinition M'
module ExtN = ExtensionalityDefinition N'
module BaseBinary = BinaryNonExpanding M' N' T'
module CompletedBinary = BinaryNonExpanding
  MP.ℭ̂ₛPremetricSpace NP.ℭ̂ₛPremetricSpace TP.ℭ̂ₛPremetricSpace

open CategoryStructures
open PositiveRationals


private
  toRegularMⁿ : NE[ MP.ℭ̂ₛPremetricSpace , MC.C.ℭPremetricSpace ]
  toRegularMⁿ = MC.toRegular ,
    isIsometry→IsNonExpanding
      (MP.ℭ̂ₛPremetricSpace .snd) MC.sequentialRegularEquiv
      (MC.C.ℭPremetricSpace .snd) MC.sequentialRegularIsometry

  toRegularNⁿ : NE[ NP.ℭ̂ₛPremetricSpace , NC.C.ℭPremetricSpace ]
  toRegularNⁿ = NC.toRegular ,
    isIsometry→IsNonExpanding
      (NP.ℭ̂ₛPremetricSpace .snd) NC.sequentialRegularEquiv
      (NC.C.ℭPremetricSpace .snd) NC.sequentialRegularIsometry

  fromRegularTⁿ : NE[ TC.C.ℭPremetricSpace , TP.ℭ̂ₛPremetricSpace ]
  fromRegularTⁿ = TC.fromRegular ,
    isIsometry→IsNonExpanding
      (TC.C.ℭPremetricSpace .snd) TC.regularSequentialEquiv
      (TP.ℭ̂ₛPremetricSpace .snd) TC.regularSequentialIsometry


module Construction (f₂ : BaseBinary.NE₂[_,_,_]) where

  open BaseBinary.NE₂[_,_,_] f₂

  private
    regularFunction : M' .fst → N' .fst → TC.Regular.ℭ
    regularFunction x y = TC.Regular.ι (fun x y)

    regular-left-lip : ∀ y → IsLipschitzWith
      (M' .snd) (flip regularFunction y)
      (TC.C.ℭPremetricSpace .snd) 1
    regular-left-lip y = isNonExpanding→isLipschitzWith1
      (M' .snd) (flip regularFunction y)
      (TC.C.ℭPremetricSpace .snd)
      record { pres≈ = λ x x' ε x≈x' →
        TC.Regular.ι-ι (fun x y) (fun x' y) ε
          (leftNE y .IsNonExpanding.pres≈ x x' ε x≈x') }

    regular-right-lip : ∀ x → IsLipschitzWith
      (N' .snd) (regularFunction x)
      (TC.C.ℭPremetricSpace .snd) 1
    regular-right-lip x = isNonExpanding→isLipschitzWith1
      (N' .snd) (regularFunction x)
      (TC.C.ℭPremetricSpace .snd)
      record { pres≈ = λ y y' ε y≈y' →
        TC.Regular.ι-ι (fun x y) (fun x y') ε
          (rightNE x .IsNonExpanding.pres≈ y y' ε y≈y') }

    regularBinary = RegularLiftDefinition.liftLipschitzBinaryWith
      M' N' TC.C.ℭPremetricSpace TC.C.isCompleteℭ
      1 1 regularFunction regular-left-lip regular-right-lip

    regularCompletedFunction :
      MC.Regular.ℭ → NC.Regular.ℭ → TC.Regular.ℭ
    regularCompletedFunction = fst regularBinary

  transportedFunction : M.ℭ̂ₛ → N.ℭ̂ₛ → T.ℭ̂ₛ
  transportedFunction x y = TC.fromRegular
    (regularCompletedFunction (MC.toRegular x) (NC.toRegular y))

  private
    regular-rightNE : ∀ x → NE[
      NC.C.ℭPremetricSpace , TC.C.ℭPremetricSpace ]
    regular-rightNE x = regularCompletedFunction x ,
      isLipschitzWith1→isNonExpanding
        (NC.C.ℭPremetricSpace .snd) (regularCompletedFunction x)
        (TC.C.ℭPremetricSpace .snd) (fst (snd regularBinary) x)

    regular-left-lip-completed : ∀ y → IsLipschitzWith
      (MC.C.ℭPremetricSpace .snd)
      (flip regularCompletedFunction y)
      (TC.C.ℭPremetricSpace .snd) 1
    regular-left-lip-completed y .IsLipschitzWith.pres≈
      x x' ε x≈x' =
      ≈→→pointwise NC.Regular.ℭ TC.C.ℭPremetricSpace
        (regularCompletedFunction x) (regularCompletedFunction x')
        (1 ·₊ ε)
        ((snd (snd regularBinary)) .IsLipschitzWith.pres≈
          x x' ε x≈x') y

    regular-leftNE : ∀ y → NE[
      MC.C.ℭPremetricSpace , TC.C.ℭPremetricSpace ]
    regular-leftNE y = flip regularCompletedFunction y ,
      isLipschitzWith1→isNonExpanding
        (MC.C.ℭPremetricSpace .snd) (flip regularCompletedFunction y)
        (TC.C.ℭPremetricSpace .snd) (regular-left-lip-completed y)

  transported-leftNE : ∀ y → IsNonExpanding
    (MP.ℭ̂ₛPremetricSpace .snd) (flip transportedFunction y)
    (TP.ℭ̂ₛPremetricSpace .snd)
  transported-leftNE y = snd
    (fromRegularTⁿ ∘NE
      (regular-leftNE (NC.toRegular y) ∘NE toRegularMⁿ))

  transported-rightNE : ∀ x → IsNonExpanding
    (NP.ℭ̂ₛPremetricSpace .snd) (transportedFunction x)
    (TP.ℭ̂ₛPremetricSpace .snd)
  transported-rightNE x = snd
    (fromRegularTⁿ ∘NE
      (regular-rightNE (MC.toRegular x) ∘NE toRegularNⁿ))

  transported-ι : ∀ p q →
    transportedFunction (M.ι p) (N.ι q) ≡ T.ι (fun p q)
  transported-ι p q =
    cong
      (λ u → TC.fromRegular
        (regularCompletedFunction u (NC.toRegular (N.ι q))))
      (MC.toRegular-ι p)
    ∙ cong
        (λ v → TC.fromRegular
          (regularCompletedFunction (MC.Regular.ι p) v))
        (NC.toRegular-ι q)
    ∙ cong TC.fromRegular
        (funExt⁻ (funExt⁻
          (RegularLiftDefinition.liftBinary∘ι∘ι
            M' N' TC.C.ℭPremetricSpace TC.C.isCompleteℭ
            1 1 regularFunction regular-left-lip regular-right-lip)
          p) q)
    ∙ TC.fromRegular-ι (fun p q)

  -- Compatibility surface: the implementation now uses one transported
  -- binary lift, while retaining the original Construction names.
  uncurried : M.ℭ̂ₛ × N.ℭ̂ₛ → T.ℭ̂ₛ
  uncurried p = transportedFunction (fst p) (snd p)

  sequentialFunction : M.ℭ̂ₛ → N.ℭ̂ₛ → T.ℭ̂ₛ
  sequentialFunction = curry uncurried

  sequential-leftNE : ∀ y → IsNonExpanding
    (MP.ℭ̂ₛPremetricSpace .snd) (flip sequentialFunction y)
    (TP.ℭ̂ₛPremetricSpace .snd)
  sequential-leftNE = transported-leftNE

  sequential-rightNE : ∀ x → IsNonExpanding
    (NP.ℭ̂ₛPremetricSpace .snd) (sequentialFunction x)
    (TP.ℭ̂ₛPremetricSpace .snd)
  sequential-rightNE = transported-rightNE

  sequentialFunction-ι : ∀ p q →
    sequentialFunction (M.ι p) (N.ι q) ≡ T.ι (fun p q)
  sequentialFunction-ι = transported-ι


liftBinaryNonExpanding :
  BaseBinary.NE₂[_,_,_] → CompletedBinary.NE₂[_,_,_]
liftBinaryNonExpanding f₂ .CompletedBinary.NE₂[_,_,_].fun =
  Construction.sequentialFunction f₂
liftBinaryNonExpanding f₂ .CompletedBinary.NE₂[_,_,_].leftNE =
  Construction.sequential-leftNE f₂
liftBinaryNonExpanding f₂ .CompletedBinary.NE₂[_,_,_].rightNE =
  Construction.sequential-rightNE f₂

liftBinaryNonExpanding-ι : ∀ f₂ p q →
  CompletedBinary.NE₂[_,_,_].fun (liftBinaryNonExpanding f₂)
    (M.ι p) (N.ι q) ≡
  T.ι (BaseBinary.NE₂[_,_,_].fun f₂ p q)
liftBinaryNonExpanding-ι = Construction.sequentialFunction-ι

liftBinaryNonExpanding-fun-ext :
  (f₂ g₂ : BaseBinary.NE₂[_,_,_]) →
  (∀ p q →
    BaseBinary.NE₂[_,_,_].fun f₂ p q ≡
    BaseBinary.NE₂[_,_,_].fun g₂ p q) →
  CompletedBinary.NE₂[_,_,_].fun (liftBinaryNonExpanding f₂) ≡
  CompletedBinary.NE₂[_,_,_].fun (liftBinaryNonExpanding g₂)
liftBinaryNonExpanding-fun-ext f₂ g₂ on-base =
  funExt λ x → funExt λ y →
    funExt⁻
      (Ext.nonExpandingExtensionality TP.ℭ̂ₛPremetricSpace
        (λ u → CompletedBinary.NE₂[_,_,_].fun
          (liftBinaryNonExpanding f₂) u y)
        (λ u → CompletedBinary.NE₂[_,_,_].fun
          (liftBinaryNonExpanding g₂) u y)
        (CompletedBinary.NE₂[_,_,_].leftNE
          (liftBinaryNonExpanding f₂) y)
        (CompletedBinary.NE₂[_,_,_].leftNE
          (liftBinaryNonExpanding g₂) y)
        λ p →
          funExt⁻
            (ExtN.nonExpandingExtensionality TP.ℭ̂ₛPremetricSpace
              (CompletedBinary.NE₂[_,_,_].fun
                (liftBinaryNonExpanding f₂) (M.ι p))
              (CompletedBinary.NE₂[_,_,_].fun
                (liftBinaryNonExpanding g₂) (M.ι p))
              (CompletedBinary.NE₂[_,_,_].rightNE
                (liftBinaryNonExpanding f₂) (M.ι p))
              (CompletedBinary.NE₂[_,_,_].rightNE
                (liftBinaryNonExpanding g₂) (M.ι p))
              λ q →
                liftBinaryNonExpanding-ι f₂ p q
                ∙ cong T.ι (on-base p q)
                ∙ sym (liftBinaryNonExpanding-ι g₂ p q))
            y)
      x
