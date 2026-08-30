open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as RegularComparisonDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous.Technical
  as TechnicalDefinition

module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module T = SequentialDefinition N'
module TP = SequentialPropertiesDefinition N'
module Comparison = RegularComparisonDefinition M'
module C = CauchyContinuousDefinition M' N'
module Tech = TechnicalDefinition M' N'

private
  M = M' .fst
  N = N' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')
  module PM = PremetricStr (M' .snd)

open PositiveRationals


-- These aliases keep the public graph language independent of the technical
-- modulus calculation below.

JointlyApproximableFor :
  (M → N) → S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
JointlyApproximableFor = Tech.JointlyApproximableFor

isPropJointlyApproximableFor : ∀ f x y →
  isProp (JointlyApproximableFor f x y)
isPropJointlyApproximableFor = Tech.isPropJointlyApproximableFor

ι-ι-reflects∼ : ∀ x y ε →
  S.ι x S.∼̂ₛ[ ε ] S.ι y →
  x PM.≈[ ε ] y
ι-ι-reflects∼ = Comparison.ι-reflects∼


-- An explicit modulus gives an explicit modulus on the completion.  The
-- proof that graph-Cauchy sequences are preserved is kept in Technical;
-- construction and uniqueness are inherited from the canonical Cauchy lift.

module WithModulus
  (f : M → N)
  (μ : ℚ₊ → ℚ₊)
  (f-uc : IsUniformlyContinuousWith (M' .snd) f (N' .snd) μ) where

  module Construction = Tech.WithModulus f μ f-uc

  inputBudget : ℚ₊ → ℚ₊
  inputBudget = Construction.inputBudget

  JointlyApproximable : S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
  JointlyApproximable = JointlyApproximableFor f

  jointlyApproximable-pres∼ : ∀ x x' y y' ε →
    JointlyApproximable x y →
    JointlyApproximable x' y' →
    x S.∼̂ₛ[ inputBudget ε ] x' →
    y T.∼̂ₛ[ ε ] y'
  jointlyApproximable-pres∼ = Construction.jointlyApproximable-pres∼

  jointlyApproximable-equal : ∀ x y y' →
    JointlyApproximable x y →
    JointlyApproximable x y' → y ≡ y'
  jointlyApproximable-equal = Construction.jointlyApproximable-equal

  imageCauchySeq : ∀ x y →
    (∀ n → JointlyApproximable (x n) (y n)) →
    S.CauchySeq x → T.CauchySeq y
  imageCauchySeq = Construction.imageCauchySeq

  isCauchyContinuousWith : C.IsCauchyContinuous (T.ι ∘ f)
  isCauchyContinuousWith = Construction.isCauchyContinuousWith

  liftUniformlyContinuousWith : S.ℭ̂ₛ → T.ℭ̂ₛ
  liftUniformlyContinuousWith =
    C.liftCauchyContinuous (T.ι ∘ f) isCauchyContinuousWith

  liftUniformlyContinuousWith-joint : ∀ x →
    JointlyApproximable x (liftUniformlyContinuousWith x)
  liftUniformlyContinuousWith-joint =
    C.liftCauchyContinuous-joint (T.ι ∘ f) isCauchyContinuousWith

  liftUniformlyContinuousWith-pres∼ : ∀ x y ε →
    x S.∼̂ₛ[ inputBudget ε ] y →
    liftUniformlyContinuousWith x T.∼̂ₛ[ ε ]
      liftUniformlyContinuousWith y
  liftUniformlyContinuousWith-pres∼ x y ε =
    jointlyApproximable-pres∼ x y
      (liftUniformlyContinuousWith x)
      (liftUniformlyContinuousWith y) ε
      (liftUniformlyContinuousWith-joint x)
      (liftUniformlyContinuousWith-joint y)

  liftUniformlyContinuousWith-isUniformlyContinuousWith :
    IsUniformlyContinuousWith
      (SP.ℭ̂ₛPremetricSpace .snd) liftUniformlyContinuousWith
      (TP.ℭ̂ₛPremetricSpace .snd) inputBudget
  liftUniformlyContinuousWith-isUniformlyContinuousWith =
    isuniformlycontinuouswith liftUniformlyContinuousWith-pres∼

  liftUniformlyContinuousWith-ι : ∀ q →
    liftUniformlyContinuousWith (S.ι q) ≡ T.ι (f q)
  liftUniformlyContinuousWith-ι =
    C.liftCauchyContinuous-ι (T.ι ∘ f) isCauchyContinuousWith


liftUniformlyContinuousWith-ext :
  ∀ (f g : M → N) μ ν
    (f-uc : IsUniformlyContinuousWith (M' .snd) f (N' .snd) μ)
    (g-uc : IsUniformlyContinuousWith (M' .snd) g (N' .snd) ν) →
  (∀ q → f q ≡ g q) →
  WithModulus.liftUniformlyContinuousWith f μ f-uc ≡
    WithModulus.liftUniformlyContinuousWith g ν g-uc
liftUniformlyContinuousWith-ext f g μ ν f-uc g-uc f∼g =
  C.liftCauchyContinuous-ext (T.ι ∘ f) (T.ι ∘ g)
    (WithModulus.isCauchyContinuousWith f μ f-uc)
    (WithModulus.isCauchyContinuousWith g ν g-uc)
    (λ q → cong T.ι (f∼g q))


UniformContinuityData : (M → N) → Type _
UniformContinuityData f =
  Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
    IsUniformlyContinuousWith (M' .snd) f (N' .snd) μ

uniformlyContinuous→cauchyContinuous : ∀ (f : M → N) →
  isUniformlyContinuous (M' .snd) f (N' .snd) →
  C.IsCauchyContinuous (T.ι ∘ f)
uniformlyContinuous→cauchyContinuous f =
  PT.rec (C.isPropIsCauchyContinuous (T.ι ∘ f)) λ where
    (μ , f-uc) → WithModulus.isCauchyContinuousWith f μ f-uc


liftUniformlyContinuous : (f : M → N) →
  isUniformlyContinuous (M' .snd) f (N' .snd) →
  S.ℭ̂ₛ → T.ℭ̂ₛ
liftUniformlyContinuous f f-uc =
  C.liftCauchyContinuous (T.ι ∘ f)
    (uniformlyContinuous→cauchyContinuous f f-uc)

liftUniformlyContinuous-joint : ∀ f f-uc x →
  JointlyApproximableFor f x (liftUniformlyContinuous f f-uc x)
liftUniformlyContinuous-joint f f-uc =
  C.liftCauchyContinuous-joint (T.ι ∘ f)
    (uniformlyContinuous→cauchyContinuous f f-uc)

liftUniformlyContinuous-ι : ∀ f f-uc q →
  liftUniformlyContinuous f f-uc (S.ι q) ≡ T.ι (f q)
liftUniformlyContinuous-ι f f-uc =
  C.liftCauchyContinuous-ι (T.ι ∘ f)
    (uniformlyContinuous→cauchyContinuous f f-uc)

liftUniformlyContinuous-ext :
  ∀ (f g : M → N)
    (f-uc : isUniformlyContinuous (M' .snd) f (N' .snd))
    (g-uc : isUniformlyContinuous (M' .snd) g (N' .snd)) →
  (∀ q → f q ≡ g q) →
  liftUniformlyContinuous f f-uc ≡
    liftUniformlyContinuous g g-uc
liftUniformlyContinuous-ext f g f-uc g-uc f∼g =
  C.liftCauchyContinuous-ext (T.ι ∘ f) (T.ι ∘ g)
    (uniformlyContinuous→cauchyContinuous f f-uc)
    (uniformlyContinuous→cauchyContinuous g g-uc)
    (λ q → cong T.ι (f∼g q))


liftUniformlyContinuous-isUniformlyContinuous : ∀ f
  (f-uc : isUniformlyContinuous (M' .snd) f (N' .snd)) →
  isUniformlyContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) (liftUniformlyContinuous f f-uc)
    (TP.ℭ̂ₛPremetricSpace .snd)
liftUniformlyContinuous-isUniformlyContinuous f f-uc =
  PT.rec
    (isPropIsUniformlyContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) (liftUniformlyContinuous f f-uc)
      (TP.ℭ̂ₛPremetricSpace .snd))
    withData f-uc
  where
  derived = uniformlyContinuous→cauchyContinuous f f-uc

  withData : UniformContinuityData f →
    isUniformlyContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) (liftUniformlyContinuous f f-uc)
      (TP.ℭ̂ₛPremetricSpace .snd)
  withData (μ , f-uc-with) =
    ∣ WithModulus.inputBudget f μ f-uc-with ,
      isuniformlycontinuouswith preserve ∣₁
    where
    explicit = WithModulus.liftUniformlyContinuousWith f μ f-uc-with

    packaged≡explicit : liftUniformlyContinuous f f-uc ≡ explicit
    packaged≡explicit =
      C.liftCauchyContinuous-hypothesis-independent (T.ι ∘ f)
        derived
        (WithModulus.isCauchyContinuousWith f μ f-uc-with)

    preserve : ∀ x y ε →
      x S.∼̂ₛ[ WithModulus.inputBudget f μ f-uc-with ε ] y →
      liftUniformlyContinuous f f-uc x T.∼̂ₛ[ ε ]
        liftUniformlyContinuous f f-uc y
    preserve x y ε x∼y = subst2 (T._∼̂ₛ[ ε ]_)
      (sym (funExt⁻ packaged≡explicit x))
      (sym (funExt⁻ packaged≡explicit y))
      (WithModulus.liftUniformlyContinuousWith-pres∼
        f μ f-uc-with x y ε x∼y)
