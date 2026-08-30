open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Comparison
  {ℓ ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.PropositionalTruncation.Properties as PTProps

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

import Cubical.Axiom.Choice as AC

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures

import Cubical.Relation.Premetric.Completion.Base
  as RegularBase
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as RegularPremetric
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as RegularExtension

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialBase
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPremetric
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as RegularSequentialComparison

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchySequenceBase
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CauchySequencePremetric
import Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  as CauchySequenceLimits
import Cubical.Relation.Premetric.Completion.CauchySequence.Comparison.Regular
  as RegularCauchySequenceComparison
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.UniversalProperty
  as CauchySequenceExtension

module Regular = RegularBase M'
module RegularMetric = RegularPremetric M'
module Sequential = SequentialBase M'
module SequentialMetric = SequentialPremetric M'
module RegularSequential = RegularSequentialComparison M'
module CauchySequence = CauchySequenceBase M'
module CauchySequenceMetric = CauchySequencePremetric M'
module RegularCauchySequence = RegularCauchySequenceComparison M'

open PositiveRationals


-- The three relevant placements of propositional truncation.  The first
-- form chooses a tail index at every radius.  The second remembers only the
-- mere existence of that entire choice function.  The third, used by
-- CauchySequence, merely chooses a tail separately at each radius.

module Witnesses {ℓP ℓP'} (P' : PremetricSpace ℓP ℓP') where
  private
    module P = PremetricStr (P' .snd)

  CauchyTail : (ℕ → P' .fst) → ℚ₊ → Type ℓP'
  CauchyTail x ε =
    Σ[ N ∈ ℕ ]
      (∀ m n → N ℕ.≤ m → N ℕ.≤ n → x m P.≈[ ε ] x n)

  ChosenCauchySequence : (ℕ → P' .fst) → Type ℓP'
  ChosenCauchySequence x = ∀ ε → CauchyTail x ε

  BundledCauchySequence : (ℕ → P' .fst) → Type ℓP'
  BundledCauchySequence x = ∥ ChosenCauchySequence x ∥₁

  RadiuswiseCauchySequence : (ℕ → P' .fst) → Type ℓP'
  RadiuswiseCauchySequence x = ∀ ε → ∥ CauchyTail x ε ∥₁

  chosen→bundled : ∀ {x} →
    ChosenCauchySequence x → BundledCauchySequence x
  chosen→bundled = ∣_∣₁

  bundled→radiuswise : ∀ {x} →
    BundledCauchySequence x → RadiuswiseCauchySequence x
  bundled→radiuswise =
    PT.rec (isPropΠ λ _ → squash₁)
      (λ chosen ε → ∣ chosen ε ∣₁)

  RadiuswiseTailChoice : Type (ℓ-max ℓP ℓP')
  RadiuswiseTailChoice =
    ∀ x → RadiuswiseCauchySequence x → BundledCauchySequence x

  isPropRadiuswiseTailChoice : isProp RadiuswiseTailChoice
  isPropRadiuswiseTailChoice =
    isPropΠ2 λ _ _ → squash₁


-- This axiom schema is the missing reverse direction of the canonical map
-- ∥ Π ε , A ε ∥ → Π ε , ∥ A ε ∥.  It is not assumed by this module.  Since
-- positive rationals form a countable index type, this is a countable-choice
-- principle rather than a consequence of propositional truncation.

PositiveRationalChoice : (ℓA : Level) → Type (ℓ-suc ℓA)
PositiveRationalChoice ℓA =
  (A : ℚ₊ → Type ℓA) →
  ((ε : ℚ₊) → ∥ A ε ∥₁) →
  ∥ ((ε : ℚ₊) → A ε) ∥₁

-- The library's standard propositional axiom of choice on ℚ₊ supplies
-- this schema.  Keeping the implication explicit records that the reverse
-- comparison below is conditional, while the forward comparison is not.

propositionalChoice→positiveRationalChoice : ∀ {ℓA} →
  AC.satAC ℓA 1 ℚ₊ → PositiveRationalChoice ℓA
propositionalChoice→positiveRationalChoice choice A radiuswise =
  PT.map fst
    (invEq
      (AC.AC∃-map ,
        AC.satAC→satAC∃ choice A (λ _ _ → Unit))
      (λ ε → PT.map (λ a → a , tt) (radiuswise ε)))

positiveRationalChoice→tailChoice :
  ∀ {ℓP ℓP'} {P' : PremetricSpace ℓP ℓP'} →
  PositiveRationalChoice ℓP' →
  Witnesses.RadiuswiseTailChoice P'
positiveRationalChoice→tailChoice {P' = P'} choice x radiuswise =
  choice (Witnesses.CauchyTail P' x) radiuswise


-- On the middle completion, the untruncated family of tail indices is
-- exactly Sequential.CauchySeq.  This is ordinary Π/Σ distributivity; the
-- only non-constructive-looking step occurs after propositional truncation.

module MiddleWitnesses where
  CauchyTail : (ℕ → Sequential.ℭ̂ₛ) → ℚ₊ → Type (ℓ-max ℓ ℓ')
  CauchyTail x ε =
    Σ[ N ∈ ℕ ]
      (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        x m Sequential.∼̂ₛ[ ε ] x n)

  ChosenCauchySequence : (ℕ → Sequential.ℭ̂ₛ) → Type (ℓ-max ℓ ℓ')
  ChosenCauchySequence x = ∀ ε → CauchyTail x ε

  BundledCauchySequence : (ℕ → Sequential.ℭ̂ₛ) → Type (ℓ-max ℓ ℓ')
  BundledCauchySequence x = ∥ ChosenCauchySequence x ∥₁

  RadiuswiseCauchySequence : (ℕ → Sequential.ℭ̂ₛ) → Type (ℓ-max ℓ ℓ')
  RadiuswiseCauchySequence x = ∀ ε → ∥ CauchyTail x ε ∥₁

  bundled→radiuswise : ∀ {x} →
    BundledCauchySequence x → RadiuswiseCauchySequence x
  bundled→radiuswise =
    PT.rec (isPropΠ λ _ → squash₁)
      (λ chosen ε → ∣ chosen ε ∣₁)

  RadiuswiseTailChoice : Type (ℓ-max ℓ ℓ')
  RadiuswiseTailChoice =
    ∀ x → RadiuswiseCauchySequence x → BundledCauchySequence x

chosenCauchySequence≃sequentialCauchyData : ∀ {x} →
  MiddleWitnesses.ChosenCauchySequence x ≃ Sequential.CauchySeq x
chosenCauchySequence≃sequentialCauchyData =
  isoToEquiv Σ-Π-Iso

bundledCauchySequence≃sequentialWitness : ∀ {x} →
  MiddleWitnesses.BundledCauchySequence x ≃ Sequential.SeqWitness x
bundledCauchySequence≃sequentialWitness =
  PTProps.propTrunc≃ chosenCauchySequence≃sequentialCauchyData

sequentialWitness→radiuswise : ∀ {x} →
  Sequential.SeqWitness x →
  MiddleWitnesses.RadiuswiseCauchySequence x
sequentialWitness→radiuswise {x} witness =
  MiddleWitnesses.bundled→radiuswise
    (invEq bundledCauchySequence≃sequentialWitness witness)

SequentialTailChoice : Type (ℓ-max ℓ ℓ')
SequentialTailChoice =
  ∀ x → MiddleWitnesses.RadiuswiseCauchySequence x →
    Sequential.SeqWitness x

isPropSequentialTailChoice : isProp SequentialTailChoice
isPropSequentialTailChoice =
  isPropΠ2 λ _ _ → squash₁

tailChoice→sequentialTailChoice :
  MiddleWitnesses.RadiuswiseTailChoice → SequentialTailChoice
tailChoice→sequentialTailChoice choice x radiuswise =
  equivFun bundledCauchySequence≃sequentialWitness
    (choice x radiuswise)

positiveRationalChoice→sequentialTailChoice :
  PositiveRationalChoice (ℓ-max ℓ ℓ') → SequentialTailChoice
positiveRationalChoice→sequentialTailChoice choice =
  tailChoice→sequentialTailChoice
    (λ x radiuswise →
      choice (MiddleWitnesses.CauchyTail x) radiuswise)

sequentialWitness≃radiuswiseWithChoice :
  SequentialTailChoice → ∀ x →
  Sequential.SeqWitness x ≃
    MiddleWitnesses.RadiuswiseCauchySequence x
sequentialWitness≃radiuswiseWithChoice choice x =
  propBiimpl→Equiv
    squash₁
    (isPropΠ λ _ → squash₁)
    sequentialWitness→radiuswise
    (choice x)


-- The middle completion is already known, constructively, to be isometric
-- to Completion.Base.  These maps merely expose that result in the same
-- nonexpanding-map vocabulary used below.

sequentialToRegularⁿ :
  NE[ SequentialMetric.ℭ̂ₛPremetricSpace ,
      RegularMetric.ℭPremetricSpace ]
sequentialToRegularⁿ .fst = RegularSequential.toRegular
sequentialToRegularⁿ .snd =
  isIsometry→IsNonExpanding
    (SequentialMetric.ℭ̂ₛPremetricSpace .snd)
    RegularSequential.sequentialRegularEquiv
    (RegularMetric.ℭPremetricSpace .snd)
    RegularSequential.sequentialRegularIsometry

regularToSequentialⁿ :
  NE[ RegularMetric.ℭPremetricSpace ,
      SequentialMetric.ℭ̂ₛPremetricSpace ]
regularToSequentialⁿ .fst = RegularSequential.fromRegular
regularToSequentialⁿ .snd =
  isIsometry→IsNonExpanding
    (RegularMetric.ℭPremetricSpace .snd)
    RegularSequential.regularSequentialEquiv
    (SequentialMetric.ℭ̂ₛPremetricSpace .snd)
    RegularSequential.regularSequentialIsometry


-- Forgetting coherent tail choices is unconditional.  Completion.Base can
-- therefore map canonically into CauchySequence, and the same holds for the
-- chosen-modulus sequential presentation.

regularToCauchySequenceⁿ :
  NE[ RegularMetric.ℭPremetricSpace ,
      CauchySequenceMetric.CompletionPremetricSpace ]
regularToCauchySequenceⁿ = RegularCauchySequence.fromRegularⁿ

sequentialToCauchySequenceⁿ :
  NE[ SequentialMetric.ℭ̂ₛPremetricSpace ,
      CauchySequenceMetric.CompletionPremetricSpace ]
sequentialToCauchySequenceⁿ =
  regularToCauchySequenceⁿ ∘NE sequentialToRegularⁿ

sequentialToCauchySequence-ι : ∀ q →
  fst sequentialToCauchySequenceⁿ (Sequential.ι q) ≡
    CauchySequence.ι q
sequentialToCauchySequence-ι q =
  cong (fst regularToCauchySequenceⁿ)
    (RegularSequential.toRegular-ι q)
  ∙ funExt⁻ RegularCauchySequence.fromRegular-ι q


-- A reverse map first needs the middle completion to accept radiuswise
-- Cauchy sequences.  SequentialTailChoice supplies exactly that missing
-- constructor argument and nothing else.

module SequentialLimits =
  CauchySequenceLimits SequentialMetric.ℭ̂ₛPremetricSpace

sequentialHasCauchySequenceLimits :
  SequentialTailChoice → SequentialLimits.HasCauchySequenceLimits
sequentialHasCauchySequenceLimits choice x radiuswise =
  Sequential.lim x witness ,
  SequentialMetric.lim-isLimitSeq x witness
  where
  witness : Sequential.SeqWitness x
  witness = choice x radiuswise

sequentialInjectionⁿ :
  NE[ M' , SequentialMetric.ℭ̂ₛPremetricSpace ]
sequentialInjectionⁿ .fst = Sequential.ι
sequentialInjectionⁿ .snd .IsNonExpanding.pres≈ = Sequential.ι-ι

module ExtendCauchySequenceToSequential =
  CauchySequenceExtension M' SequentialMetric.ℭ̂ₛPremetricSpace

cauchySequenceToSequentialWithChoiceⁿ :
  SequentialTailChoice →
  NE[ CauchySequenceMetric.CompletionPremetricSpace ,
      SequentialMetric.ℭ̂ₛPremetricSpace ]
cauchySequenceToSequentialWithChoiceⁿ choice =
  ExtendCauchySequenceToSequential.liftNonExpanding
    (sequentialHasCauchySequenceLimits choice)
    sequentialInjectionⁿ

cauchySequenceToSequentialWithChoice-ι :
  ∀ choice q →
  fst (cauchySequenceToSequentialWithChoiceⁿ choice)
    (CauchySequence.ι q) ≡ Sequential.ι q
cauchySequenceToSequentialWithChoice-ι choice q =
  ExtendCauchySequenceToSequential.liftNonExpanding-ι
    (sequentialHasCauchySequenceLimits choice)
    sequentialInjectionⁿ q

cauchySequenceToRegularWithChoiceⁿ :
  SequentialTailChoice →
  NE[ CauchySequenceMetric.CompletionPremetricSpace ,
      RegularMetric.ℭPremetricSpace ]
cauchySequenceToRegularWithChoiceⁿ choice =
  sequentialToRegularⁿ ∘NE
    cauchySequenceToSequentialWithChoiceⁿ choice

cauchySequenceToRegularWithChoice-ι :
  ∀ choice q →
  fst (cauchySequenceToRegularWithChoiceⁿ choice)
    (CauchySequence.ι q) ≡ Regular.ι q
cauchySequenceToRegularWithChoice-ι choice q =
  cong (fst sequentialToRegularⁿ)
    (cauchySequenceToSequentialWithChoice-ι choice q)
  ∙ RegularSequential.toRegular-ι q


-- Density makes the two conditional maps inverse.  Thus the comparison is
-- an actual isometric equivalence under the precise tail-choice principle,
-- not merely a pair of unrelated maps.

module CauchySequenceUniqueness =
  CauchySequenceExtension
    M' CauchySequenceMetric.CompletionPremetricSpace

regularAfterCauchySequenceWithChoiceⁿ :
  ∀ choice →
  regularToCauchySequenceⁿ ∘NE
      cauchySequenceToRegularWithChoiceⁿ choice
    ≡ idⁿ
regularAfterCauchySequenceWithChoiceⁿ choice =
  CauchySequenceUniqueness.nonExpandingExtensionality
    (regularToCauchySequenceⁿ ∘NE
      cauchySequenceToRegularWithChoiceⁿ choice)
    idⁿ
    (funExt agree)
  where
  agree : ∀ q →
    fst (regularToCauchySequenceⁿ ∘NE
      cauchySequenceToRegularWithChoiceⁿ choice)
      (CauchySequence.ι q) ≡ CauchySequence.ι q
  agree q =
    cong (fst regularToCauchySequenceⁿ)
      (cauchySequenceToRegularWithChoice-ι choice q)
    ∙ funExt⁻ RegularCauchySequence.fromRegular-ι q

cauchySequenceAfterRegularWithChoiceⁿ :
  ∀ choice →
  cauchySequenceToRegularWithChoiceⁿ choice ∘NE
      regularToCauchySequenceⁿ
    ≡ idⁿ
cauchySequenceAfterRegularWithChoiceⁿ choice =
  RegularExtension.nonExpanding≡
    M' RegularMetric.ℭPremetricSpace
    (cauchySequenceToRegularWithChoiceⁿ choice ∘NE
      regularToCauchySequenceⁿ)
    idⁿ
    (funExt agree)
  where
  agree : ∀ q →
    fst (cauchySequenceToRegularWithChoiceⁿ choice ∘NE
      regularToCauchySequenceⁿ) (Regular.ι q) ≡ Regular.ι q
  agree q =
    cong (fst (cauchySequenceToRegularWithChoiceⁿ choice))
      (funExt⁻ RegularCauchySequence.fromRegular-ι q)
    ∙ cauchySequenceToRegularWithChoice-ι choice q


regularCauchySequenceIsoWithChoice :
  SequentialTailChoice → Iso Regular.ℭ CauchySequence.Completion
regularCauchySequenceIsoWithChoice choice .Iso.fun =
  fst regularToCauchySequenceⁿ
regularCauchySequenceIsoWithChoice choice .Iso.inv =
  fst (cauchySequenceToRegularWithChoiceⁿ choice)
regularCauchySequenceIsoWithChoice choice .Iso.sec x =
  funExt⁻
    (cong fst (regularAfterCauchySequenceWithChoiceⁿ choice)) x
regularCauchySequenceIsoWithChoice choice .Iso.ret x =
  funExt⁻
    (cong fst (cauchySequenceAfterRegularWithChoiceⁿ choice)) x

regularCauchySequenceEquivWithChoice :
  SequentialTailChoice → Regular.ℭ ≃ CauchySequence.Completion
regularCauchySequenceEquivWithChoice choice =
  isoToEquiv (regularCauchySequenceIsoWithChoice choice)

regularCauchySequenceIsometryWithChoice :
  ∀ choice →
  IsIsometry
    (RegularMetric.ℭPremetricSpace .snd)
    (regularCauchySequenceEquivWithChoice choice)
    (CauchySequenceMetric.CompletionPremetricSpace .snd)
regularCauchySequenceIsometryWithChoice choice
  .IsIsometry.pres≈ x ε y =
  propBiimpl→Equiv
    (Regular.isProp∼ x ε y)
    (CauchySequence.isProp≈ᶜ
      (fst regularToCauchySequenceⁿ x) ε
      (fst regularToCauchySequenceⁿ y))
    (regularToCauchySequenceⁿ .snd .IsNonExpanding.pres≈ x y ε)
    reflect
  where
  reflect :
    fst regularToCauchySequenceⁿ x
      CauchySequence.≈ᶜ[ ε ]
    fst regularToCauchySequenceⁿ y →
    x Regular.∼[ ε ] y
  reflect close =
    subst2 (Regular._∼[ ε ]_)
      (regularCauchySequenceIsoWithChoice choice .Iso.ret x)
      (regularCauchySequenceIsoWithChoice choice .Iso.ret y)
      (cauchySequenceToRegularWithChoiceⁿ choice
        .snd .IsNonExpanding.pres≈
          (fst regularToCauchySequenceⁿ x)
          (fst regularToCauchySequenceⁿ y) ε close)

regularCauchySequencePremetricEquivWithChoice :
  ∀ choice →
  PremetricSpaceEquiv
    RegularMetric.ℭPremetricSpace
    CauchySequenceMetric.CompletionPremetricSpace
regularCauchySequencePremetricEquivWithChoice choice =
  regularCauchySequenceEquivWithChoice choice ,
  regularCauchySequenceIsometryWithChoice choice

regularCauchySequencePremetricEquivWithPositiveRationalChoice :
  PositiveRationalChoice (ℓ-max ℓ ℓ') →
  PremetricSpaceEquiv
    RegularMetric.ℭPremetricSpace
    CauchySequenceMetric.CompletionPremetricSpace
regularCauchySequencePremetricEquivWithPositiveRationalChoice choice =
  regularCauchySequencePremetricEquivWithChoice
    (positiveRationalChoice→sequentialTailChoice choice)

regularCauchySequencePremetricEquivWithPropositionalChoice :
  AC.satAC (ℓ-max ℓ ℓ') 1 ℚ₊ →
  PremetricSpaceEquiv
    RegularMetric.ℭPremetricSpace
    CauchySequenceMetric.CompletionPremetricSpace
regularCauchySequencePremetricEquivWithPropositionalChoice choice =
  regularCauchySequencePremetricEquivWithPositiveRationalChoice
    (propositionalChoice→positiveRationalChoice choice)
