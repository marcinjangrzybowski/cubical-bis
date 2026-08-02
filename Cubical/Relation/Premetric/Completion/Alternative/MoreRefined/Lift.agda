open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Lift
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Properties as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  as MoreRefinedDefinition

module Source = PremetricTheory M'
module Target = MoreRefinedDefinition N'

open PositiveRationals


-- Uniform continuity acts on the data used by the new limit constructor
-- without any rescaling law: the input Cauchy modulus is simply
-- precomposed with the uniform-continuity modulus.

mapBaseCauchySeqWith : ∀ {μ} (f : M' .fst → N' .fst) →
  IsUniformlyContinuousWith (M' .snd) f (N' .snd) μ →
  ∀ x → Source.isCauchySeq x →
  Target.CauchySeq (λ n → Target.ι (f (x n)))
mapBaseCauchySeqWith {μ} f f-uc x xc = image .fst , image-close
  where
  image : PremetricTheory.isCauchySeq N' (f ∘ x)
  image = UCWith→presIsCauchySeq f f-uc x xc

  image-close : ∀ ε m n → image .fst ε ℕ.≤ m →
    image .fst ε ℕ.≤ n →
    Target.ι (f (x m)) Target.∼̂ₛ[ ε ] Target.ι (f (x n))
  image-close ε m n με≤m με≤n =
    Target.ι-ι (f (x m)) (f (x n)) ε
      (image .snd ε m n με≤m με≤n)


BaseSeqWitness : (ℕ → M' .fst) → Type _
BaseSeqWitness x = ∥ Source.isCauchySeq x ∥₁

mapBaseSeqWitness : (f : M' .fst → N' .fst) →
  isUniformlyContinuous (M' .snd) f (N' .snd) →
  ∀ x → BaseSeqWitness x →
  Target.SeqWitness (λ n → Target.ι (f (x n)))
mapBaseSeqWitness f f-uc x =
  PT.map2
    (λ { (μ , f-uc) xc → mapBaseCauchySeqWith f f-uc x xc })
    f-uc


-- Thus every merely Cauchy base sequence has a directly constructed image
-- limit.  Neither the uniform-continuity modulus nor the Cauchy modulus has
-- to be selected outside propositional truncation.

imageSequenceLimit : (f : M' .fst → N' .fst) →
  isUniformlyContinuous (M' .snd) f (N' .snd) →
  ∀ x → BaseSeqWitness x → Target.ℭ̂ₛ
imageSequenceLimit f f-uc x xc =
  Target.lim (λ n → Target.ι (f (x n)))
    (mapBaseSeqWitness f f-uc x xc)

imageSequenceLimit-witness-independent :
  ∀ f f-uc g-uc x xc yc →
  imageSequenceLimit f f-uc x xc ≡
    imageSequenceLimit f g-uc x yc
imageSequenceLimit-witness-independent f f-uc g-uc x xc yc =
  cong (Target.lim (λ n → Target.ι (f (x n))))
    (squash₁ (mapBaseSeqWitness f f-uc x xc)
      (mapBaseSeqWitness f g-uc x yc))


-- This does not yet define a function from the whole source completion.
-- Recℭ̂ₛ maps each individual source relation at its displayed radius and,
-- in particular, asks for mono-B and tri-B.  Uniform continuity instead
-- chooses an input radius μ ε after an output radius ε is requested.  An
-- arbitrary μ has no additivity or inverse law that would make those fields
-- typecheck.  A full direct lift therefore needs a new all-radii/sequential
-- coherence eliminator (or an equality characterization of represented
-- Cauchy sequences), rather than another instantiation of the current
-- exact-radius recursor.
