module Cubical.HITs.PropositionalTruncation.SequentialColimitChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (+-zero ; +-suc)
open import Cubical.Data.Sequence.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit.Base using (Unit* ; tt*)

open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT
open import Cubical.HITs.PropositionalTruncation.FiniteChoice
  using (CountableChoiceFor)
import Cubical.HITs.SequentialColimit.Base as SC
import Cubical.HITs.SequentialColimit.Properties as SCP

private
  variable
    ℓ : Level


-- A recursively presented prefix avoids committing to a particular finite
-- indexing type.  A prefix of length `suc k` consists of the first `k`
-- choices followed by the choice at `k`.

Prefix : (ℕ → Type ℓ) → ℕ → Type ℓ
Prefix P zero = Unit*
Prefix P (suc k) = Prefix P k × P k


-- At stage `k`, the proposed state contains an actual prefix and all remaining
-- values merely.  The tail is indexed as `k + n`, so its zero-th value is the
-- next value to append (up to `+-zero`).

Tail : (ℕ → Type ℓ) → ℕ → Type ℓ
Tail P k = (n : ℕ) → ∥ P (k + n) ∥₁


PrefixAndTail : (ℕ → Type ℓ) → ℕ → Type ℓ
PrefixAndTail P k = Prefix P k × Tail P k


tailHead : {P : ℕ → Type ℓ} {k : ℕ} → Tail P k → ∥ P k ∥₁
tailHead {P = P} {k = k} tail =
  subst (λ n → ∥ P n ∥₁) (+-zero k) (tail zero)


tailStep : {P : ℕ → Type ℓ} {k : ℕ} → Tail P k → Tail P (suc k)
tailStep {P = P} {k = k} tail n =
  subst (λ m → ∥ P m ∥₁) (+-suc k n) (tail (suc n))


-- Conversely, an actual next value can be put back in front of a tail.  This
-- is useful for observing that every complete stage still determines all the
-- original pointwise truncated values.

tailUnstep : {P : ℕ → Type ℓ} {k : ℕ} →
  P k → Tail P (suc k) → Tail P k
tailUnstep {P = P} {k = k} next tail zero =
  subst (λ m → ∥ P m ∥₁) (sym (+-zero k)) ∣ next ∣₁
tailUnstep {P = P} {k = k} next tail (suc n) =
  subst (λ m → ∥ P m ∥₁) (sym (+-suc k n)) (tail n)


-- This is the natural transition supplied by the data.  Its codomain is
-- truncated: the remaining tail supplies only `∥ P k ∥₁`, not `P k`.

merelyAdvance : {P : ℕ → Type ℓ} {k : ℕ} →
  PrefixAndTail P k → ∥ PrefixAndTail P (suc k) ∥₁
merelyAdvance {P = P} {k = k} (prefix , tail) =
  PT.map
    (λ next → (prefix , next) , tailStep {P = P} {k = k} tail)
    (tailHead {P = P} {k = k} tail)


-- Consequently the untruncated stages are not, from the given data, a
-- `Sequence`: its `map` field would have to return the untruncated codomain.
-- Truncating each complete stage repairs that typing problem.

TruncatedStage : (ℕ → Type ℓ) → ℕ → Type ℓ
TruncatedStage P k = ∥ PrefixAndTail P k ∥₁


advanceTruncatedStage : {P : ℕ → Type ℓ} {k : ℕ} →
  TruncatedStage P k → TruncatedStage P (suc k)
advanceTruncatedStage = PT.rec squash₁ merelyAdvance


truncatedStageSequence : (P : ℕ → Type ℓ) → Sequence ℓ
truncatedStageSequence P .Sequence.obj k = TruncatedStage P k
truncatedStageSequence P .Sequence.map = advanceTruncatedStage


PrefixTailColimit : (ℕ → Type ℓ) → Type ℓ
PrefixTailColimit P = SC.SeqColim (truncatedStageSequence P)


-- Any pointwise family of truncated choices already gives a point of the
-- colimit, via stage zero.  Moving farther into this direct colimit records
-- only that some finite prefix was chosen.

prefixTailColimitPoint : {P : ℕ → Type ℓ} →
  ((n : ℕ) → ∥ P n ∥₁) → PrefixTailColimit P
prefixTailColimitPoint choices = SC.incl ∣ tt* , choices ∣₁


-- A stage also recovers the entire original family of truncated values.  For
-- a successor stage, put its last actual prefix value back onto its tail and
-- recurse.  Since the result is a proposition, this descends through both the
-- stage truncation and the sequential colimit.

prefixAndTailChoices : {P : ℕ → Type ℓ} {k : ℕ} →
  PrefixAndTail P k → ((n : ℕ) → ∥ P n ∥₁)
prefixAndTailChoices {k = zero} (_ , tail) = tail
prefixAndTailChoices {P = P} {k = suc k} ((prefix , next) , tail) =
  prefixAndTailChoices {P = P} {k = k}
    (prefix , tailUnstep {P = P} {k = k} next tail)


truncatedStageChoices : {P : ℕ → Type ℓ} {k : ℕ} →
  TruncatedStage P k → ((n : ℕ) → ∥ P n ∥₁)
truncatedStageChoices =
  PT.rec (isPropΠ λ _ → squash₁) prefixAndTailChoices


colimitChoices : {P : ℕ → Type ℓ} →
  PrefixTailColimit P → ((n : ℕ) → ∥ P n ∥₁)
colimitChoices {P = P} =
  SCP.SeqColim→Prop
    (λ _ → isPropΠ λ _ → squash₁)
    (λ k → truncatedStageChoices {P = P} {k = k})


-- Thus an eliminator that extracted an infinite section from this colimit
-- would prove exactly the missing countable-choice instance.  Conversely,
-- countable choice first reads the pointwise truncated values from the
-- colimit and then chooses them.

ColimitExtractionFor : (P : ℕ → Type ℓ) → Type ℓ
ColimitExtractionFor P =
  PrefixTailColimit P →
  ∥ ((n : ℕ) → P n) ∥₁


colimitExtraction→countableChoice : {P : ℕ → Type ℓ} →
  ColimitExtractionFor P → CountableChoiceFor P
colimitExtraction→countableChoice extract choices =
  extract (prefixTailColimitPoint choices)


countableChoice→colimitExtraction : {P : ℕ → Type ℓ} →
  CountableChoiceFor P → ColimitExtractionFor P
countableChoice→colimitExtraction choice point =
  choice (colimitChoices point)


colimitExtraction≃CountableChoice : {P : ℕ → Type ℓ} →
  ColimitExtractionFor P ≃ CountableChoiceFor P
colimitExtraction≃CountableChoice =
  propBiimpl→Equiv
    (isPropΠ λ _ → squash₁)
    (isPropΠ λ _ → squash₁)
    colimitExtraction→countableChoice
    countableChoice→colimitExtraction


-- The obstruction occurs one step earlier for the untruncated stages.  If
-- genuine transition functions for them were available, iterating from the
-- stage-zero state would select an actual dependent function.

StageTransitions : (P : ℕ → Type ℓ) → Type ℓ
StageTransitions P =
  (k : ℕ) → PrefixAndTail P k → PrefixAndTail P (suc k)


iterateStages : {P : ℕ → Type ℓ} →
  StageTransitions P →
  (choices : (n : ℕ) → ∥ P n ∥₁) →
  (k : ℕ) → PrefixAndTail P k
iterateStages transition choices zero = tt* , choices
iterateStages transition choices (suc k) =
  transition k (iterateStages transition choices k)


stageTransitions→deterministicChoice : {P : ℕ → Type ℓ} →
  StageTransitions P →
  ((n : ℕ) → ∥ P n ∥₁) →
  ((n : ℕ) → P n)
stageTransitions→deterministicChoice transition choices n =
  snd (fst (iterateStages transition choices (suc n)))


stageTransitions→countableChoice : {P : ℕ → Type ℓ} →
  StageTransitions P → CountableChoiceFor P
stageTransitions→countableChoice transition choices =
  ∣ stageTransitions→deterministicChoice transition choices ∣₁


-- Infinite information is instead captured by the product of all prefixes.
-- Reading the last entry of prefix `suc n` recovers the section, while a
-- section constructs every prefix.  The coherent subtype below is the actual
-- inverse limit of the prefix restriction maps.

AllPrefixes : (ℕ → Type ℓ) → Type ℓ
AllPrefixes P = (k : ℕ) → Prefix P k


section→allPrefixes : {P : ℕ → Type ℓ} →
  ((n : ℕ) → P n) → AllPrefixes P
section→allPrefixes section zero = tt*
section→allPrefixes section (suc k) =
  section→allPrefixes section k , section k


allPrefixes→section : {P : ℕ → Type ℓ} →
  AllPrefixes P → ((n : ℕ) → P n)
allPrefixes→section prefixes n = snd (prefixes (suc n))


allPrefixes-section-retract : {P : ℕ → Type ℓ}
  (section : (n : ℕ) → P n) →
  allPrefixes→section (section→allPrefixes section) ≡ section
allPrefixes-section-retract section = refl


restrictPrefix : {P : ℕ → Type ℓ} {k : ℕ} →
  Prefix P (suc k) → Prefix P k
restrictPrefix = fst


CoherentPrefixes : (ℕ → Type ℓ) → Type ℓ
CoherentPrefixes P =
  Σ[ prefixes ∈ AllPrefixes P ]
    ((k : ℕ) → restrictPrefix (prefixes (suc k)) ≡ prefixes k)


section→coherentPrefixes : {P : ℕ → Type ℓ} →
  ((n : ℕ) → P n) → CoherentPrefixes P
section→coherentPrefixes section =
  section→allPrefixes section , λ _ → refl


coherentPrefixes→section : {P : ℕ → Type ℓ} →
  CoherentPrefixes P → ((n : ℕ) → P n)
coherentPrefixes→section (prefixes , _) = allPrefixes→section prefixes


coherentPrefixes-section-retract : {P : ℕ → Type ℓ}
  (section : (n : ℕ) → P n) →
  coherentPrefixes→section (section→coherentPrefixes section) ≡ section
coherentPrefixes-section-retract section = refl
