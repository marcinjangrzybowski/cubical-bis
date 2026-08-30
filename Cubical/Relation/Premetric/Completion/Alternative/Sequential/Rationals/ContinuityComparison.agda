module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.ContinuityComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous
  as RationalCauchyDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous
  as LocalDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.NaturalClosedBalls
  as NaturalDefinition

module Local = LocalDefinition
module Natural = NaturalDefinition
-- Reuse the instances exported by the rational local-continuity development.
-- Re-instantiating the same parameterized completion modules independently
-- makes conversion compare large HIT eliminators unnecessarily.
module S = Local.S
module SP = Local.SP
module U = Local.U
module CC = Local.CC
module G = Local.CC.C
module RC = RationalCauchyDefinition
module RationalTheory = PremetricTheory ℚPremetricSpace
module RealTheory = PremetricTheory SP.ℭ̂ₛPremetricSpace

open PositiveRationals


-- Standard metric notions.  `OrdinaryContinuous` is pointwise epsilon-delta
-- continuity, with the radius separately truncated at each epsilon.
-- `UniformlyContinuous` has one global modulus under truncation.

OrdinaryContinuous : (ℚ → ℚ) → Type₀
OrdinaryContinuous f =
  isContinuous (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd)


UniformlyContinuous : (ℚ → ℚ) → Type₀
UniformlyContinuous f =
  isUniformlyContinuous
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd)


-- The library name `IsLocallyUniformlyContinuous` means uniform continuity
-- on every bounded centered rational ball.  It is therefore the familiar
-- "uniformly continuous on bounded sets" condition, not merely pointwise
-- continuity at every rational.

BoundedlyUniformlyContinuous : (ℚ → ℚ) → Type₀
BoundedlyUniformlyContinuous = Local.IsLocallyUniformlyContinuous


UniformlyContinuousOnClosedBalls : (ℚ → ℚ) → Type₀
UniformlyContinuousOnClosedBalls =
  Local.IsUniformlyContinuousOnClosedBalls


UniformlyContinuousOnNaturalClosedBalls : (ℚ → ℚ) → Type₀
UniformlyContinuousOnNaturalClosedBalls =
  Natural.IsUniformlyContinuousOnNaturalClosedBalls


-- Completion-centered continuity is a density formulation: at every
-- completed point, sufficiently accurate rational approximants have
-- mutually close images.  Unlike ordinary continuity, its whole local
-- modulus is chosen under one truncation at each completed point.

CompletionCenteredContinuous : (ℚ → ℚ) → Type₀
CompletionCenteredContinuous f =
  CC.IsCompletionCenteredContinuous (S.ι ∘ f)


-- Graph-Cauchy continuity says that every Cauchy sequence in the completed
-- graph has a Cauchy image sequence.  `MapsRationalCauchySequences` is the
-- weaker, familiar statement only about rational-valued Cauchy sequences.

GraphCauchyContinuous : (ℚ → ℚ) → Type₀
GraphCauchyContinuous f = G.IsCauchyContinuous (S.ι ∘ f)


RationalGraphCauchyContinuous : (ℚ → ℚ) → Type₀
RationalGraphCauchyContinuous = RC.IsCauchyContinuousBase


MapsInjectedRationalCauchySequences : (ℚ → ℚ) → Type₀
MapsInjectedRationalCauchySequences f =
  G.MapsBaseCauchySequences (S.ι ∘ f)


MapsRationalCauchySequences : (ℚ → ℚ) → Type₀
MapsRationalCauchySequences = RC.MapsRationalCauchySequences


-- The implication chain between the available pre-lift hypotheses.

uniform→ordinary : ∀ {f} →
  UniformlyContinuous f → OrdinaryContinuous f
uniform→ordinary {f} =
  isUniformlyContinuous→isContinuous
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd)


uniform→boundedlyUniform : ∀ {f} →
  UniformlyContinuous f → BoundedlyUniformlyContinuous f
uniform→boundedlyUniform {f} =
  Local.uniformlyContinuous→locallyUniformlyContinuous f


boundedlyUniform→completionCentered : ∀ {f} →
  BoundedlyUniformlyContinuous f → CompletionCenteredContinuous f
boundedlyUniform→completionCentered {f} =
  Local.locallyUniformlyContinuous→completionCenteredContinuous f


completionCentered→graphCauchy : ∀ {f} →
  CompletionCenteredContinuous f → GraphCauchyContinuous f
completionCentered→graphCauchy =
  CC.completionCenteredContinuous→cauchyContinuous


graphCauchy→mapsInjectedRationalCauchy : ∀ {f} →
  GraphCauchyContinuous f → MapsInjectedRationalCauchySequences f
graphCauchy→mapsInjectedRationalCauchy =
  G.isCauchyContinuous→mapsBaseCauchySequences


-- `Rationals.CauchyContinuous` contains a specialized copy of the generic
-- graph record.  The fields have the same rational instance, but keeping this
-- conversion opaque avoids repeatedly comparing the two large module
-- instantiations.

opaque
  graphCauchy→rationalGraphCauchy : ∀ {f} →
    GraphCauchyContinuous f → RationalGraphCauchyContinuous f
  graphCauchy→rationalGraphCauchy graph = record
    { presCauchyGraph =
        graph .G.IsCauchyContinuous.presCauchyGraph }


rationalGraphCauchy→mapsRationalCauchy : ∀ {f} →
  RationalGraphCauchyContinuous f → MapsRationalCauchySequences f
rationalGraphCauchy→mapsRationalCauchy =
  RC.isCauchyContinuousBase→mapsRationalCauchySequences


graphCauchy→mapsRationalCauchy : ∀ {f} →
  GraphCauchyContinuous f → MapsRationalCauchySequences f
graphCauchy→mapsRationalCauchy =
  rationalGraphCauchy→mapsRationalCauchy ∘
  graphCauchy→rationalGraphCauchy


boundedlyUniform≃closedBalls : ∀ f →
  BoundedlyUniformlyContinuous f ≃
  UniformlyContinuousOnClosedBalls f
boundedlyUniform≃closedBalls =
  Local.locallyUniformlyContinuous≃onClosedBalls


closedBalls≃naturalClosedBalls : ∀ f →
  UniformlyContinuousOnClosedBalls f ≃
  UniformlyContinuousOnNaturalClosedBalls f
closedBalls≃naturalClosedBalls =
  Natural.onClosedBalls≃onNaturalClosedBalls


-- The first implication is genuinely strict: signed squaring is uniformly
-- continuous on every bounded ball but not uniformly continuous on all of
-- the unbounded rational line.

boundedlyUniformButNotUniform :
  Σ[ f ∈ (ℚ → ℚ) ]
    BoundedlyUniformlyContinuous f ×
    (UniformlyContinuous f → ⊥)
boundedlyUniformButNotUniform =
  signedSquareℚ ,
  Local.signedSquareℚ-locallyUniformlyContinuous ,
  Local.signedSquareℚ-notUniformlyContinuous


graphCauchyButNotUniform :
  Σ[ f ∈ (ℚ → ℚ) ]
    GraphCauchyContinuous f ×
    (UniformlyContinuous f → ⊥)
graphCauchyButNotUniform =
  signedSquareℚ ,
  completionCentered→graphCauchy
    (boundedlyUniform→completionCentered
      Local.signedSquareℚ-locallyUniformlyContinuous) ,
  Local.signedSquareℚ-notUniformlyContinuous


-- Output-side notions on the sequential rational completion.

RealOrdinaryContinuous : (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
RealOrdinaryContinuous F =
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (SP.ℭ̂ₛPremetricSpace .snd)


RealUniformlyContinuous : (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
RealUniformlyContinuous F =
  isUniformlyContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (SP.ℭ̂ₛPremetricSpace .snd)


PreservesCompletionCauchySequences : (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
PreservesCompletionCauchySequences = G.MapsCompletionCauchySequences


RationalSequentiallyContinuous : (ℚ → ℚ) → Type₀
RationalSequentiallyContinuous f = ∀ x l →
  RationalTheory.isLimitSeq x l →
  RationalTheory.isLimitSeq (f ∘ x) (f l)


RealSequentiallyContinuous : (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
RealSequentiallyContinuous F = ∀ x l →
  RealTheory.isLimitSeq x l →
  RealTheory.isLimitSeq (F ∘ x) (F l)


ordinary→sequential : ∀ {f} →
  OrdinaryContinuous f → RationalSequentiallyContinuous f
ordinary→sequential {f} f-cont =
  C→seqContinuous (f , f-cont)


realOrdinary→sequential : ∀ {F} →
  RealOrdinaryContinuous F → RealSequentiallyContinuous F
realOrdinary→sequential {F} F-cont =
  C→seqContinuous (F , F-cont)


realUniform→realOrdinary : ∀ {F} →
  RealUniformlyContinuous F → RealOrdinaryContinuous F
realUniform→realOrdinary {F} =
  isUniformlyContinuous→isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (SP.ℭ̂ₛPremetricSpace .snd)


-- Restriction along the rational injection relates the completion-side
-- guarantees back to the standard rational epsilon-delta notions.

opaque
  continuousExtension→ordinary : ∀ f F →
    (∀ q → F (S.ι q) ≡ S.ι (f q)) →
    RealOrdinaryContinuous F →
    OrdinaryContinuous f
  continuousExtension→ordinary f F extends F-cont q
    .IsContinuousAt.pres≈ ε =
    PT.map restrict
      (F-cont (S.ι q) .IsContinuousAt.pres≈ ε)
    where
    restrict :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ y → S.ι q S.∼̂ₛ[ δ ] y →
          F (S.ι q) S.∼̂ₛ[ ε ] F y)) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ r →
          PremetricStr._≈[_]_ (ℚPremetricSpace .snd) q δ r →
          PremetricStr._≈[_]_ (ℚPremetricSpace .snd)
            (f q) ε (f r))
    restrict (δ , preserve) = δ , λ r q≈r →
      U.ι-ι-reflects∼ (f q) (f r) ε
        (subst2 (S._∼̂ₛ[ ε ]_)
          (extends q) (extends r)
          (preserve (S.ι r) (S.ι-ι q r δ q≈r)))


opaque
  uniformExtension→uniform : ∀ f F →
    (∀ q → F (S.ι q) ≡ S.ι (f q)) →
    RealUniformlyContinuous F →
    UniformlyContinuous f
  uniformExtension→uniform f F extends = PT.map λ where
    (μ , F-uc) → μ , isuniformlycontinuouswith λ q r ε q≈r →
      U.ι-ι-reflects∼ (f q) (f r) ε
        (subst2 (S._∼̂ₛ[ ε ]_)
          (extends q) (extends r)
          (F-uc .IsUniformlyContinuousWith.pres≈
            (S.ι q) (S.ι r) ε (S.ι-ι q r (μ ε) q≈r)))


-- All constructions below are the same canonical graph-Cauchy extension;
-- stronger input hypotheses only prove stronger properties of that map.

uniformLift : ∀ f → UniformlyContinuous f → S.ℭ̂ₛ → S.ℭ̂ₛ
uniformLift = U.liftUniformlyContinuous


boundedlyUniformLift : ∀ f →
  BoundedlyUniformlyContinuous f → S.ℭ̂ₛ → S.ℭ̂ₛ
boundedlyUniformLift = Local.liftLocallyUniformlyContinuous


closedBallLift : ∀ f →
  UniformlyContinuousOnClosedBalls f → S.ℭ̂ₛ → S.ℭ̂ₛ
closedBallLift = Local.liftUniformlyContinuousOnClosedBalls


naturalClosedBallLift : ∀ f →
  UniformlyContinuousOnNaturalClosedBalls f → S.ℭ̂ₛ → S.ℭ̂ₛ
naturalClosedBallLift = Natural.liftUniformlyContinuousOnNaturalClosedBalls


completionCenteredLift : ∀ f →
  CompletionCenteredContinuous f → S.ℭ̂ₛ → S.ℭ̂ₛ
completionCenteredLift f =
  CC.liftCompletionCenteredContinuous (S.ι ∘ f)


graphCauchyLift : ∀ f →
  GraphCauchyContinuous f → S.ℭ̂ₛ → S.ℭ̂ₛ
graphCauchyLift = G.liftCauchyContinuousBase


opaque
  uniformLift-isUniform : ∀ f f-uc →
    RealUniformlyContinuous (uniformLift f f-uc)
  uniformLift-isUniform =
    U.liftUniformlyContinuous-isUniformlyContinuous


opaque
  boundedlyUniformLift-isOrdinary : ∀ f f-local →
    RealOrdinaryContinuous (boundedlyUniformLift f f-local)
  boundedlyUniformLift-isOrdinary =
    Local.liftLocallyUniformlyContinuous-isContinuous


opaque
  closedBallLift-isOrdinary : ∀ f f-closed →
    RealOrdinaryContinuous (closedBallLift f f-closed)
  closedBallLift-isOrdinary =
    Local.liftUniformlyContinuousOnClosedBalls-isContinuous


opaque
  naturalClosedBallLift-isOrdinary : ∀ f f-natural →
    RealOrdinaryContinuous (naturalClosedBallLift f f-natural)
  naturalClosedBallLift-isOrdinary =
    Natural.liftUniformlyContinuousOnNaturalClosedBalls-isContinuous


opaque
  completionCenteredLift-isOrdinary : ∀ f f-centered →
    RealOrdinaryContinuous (completionCenteredLift f f-centered)
  completionCenteredLift-isOrdinary f =
    CC.liftCompletionCenteredContinuous-isContinuous (S.ι ∘ f)

opaque
  graphCauchyLift-preservesCauchy : ∀ f f-graph →
    PreservesCompletionCauchySequences (graphCauchyLift f f-graph)
  graphCauchyLift-preservesCauchy =
    G.liftCauchyContinuousBase-presCauchy


opaque
  boundedlyUniform→ordinary : ∀ {f} →
    BoundedlyUniformlyContinuous f → OrdinaryContinuous f
  boundedlyUniform→ordinary {f} f-local =
    continuousExtension→ordinary f
      (boundedlyUniformLift f f-local)
      (Local.liftLocallyUniformlyContinuous-ι f f-local)
      (boundedlyUniformLift-isOrdinary f f-local)


-- Thus the ordinary-continuity guarantee for the bounded-ball lift cannot
-- in general be upgraded to global uniform continuity.

opaque
  signedSquareLift-notUniform :
    RealUniformlyContinuous Local.liftSignedSquare → ⊥
  signedSquareLift-notUniform F-uc =
    Local.signedSquareℚ-notUniformlyContinuous
      (uniformExtension→uniform signedSquareℚ Local.liftSignedSquare
        Local.liftSignedSquare-ι F-uc)


-- Agreement is not an additional construction: all four definitions reduce
-- to `G.liftCauchyContinuous (S.ι ∘ f)` with different proofs of the same
-- graph-Cauchy proposition.  Hence `G.liftCauchyContinuous-hypothesis-independent`
-- compares any two of them.  The explicit uniform-versus-bounded theorem is
-- `Local.liftLocallyUniformlyContinuous-agreesWithUniformlyContinuousWith`.


-- The weaker presentation-based route in
-- `Rationals.Lift.MapsRationalCauchySequencesPresented` starts only from
-- `MapsRationalCauchySequences`.  Its `liftAllSequentialReals` additionally
-- requires `AllSequentialRealsMerelyPresented`; the proved guarantee is
-- `liftAllSequentialReals-rational`, not ordinary or uniform continuity.
-- We deliberately do not import that very large experimental module here:
-- merely re-exporting the theorem makes this comparison exceed one minute.


-- Summary of the proved constructive comparison:
--
--   global uniform
--     ⇒ uniform on every bounded ball
--     ≃ uniform on every rational closed ball
--     ≃ uniform on the cofinal natural closed balls
--     ⇒ completion-centered
--     ⇒ graph-Cauchy
--     ⇒ maps rational Cauchy sequences.
--
-- The corresponding canonical lifts respectively carry global uniform
-- continuity, ordinary epsilon-delta continuity, and bare preservation of
-- Cauchy sequences.  Ordinary continuity also implies sequential limit
-- continuity via `ordinary→sequential` and `realOrdinary→sequential`.
--
-- Classically, for maps on the incomplete metric space ℚ, Cauchy continuity
-- lies strictly between uniform and ordinary continuity: squaring separates
-- it from global uniform continuity, while q ↦ 1 / (q² - 2) is the standard
-- ordinary-continuous map which fails on a Cauchy sequence approaching √2.
-- The latter separation and the classical implication from Cauchy continuity
-- to pointwise continuity require principles not developed here.  Therefore
-- no constructive `graphCauchy → ordinary` arrow is claimed in this module.
