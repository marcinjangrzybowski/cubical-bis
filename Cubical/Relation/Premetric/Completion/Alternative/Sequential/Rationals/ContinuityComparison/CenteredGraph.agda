module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.ContinuityComparison.CenteredGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.ContinuityComparison

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


-- A real function extends a completion-valued rational restriction when it
-- agrees with it on the dense injection.  Ordinary continuity supplies the
-- graph compatibility required by the Cauchy lifting universal property.
-- The radius `min₊ α δ /2₊` lets one rational approximation meet both the
-- requested density radius and the radius supplied by continuity.

ExtendsDenseRestriction :
  (ℚ → S.ℭ̂ₛ) → (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
ExtendsDenseRestriction f F = ∀ q → F (S.ι q) ≡ f q


isPropExtendsDenseRestriction : ∀ f F →
  isProp (ExtendsDenseRestriction f F)
isPropExtendsDenseRestriction f F =
  isPropΠ λ q → S.isSetℭ̂ₛ (F (S.ι q)) (f q)


opaque
  ordinaryExtension→jointlyApproximable : ∀ f F →
    ExtendsDenseRestriction f F →
    RealOrdinaryContinuous F →
    ∀ x → G.JointlyApproximableFor f x (F x)
  ordinaryExtension→jointlyApproximable f F extends F-cont x α β =
    PT.rec squash₁
      withRadius
      (F-cont x .IsContinuousAt.pres≈ β)
    where
    withRadius :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ y → x S.∼̂ₛ[ δ ] y → F x S.∼̂ₛ[ β ] F y)) →
      ∃[ q ∈ ℚ ]
        (S.ι q S.∼̂ₛ[ α ] x) ×
        (f q S.∼̂ₛ[ β ] F x)
    withRadius (δ , preserve) =
      PT.map withApproximation
        (SP.∃approx x (min₊ α δ /2₊))
      where
      sourceRadius : ℚ₊
      sourceRadius = min₊ α δ /2₊

      withApproximation :
        (Σ[ q ∈ ℚ ] (S.ι q S.∼̂ₛ[ sourceRadius ] x)) →
        Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ α ] x) ×
          (f q S.∼̂ₛ[ β ] F x)
      withApproximation (q , ιq∼x) = q ,
        S.isMonotone∼̂ₛ< (S.ι q) x sourceRadius α
          (min/2₊<L α δ) ιq∼x ,
        subst (λ z → z S.∼̂ₛ[ β ] F x) (extends q)
          (S.sym∼ (F x) (F (S.ι q)) β
            (preserve (S.ι q)
              (S.isMonotone∼̂ₛ< x (S.ι q) sourceRadius δ
                (min/2₊<R α δ)
                (S.sym∼ (S.ι q) x sourceRadius ιq∼x))))


-- Pointwise centered continuity has the same Π/truncation order as ordinary
-- continuity.  The original completion-centered condition instead bundles
-- a whole local modulus before truncation.

CenteredRadiusFor :
  (ℚ → S.ℭ̂ₛ) → S.ℭ̂ₛ → ℚ₊ → Type₀
CenteredRadiusFor f x ε =
  Σ[ δ ∈ ℚ₊ ]
    (∀ q r →
      S.ι q S.∼̂ₛ[ δ ] x →
      S.ι r S.∼̂ₛ[ δ ] x →
      f q S.∼̂ₛ[ ε ] f r)


IsPointwiseCompletionCenteredContinuous :
  (ℚ → S.ℭ̂ₛ) → Type₀
IsPointwiseCompletionCenteredContinuous f =
  ∀ x ε → ∥ CenteredRadiusFor f x ε ∥₁


BundledCenteredRadii : (ℚ → S.ℭ̂ₛ) → Type₀
BundledCenteredRadii f =
  ∀ x → ∥ ((ε : ℚ₊) → CenteredRadiusFor f x ε) ∥₁


completionCentered→pointwiseCompletionCentered : ∀ {f} →
  CC.IsCompletionCenteredContinuous f →
  IsPointwiseCompletionCenteredContinuous f
completionCentered→pointwiseCompletionCentered {f} centered x ε =
  PT.map atRadius
    (centered .CC.IsCompletionCenteredContinuous.at x)
  where
  atRadius :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      CC.IsCompletionContinuousAtWith f x μ) →
    CenteredRadiusFor f x ε
  atRadius (μ , local) =
    μ ε , λ q r →
      local .CC.IsCompletionContinuousAtWith.pres∼ q r ε


ordinary→pointwiseCompletionCentered : ∀ F →
  RealOrdinaryContinuous F →
  IsPointwiseCompletionCenteredContinuous (F ∘ S.ι)
ordinary→pointwiseCompletionCentered F F-cont x ε =
  PT.map withRadius (F-cont x .IsContinuousAt.pres≈ (ε /2₊))
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.∼̂ₛ[ δ ] y →
        F x S.∼̂ₛ[ ε /2₊ ] F y)) →
    CenteredRadiusFor (F ∘ S.ι) x ε
  withRadius (δ , preserve) = δ , λ q r ιq∼x ιr∼x →
      subst (F (S.ι q) S.∼̂ₛ[_] F (S.ι r))
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (S.tri∼ (F (S.ι q)) (F x) (F (S.ι r))
          (ε /2₊) (ε /2₊)
          (S.sym∼ (F x) (F (S.ι q)) (ε /2₊)
            (preserve (S.ι q)
              (S.sym∼ (S.ι q) x δ ιq∼x)))
          (preserve (S.ι r)
            (S.sym∼ (S.ι r) x δ ιr∼x)))


-- The graph-Cauchy universal property classifies graph-compatible real
-- extensions, not arbitrary functions which merely preserve Cauchy
-- sequences.  Cauchy-sequence preservation is a consequence of this package.

GraphCauchyRestriction : Type₀
GraphCauchyRestriction = G.CauchyContinuousRestriction


GraphCauchyExtension : Type₀
GraphCauchyExtension = G.CauchyContinuousExtension


graphCauchyRestrictionExtensionEquiv :
  GraphCauchyRestriction ≃ GraphCauchyExtension
graphCauchyRestrictionExtensionEquiv =
  G.cauchyContinuousRestrictionExtensionEquiv


-- Completion-centered restrictions have an analogous classification by a
-- more familiar output package.  It consists of ordinary-continuous real
-- functions whose dense restriction retains a bundled completion-centered
-- modulus.

isPropCompletionCentered : ∀ f →
  isProp (CC.IsCompletionCenteredContinuous f)
isPropCompletionCentered f a b i
  .CC.IsCompletionCenteredContinuous.at x =
  squash₁ (a .CC.IsCompletionCenteredContinuous.at x)
    (b .CC.IsCompletionCenteredContinuous.at x) i


-- This equivalence exposes the bundled local modulus directly.

completionCentered≃bundledCenteredRadii : ∀ f →
  CC.IsCompletionCenteredContinuous f ≃ BundledCenteredRadii f
completionCentered≃bundledCenteredRadii f =
  propBiimpl→Equiv
    (isPropCompletionCentered f)
    (isPropΠ λ _ → squash₁)
    toRadii
    fromRadii
  where
  toRadii :
    CC.IsCompletionCenteredContinuous f → BundledCenteredRadii f
  toRadii centered x =
    PT.map
      (λ (μ , local) ε →
        μ ε , λ q r →
          local .CC.IsCompletionContinuousAtWith.pres∼ q r ε)
      (centered .CC.IsCompletionCenteredContinuous.at x)

  fromRadii :
    BundledCenteredRadii f → CC.IsCompletionCenteredContinuous f
  fromRadii radii .CC.IsCompletionCenteredContinuous.at x =
    PT.map package (radii x)
    where
    package :
      ((ε : ℚ₊) → CenteredRadiusFor f x ε) →
      Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        CC.IsCompletionContinuousAtWith f x μ
    package selected .fst ε = fst (selected ε)
    package selected .snd .CC.IsCompletionContinuousAtWith.pres∼
      q r ε = snd (selected ε) q r


-- Moving truncation through the epsilon-indexed Π is precisely the remaining
-- choice principle for the original completion-centered definition.

PositiveRationalChoice : Type₁
PositiveRationalChoice =
  (A : ℚ₊ → Type₀) →
  (∀ ε → ∥ A ε ∥₁) →
  ∥ ((ε : ℚ₊) → A ε) ∥₁


pointwise→completionCentered :
  PositiveRationalChoice → ∀ {f} →
  IsPointwiseCompletionCenteredContinuous f →
  CC.IsCompletionCenteredContinuous f
pointwise→completionCentered choose {f} pointwise
  .CC.IsCompletionCenteredContinuous.at x =
  PT.map package
    (choose (CenteredRadiusFor f x) (pointwise x))
  where
  package :
    ((ε : ℚ₊) → CenteredRadiusFor f x ε) →
    Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      CC.IsCompletionContinuousAtWith f x μ
  package selected .fst ε = fst (selected ε)
  package selected .snd .CC.IsCompletionContinuousAtWith.pres∼
    q r ε = snd (selected ε) q r


ordinary→completionCentered :
  PositiveRationalChoice → ∀ F →
  RealOrdinaryContinuous F →
  CC.IsCompletionCenteredContinuous (F ∘ S.ι)
ordinary→completionCentered choose F =
  pointwise→completionCentered choose ∘
  ordinary→pointwiseCompletionCentered F


CompletionCenteredRestriction : Type₀
CompletionCenteredRestriction =
  Σ[ f ∈ (ℚ → S.ℭ̂ₛ) ] CC.IsCompletionCenteredContinuous f


IsCompletionCenteredExtension :
  (S.ℭ̂ₛ → S.ℭ̂ₛ) → Type₀
IsCompletionCenteredExtension F =
  RealOrdinaryContinuous F ×
  CC.IsCompletionCenteredContinuous (F ∘ S.ι) ×
  (∀ x → G.JointlyApproximableFor (F ∘ S.ι) x (F x))


isPropIsCompletionCenteredExtension : ∀ F →
  isProp (IsCompletionCenteredExtension F)
isPropIsCompletionCenteredExtension F = isProp×
  (isPropIsContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (SP.ℭ̂ₛPremetricSpace .snd))
  (isProp×
    (isPropCompletionCentered (F ∘ S.ι))
    (isPropΠ λ x →
      G.isPropJointlyApproximableFor (F ∘ S.ι) x (F x)))


CompletionCenteredExtension : Type₀
CompletionCenteredExtension =
  Σ[ F ∈ (S.ℭ̂ₛ → S.ℭ̂ₛ) ] IsCompletionCenteredExtension F


extendCompletionCentered :
  CompletionCenteredRestriction → CompletionCenteredExtension
extendCompletionCentered (f , f-centered) =
  F ,
  CC.liftCompletionCenteredContinuous-isContinuous f f-centered ,
  subst CC.IsCompletionCenteredContinuous
    (sym restrictionPath) f-centered ,
  G.liftCauchyContinuous-joint f f-graph
  where
  f-graph = CC.completionCenteredContinuous→cauchyContinuous f-centered
  F = G.liftCauchyContinuous f f-graph

  restrictionPath : F ∘ S.ι ≡ f
  restrictionPath =
    funExt (G.liftCauchyContinuous-ι f f-graph)


restrictCompletionCentered :
  CompletionCenteredExtension → CompletionCenteredRestriction
restrictCompletionCentered (F , _ , restriction-centered , _) =
  F ∘ S.ι , restriction-centered


completionCenteredExtension→graphCauchyExtension :
  ∀ F → IsCompletionCenteredExtension F → GraphCauchyExtension
completionCenteredExtension→graphCauchyExtension
  F (_ , restriction-centered , graph) =
  F ,
  CC.completionCenteredContinuous→cauchyContinuous
    restriction-centered ,
  graph


completionCenteredExtension-isGraphSection :
  (E : CompletionCenteredExtension) →
  G.extendCauchyContinuous
    (G.restrictCauchyContinuous
      (completionCenteredExtension→graphCauchyExtension
        (fst E) (snd E))) ≡
  completionCenteredExtension→graphCauchyExtension
    (fst E) (snd E)
completionCenteredExtension-isGraphSection E =
  G.cauchyContinuousRestrictionExtensionIso .Iso.sec
    (completionCenteredExtension→graphCauchyExtension
      (fst E) (snd E))


opaque
  restrictAfterExtendCompletionCentered :
    ∀ restriction →
    restrictCompletionCentered
      (extendCompletionCentered restriction) ≡ restriction
  restrictAfterExtendCompletionCentered (f , f-centered) =
    Σ≡Prop isPropCompletionCentered
      (funExt
        (G.liftCauchyContinuous-ι f
          (CC.completionCenteredContinuous→cauchyContinuous
            f-centered)))


completionCenteredExtension-preservesCauchy :
  ∀ F → IsCompletionCenteredExtension F →
  PreservesCompletionCauchySequences F
completionCenteredExtension-preservesCauchy F F-centered =
  G.cauchyContinuousExtension-presCauchy F
    ((completionCenteredExtension→graphCauchyExtension
      F F-centered) .snd)


-- This is the intrinsic output characterization.  For a real function, the
-- exact dense-graph extension predicate above is equivalent to the familiar
-- ordinary epsilon-delta continuity together with completion-centered data
-- on its rational restriction.

completionCenteredExtension≃ordinaryAndCentered : ∀ F →
  IsCompletionCenteredExtension F ≃
  (RealOrdinaryContinuous F ×
   CC.IsCompletionCenteredContinuous (F ∘ S.ι))
completionCenteredExtension≃ordinaryAndCentered F =
  propBiimpl→Equiv
    (isPropIsCompletionCenteredExtension F)
    (isProp×
      (isPropIsContinuous
        (SP.ℭ̂ₛPremetricSpace .snd) F
        (SP.ℭ̂ₛPremetricSpace .snd))
      (isPropCompletionCentered (F ∘ S.ι)))
    (λ (F-cont , restriction-centered , _) →
      F-cont , restriction-centered)
    (λ (F-cont , restriction-centered) →
      F-cont , restriction-centered ,
      ordinaryExtension→jointlyApproximable
        (F ∘ S.ι) F (λ _ → refl) F-cont)


OrdinaryCompletionCenteredFunction : Type₀
OrdinaryCompletionCenteredFunction =
  Σ[ F ∈ (S.ℭ̂ₛ → S.ℭ̂ₛ) ]
    (RealOrdinaryContinuous F ×
     CC.IsCompletionCenteredContinuous (F ∘ S.ι))


completionCenteredExtensions≃ordinaryAndCenteredFunctions :
  CompletionCenteredExtension ≃ OrdinaryCompletionCenteredFunction
completionCenteredExtensions≃ordinaryAndCenteredFunctions =
  Σ-cong-equiv-snd completionCenteredExtension≃ordinaryAndCentered


-- The extra centered component is redundant only after commuting
-- propositional truncation with the positive-rational Π.

completionCenteredExtension≃ordinary :
  PositiveRationalChoice → ∀ F →
  IsCompletionCenteredExtension F ≃ RealOrdinaryContinuous F
completionCenteredExtension≃ordinary choose F =
  propBiimpl→Equiv
    (isPropIsCompletionCenteredExtension F)
    (isPropIsContinuous
      (SP.ℭ̂ₛPremetricSpace .snd) F
      (SP.ℭ̂ₛPremetricSpace .snd))
    fst
    (λ F-cont →
      F-cont ,
      ordinary→completionCentered choose F F-cont ,
      ordinaryExtension→jointlyApproximable
        (F ∘ S.ι) F (λ _ → refl) F-cont)


OrdinaryContinuousRealFunction : Type₀
OrdinaryContinuousRealFunction =
  Σ[ F ∈ (S.ℭ̂ₛ → S.ℭ̂ₛ) ] RealOrdinaryContinuous F


completionCenteredExtensions≃ordinaryContinuousFunctions :
  PositiveRationalChoice →
  CompletionCenteredExtension ≃ OrdinaryContinuousRealFunction
completionCenteredExtensions≃ordinaryContinuousFunctions choose =
  Σ-cong-equiv-snd
    (completionCenteredExtension≃ordinary choose)


-- For a rational-valued restriction satisfying the centered hypothesis, the
-- centered and graph definitions produce definitionally the same canonical
-- lift.  It therefore has all three useful output properties: ordinary and
-- sequential continuity, and preservation of witnessed Cauchy sequences.

completionCenteredLift-agreesWithGraphCauchyLift : ∀ f f-centered →
  completionCenteredLift f f-centered ≡
  graphCauchyLift f (completionCentered→graphCauchy f-centered)
completionCenteredLift-agreesWithGraphCauchyLift f f-centered = refl


completionCenteredLift-preservesCauchy : ∀ f f-centered →
  PreservesCompletionCauchySequences
    (completionCenteredLift f f-centered)
completionCenteredLift-preservesCauchy f f-centered =
  G.liftCauchyContinuous-presCauchy (S.ι ∘ f)
    (completionCentered→graphCauchy f-centered)


completionCenteredLift-isSequential : ∀ f f-centered →
  RealSequentiallyContinuous (completionCenteredLift f f-centered)
completionCenteredLift-isSequential f f-centered =
  realOrdinary→sequential
    (completionCenteredLift-isOrdinary f f-centered)
