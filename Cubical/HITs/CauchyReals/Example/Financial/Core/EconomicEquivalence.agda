{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding using (isEmbedding; injEmbedding)
import Cubical.Functions.Image as Image
import Cubical.HITs.SetQuotients as SQ

open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ)
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
  using (_≤ᵣ_; isProp≤ᵣ)

-- A position may retain operational data (trade identifiers, duplicate
-- instruments, or hedge decompositions). Economic identity discards such
-- distinctions precisely when every modelled scenario has the same loss.
-- No finiteness, decidable equality, or setness of Position is required.
module EconomicModel (Ω Position : Type) (loss : Position → Ω → ℝ) where

  Loss : Type
  Loss = Ω → ℝ

  isSetLoss : isSet Loss
  isSetLoss = isSetΠ (λ _ → isSetℝ)

  infix 4 _≈ᴱ_

  _≈ᴱ_ : Position → Position → Type
  p ≈ᴱ q = (ω : Ω) → loss p ω ≡ loss q ω

  isPropEconomicEquivalence : (p q : Position) → isProp (p ≈ᴱ q)
  isPropEconomicEquivalence p q = isPropΠ (λ _ → isSetℝ _ _)

  economic-refl : (p : Position) → p ≈ᴱ p
  economic-refl p ω = refl

  economic-sym : (p q : Position) → p ≈ᴱ q → q ≈ᴱ p
  economic-sym p q e ω = sym (e ω)

  economic-trans : (p q r : Position) → p ≈ᴱ q → q ≈ᴱ r → p ≈ᴱ r
  economic-trans p q r e f ω = e ω ∙ f ω

  -- Cubical function extensionality identifies pointwise economic equality
  -- with paths between complete loss functions, without an extensionality axiom.
  economic-path : {p q : Position} → p ≈ᴱ q → loss p ≡ loss q
  economic-path = funExt

  EconomicClass : Type
  EconomicClass = Position SQ./ _≈ᴱ_

  class : Position → EconomicClass
  class = SQ.[_]

  isSetEconomicClass : isSet EconomicClass
  isSetEconomicClass = SQ.squash/

  class-sound : {p q : Position} → p ≈ᴱ q → class p ≡ class q
  class-sound {p} {q} = SQ.eq/ p q

  quotientLoss : EconomicClass → Loss
  quotientLoss = SQ.rec isSetLoss loss (λ p q → economic-path)

  quotientLoss-β : (p : Position) → quotientLoss (class p) ≡ loss p
  quotientLoss-β p = refl

  class-effective : {p q : Position} → class p ≡ class q → p ≈ᴱ q
  class-effective e ω = cong (λ c → quotientLoss c ω) e

  -- Effectiveness is an equivalence of proposition-valued identity types.
  -- A quotient path cannot identify two different scenario-loss functions.
  class-path≃economic : (p q : Position) → (class p ≡ class q) ≃ (p ≈ᴱ q)
  class-path≃economic p q = propBiimpl→Equiv
    (isSetEconomicClass _ _) (isPropEconomicEquivalence p q)
    class-effective class-sound

  loss-determines-class : (c d : EconomicClass)
    → quotientLoss c ≡ quotientLoss d → c ≡ d
  loss-determines-class = SQ.elimProp2
    (λ c d → isPropΠ (λ _ → isSetEconomicClass c d))
    (λ p q e → class-sound (funExt⁻ e))

  quotientLoss-isEmbedding : isEmbedding quotientLoss
  quotientLoss-isEmbedding = injEmbedding isSetLoss
    (λ {c} {d} → loss-determines-class c d)

  -- This image records realizability only propositionally. The equivalence
  -- below therefore does not select an actual position for each loss profile.
  RealizableLoss : Type
  RealizableLoss = Image.Image loss

  classes≃realizableLosses : EconomicClass ≃ RealizableLoss
  classes≃realizableLosses = Image.imagesEquiv
    (class , SQ.[]surjective)
    (quotientLoss , quotientLoss-isEmbedding)
    (Image.restrictToImage loss , Image.isSurjectionImageRestriction loss)
    (Image.imageInclusion loss)
    refl

  classes≃realizableLosses-preserves-loss : (c : EconomicClass)
    → fst (fst classes≃realizableLosses c) ≡ quotientLoss c
  classes≃realizableLosses-preserves-loss = Image.imagesEmbeddingComm
    (class , SQ.[]surjective)
    (quotientLoss , quotientLoss-isEmbedding)
    (Image.restrictToImage loss , Image.isSurjectionImageRestriction loss)
    (Image.imageInclusion loss)
    refl

  -- Univalence permits transport of constructions between the quotient
  -- presentation and the realizable-loss presentation.
  classes≡realizableLosses : EconomicClass ≡ RealizableLoss
  classes≡realizableLosses = ua classes≃realizableLosses

  -- Every functional on scenario losses is automatically representation
  -- invariant. In applications ρ can be a stress maximum, expectation,
  -- expected-shortfall certificate, or another already constructed functional.
  module Risk (ρ : Loss → ℝ) where

    positionRisk : Position → ℝ
    positionRisk p = ρ (loss p)

    quotientRisk : EconomicClass → ℝ
    quotientRisk c = ρ (quotientLoss c)

    quotientRisk-β : (p : Position) → quotientRisk (class p) ≡ positionRisk p
    quotientRisk-β p = refl

    realizableRisk : RealizableLoss → ℝ
    realizableRisk (profile , realizable) = ρ profile

    quotient-to-image-preserves-risk : (c : EconomicClass)
      → realizableRisk (fst classes≃realizableLosses c) ≡ quotientRisk c
    quotient-to-image-preserves-risk c =
      cong ρ (classes≃realizableLosses-preserves-loss c)

    risk-invariant : {p q : Position} → p ≈ᴱ q → positionRisk p ≡ positionRisk q
    risk-invariant e = cong ρ (economic-path e)

    -- Quotient elimination also gives uniqueness: specifying the risk on
    -- representatives determines it on every economic class.
    quotientRisk-unique : (r : EconomicClass → ℝ)
      → ((p : Position) → r (class p) ≡ positionRisk p)
      → r ≡ quotientRisk
    quotientRisk-unique r agrees = funExt
      (SQ.elimProp (λ c → isSetℝ (r c) (quotientRisk c)) agrees)

    RiskLimit : ℝ → EconomicClass → Type
    RiskLimit cap c = quotientRisk c ≤ᵣ cap

    isPropRiskLimit : (cap : ℝ) (c : EconomicClass) → isProp (RiskLimit cap c)
    isPropRiskLimit cap c = isProp≤ᵣ _ _

    -- The exact same checked limit can be carried through a portfolio
    -- compression, netting, or hedge decomposition with identical losses.
    transfer-risk-limit : {cap : ℝ} {p q : Position}
      → p ≈ᴱ q → positionRisk p ≤ᵣ cap → positionRisk q ≤ᵣ cap
    transfer-risk-limit {cap} e = subst (_≤ᵣ cap) (risk-invariant e)

    risk-limits≃ : (cap : ℝ) {p q : Position} → p ≈ᴱ q
      → (positionRisk p ≤ᵣ cap) ≃ (positionRisk q ≤ᵣ cap)
    risk-limits≃ cap {p} {q} e = propBiimpl→Equiv
      (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
      (transfer-risk-limit e)
      (transfer-risk-limit (economic-sym p q e))

    -- A certified class stores the economic position together with evidence
    -- that its risk lies below the cap. Proof irrelevance prevents different
    -- derivations of the same certificate from creating different positions.
    CertifiedClass : ℝ → Type
    CertifiedClass cap = Σ[ c ∈ EconomicClass ] RiskLimit cap c

    isSetCertifiedClass : (cap : ℝ) → isSet (CertifiedClass cap)
    isSetCertifiedClass cap = isSetΣ isSetEconomicClass
      (λ c → isProp→isSet (isPropRiskLimit cap c))

    certify : (cap : ℝ) (p : Position)
      → positionRisk p ≤ᵣ cap → CertifiedClass cap
    certify cap p proof = class p , proof

    certified-class-path : {cap : ℝ} (c d : CertifiedClass cap)
      → fst c ≡ fst d → c ≡ d
    certified-class-path {cap} c d = Σ≡Prop (isPropRiskLimit cap)

    certified-representatives-equal : {cap : ℝ} {p q : Position}
      → (e : p ≈ᴱ q)
      → (p-ok : positionRisk p ≤ᵣ cap) (q-ok : positionRisk q ≤ᵣ cap)
      → certify cap p p-ok ≡ certify cap q q-ok
    certified-representatives-equal e p-ok q-ok =
      certified-class-path _ _ (class-sound e)
