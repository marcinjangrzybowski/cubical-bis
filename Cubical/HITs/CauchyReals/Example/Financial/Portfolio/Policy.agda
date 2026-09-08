module Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Policy where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)

record Limits : Type₀ where
  constructor limits
  field
    meanLimit stressLimit tailLimit : ℝ
open Limits public

module RiskPolicy {n : ℕ} (P : Distribution (suc n)) (level : TailLevel) where
  module ES = TailRisk P level

  Satisfies : Limits → Vector (suc n) → Type₀
  Satisfies caps X = (expectation P X ≤ᵣ meanLimit caps) ×
    (worstCase X ≤ᵣ stressLimit caps) × ES.Accepted X (tailLimit caps)

  satisfies-isProp : ∀ caps X → isProp (Satisfies caps X)
  satisfies-isProp caps X = isProp× (isProp≤ᵣ _ _)
    (isProp× (isProp≤ᵣ _ _) (ES.accepted-isProp X (tailLimit caps)))

  private
    convex-constant : ∀ a b c → a +ᵣ b ≡ 1 → a ·ᵣ c +ᵣ b ·ᵣ c ≡ c
    convex-constant a b c total = sym (·DistR+ a b c)
      ∙ cong (_·ᵣ c) total ∙ ·IdLᵣ c

    convex-bound : ∀ a b x y c → 0 ≤ᵣ a → 0 ≤ᵣ b → a +ᵣ b ≡ 1 →
      x ≤ᵣ c → y ≤ᵣ c → a ·ᵣ x +ᵣ b ·ᵣ y ≤ᵣ c
    convex-bound a b x y c a₊ b₊ total px py = isTrans≤≡ᵣ _ _ _
      (≤ᵣMonotone+ᵣ _ _ _ _ (≤ᵣ-o·ᵣ _ _ a a₊ px) (≤ᵣ-o·ᵣ _ _ b b₊ py))
      (convex-constant a b c total)

  -- All three policy limits are preserved throughout a real convex blend.
  -- These are real allocation parameters, not cubical path coordinates.
  satisfies-mix : ∀ caps X Y a b → 0 ≤ᵣ a → 0 ≤ᵣ b → a +ᵣ b ≡ 1 →
    Satisfies caps X → Satisfies caps Y → Satisfies caps (mix a b X Y)
  satisfies-mix caps X Y a b a₊ b₊ total (mx , sx , tx) (my , sy , ty) =
    isTrans≡≤ᵣ _ _ _
      (expectation-add P (λ i → a ·ᵣ X i) (λ i → b ·ᵣ Y i)
        ∙ cong₂ _+ᵣ_ (expectation-scale P a X) (expectation-scale P b Y))
      (convex-bound a b _ _ (meanLimit caps) a₊ b₊ total mx my) ,
    worstCase-least (mix a b X Y) (stressLimit caps)
      (λ i → convex-bound a b _ _ (stressLimit caps) a₊ b₊ total
        (isTrans≤ᵣ _ _ _ (worstCase-upper X i) sx)
        (isTrans≤ᵣ _ _ _ (worstCase-upper Y i) sy)) ,
    subst (ES.Accepted (mix a b X Y)) (convex-constant a b (tailLimit caps) total)
      (ES.accepted-weighted X Y a b (tailLimit caps) (tailLimit caps) a₊ b₊ tx ty)

  module ManagedMarket {m : ℕ} (M : Market m (suc n)) (caps : Limits) where
    allocationLoss : Allocation m → Vector (suc n)
    allocationLoss U = portfolioLoss M (probability U)

    CertifiedAllocation : Type₀
    CertifiedAllocation = Σ[ U ∈ Allocation m ] Satisfies caps (allocationLoss U)

    isSetCertifiedAllocation : isSet CertifiedAllocation
    isSetCertifiedAllocation = isSetΣ (isSetDistribution m)
      (λ U → isProp→isSet (satisfies-isProp caps (allocationLoss U)))

    -- This operation carries policy evidence with the new allocation.
    rebalance-certified : (w : UnitWeight) →
      CertifiedAllocation → CertifiedAllocation → CertifiedAllocation
    rebalance-certified w (U , pu) (V , pv) = rebalance w U V ,
      subst (Satisfies caps)
        (sym (funExt (portfolio-mix M (fst w) (1 -ᵣ fst w) (probability U) (probability V))))
        (satisfies-mix caps (allocationLoss U) (allocationLoss V) (fst w) (1 -ᵣ fst w)
          (fst (snd w)) (complement-nonnegative w) total pu pv)
      where
      total : fst w +ᵣ (1 -ᵣ fst w) ≡ 1
      total = +ᵣComm _ _ ∙ Rℝ.minusPlus 1 (fst w)

    module Economic = EconomicModel (Fin (suc n)) (Allocation m) allocationLoss

    CertifiedEconomicClass : Type₀
    CertifiedEconomicClass = Σ[ c ∈ Economic.EconomicClass ]
      Satisfies caps (Economic.quotientLoss c)

    forget-representation : CertifiedAllocation → CertifiedEconomicClass
    forget-representation (U , proof) = Economic.class U , proof

    -- Economic netting identifies even proof-bearing portfolio records.
    netting-path : (U V : CertifiedAllocation) →
      (∀ i → allocationLoss (fst U) i ≡ allocationLoss (fst V) i) →
      forget-representation U ≡ forget-representation V
    netting-path U V equivalent =
      Σ≡Prop (λ c → satisfies-isProp caps (Economic.quotientLoss c))
        (Economic.class-sound equivalent)

  -- A model reserve transports an entire tail certificate, with coefficient
  -- one in the loss error. The error is aggregated from the asset level.
  reserve-for-model-error : ∀ {m} (M N : Market m (suc n)) u error budget →
    (∀ a → 0 ≤ᵣ u a) → (∀ a i → M a i ≤ᵣ N a i +ᵣ error a) →
    ES.Accepted (portfolioLoss N u) budget →
    ES.Accepted (portfolioLoss M u) (dot u error +ᵣ budget)
  reserve-for-model-error M N u error budget u₊ error-bound =
    ES.accepted-perturbation (portfolioLoss M u) (portfolioLoss N u) (dot u error) budget
      (λ i → isTrans≤≡ᵣ _ _ _
        (portfolio-model-error M N u error u₊ error-bound i) (+ᵣComm _ _))
