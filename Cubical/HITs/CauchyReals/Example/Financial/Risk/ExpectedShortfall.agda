module Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- κ = 1 / (1 - confidence).  Recording κ ≥ 1 avoids partial inversion.
-- κ = 1 includes expectation; the worked example uses κ = 2 (50% tail).
record TailLevel : Type₀ where
  constructor tail-level
  field
    multiplier : ℝ
    at-least-one : 1 ≤ᵣ multiplier
open TailLevel public

tail-nonnegative : (level : TailLevel) → 0 ≤ᵣ multiplier level
tail-nonnegative level = isTrans≤ᵣ 0 1 _ decℚ≤ᵣ? (at-least-one level)

module TailRisk {n : ℕ} (P : Distribution n) (level : TailLevel) where
  κ : ℝ
  κ = multiplier level

  -- Rockafellar--Uryasev's finite-scenario objective for loss convention.
  objective : Vector n → ℝ → ℝ
  objective X t = t +ᵣ κ ·ᵣ expectation P (λ i → stopLoss (X i) t)

  Admissible : Distribution n → Type₀
  Admissible Q = DensityCap P κ Q

  nominal-admissible : Admissible P
  nominal-admissible i = isTrans≡≤ᵣ _ _ _ (sym (·IdLᵣ (probability P i)))
    (≤ᵣ-·ᵣo 1 κ (probability P i) (probability-nonnegative P i) (at-least-one level))

  -- A feasible dual probability gives a lower bound at EVERY threshold.
  -- No quantile, sorted real vector, supremum, or choice principle is used.
  weak-duality : (X : Vector n) (Q : Distribution n) → Admissible Q →
    ∀ t → expectation Q X ≤ᵣ objective X t
  weak-duality X Q cap t = isTrans≤ᵣ _ _ _
    (isTrans≤≡ᵣ _ _ _
      (expectation-monotone Q X (λ i → t +ᵣ stopLoss (X i) t)
        (λ i → stopLoss-reconstruct (X i) t))
      (expectation-add Q (λ _ → t) (λ i → stopLoss (X i) t)
        ∙ cong (_+ᵣ expectation Q (λ i → stopLoss (X i) t))
            (expectation-constant Q t)))
    (≤ᵣ-o+ _ _ t (capped-expectation P Q κ
      (λ i → stopLoss (X i) t) cap (λ i → stopLoss-nonnegative (X i) t)))

  expectation-lower-bound : (X : Vector n) → ∀ t → expectation P X ≤ᵣ objective X t
  expectation-lower-bound X = weak-duality X P nominal-admissible

  objective-at-upper-bound : ∀ (X : Vector n) t → (∀ i → X i ≤ᵣ t) →
    objective X t ≡ t
  objective-at-upper-bound X t bound =
    cong (λ z → t +ᵣ κ ·ᵣ z)
      (cong (expectation P) (funExt (λ i → stopLoss-zero-below (X i) t (bound i)))
        ∙ expectation-constant P 0)
    ∙ cong (t +ᵣ_) (Rℝ.0RightAnnihilates κ) ∙ +IdR t

  objective-monotone : ∀ (X Y : Vector n) t →
    (∀ i → X i ≤ᵣ Y i) → objective X t ≤ᵣ objective Y t
  objective-monotone X Y t bound = ≤ᵣ-o+ _ _ t
    (≤ᵣ-o·ᵣ _ _ κ (tail-nonnegative level)
      (expectation-monotone P _ _ (λ i → stopLoss-monotone _ _ t (bound i))))

  objective-cash : ∀ (X : Vector n) t c →
    objective (λ i → c +ᵣ X i) (c +ᵣ t) ≡ c +ᵣ objective X t
  objective-cash X t c =
    cong ((c +ᵣ t) +ᵣ_) (cong (κ ·ᵣ_)
      (cong (expectation P) (funExt (λ i → stopLoss-translation (X i) t c))))
    ∙ sym (+ᵣAssoc c t _)

  objective-subadditive : ∀ (X Y : Vector n) s t →
    objective (λ i → X i +ᵣ Y i) (s +ᵣ t)
      ≤ᵣ objective X s +ᵣ objective Y t
  objective-subadditive X Y s t = isTrans≤≡ᵣ _ _ _
    (≤ᵣ-o+ _ _ (s +ᵣ t)
      (≤ᵣ-o·ᵣ _ _ κ (tail-nonnegative level)
        (isTrans≤≡ᵣ _ _ _
          (expectation-monotone P _ _ (λ i → stopLoss-subadditive (X i) (Y i) s t))
          (expectation-add P (λ i → stopLoss (X i) s) (λ i → stopLoss (Y i) t)))))
    (distribute s t _ _)
    where
    distribute : ∀ s t u v → (s +ᵣ t) +ᵣ κ ·ᵣ (u +ᵣ v)
      ≡ (s +ᵣ κ ·ᵣ u) +ᵣ (t +ᵣ κ ·ᵣ v)
    distribute s t u v = ℝ!

  objective-weighted : ∀ (X Y : Vector n) a b s t → 0 ≤ᵣ a → 0 ≤ᵣ b →
    objective (λ i → a ·ᵣ X i +ᵣ b ·ᵣ Y i) (a ·ᵣ s +ᵣ b ·ᵣ t)
      ≤ᵣ a ·ᵣ objective X s +ᵣ b ·ᵣ objective Y t
  objective-weighted X Y a b s t a₊ b₊ = isTrans≤≡ᵣ _ _ _
    (≤ᵣ-o+ _ _ (a ·ᵣ s +ᵣ b ·ᵣ t)
      (≤ᵣ-o·ᵣ _ _ κ (tail-nonnegative level)
        (isTrans≤≡ᵣ _ _ _
          (expectation-monotone P _ _
            (λ i → stopLoss-weighted-bound a b (X i) (Y i) s t a₊ b₊))
          (expectation-add P (λ i → a ·ᵣ stopLoss (X i) s) (λ i → b ·ᵣ stopLoss (Y i) t)
            ∙ cong₂ _+ᵣ_ (expectation-scale P a (λ i → stopLoss (X i) s))
                (expectation-scale P b (λ i → stopLoss (Y i) t))))))
    (distribute a b s t _ _)
    where
    distribute : ∀ a b s t u v →
      (a ·ᵣ s +ᵣ b ·ᵣ t) +ᵣ κ ·ᵣ (a ·ᵣ u +ᵣ b ·ᵣ v)
        ≡ a ·ᵣ (s +ᵣ κ ·ᵣ u) +ᵣ b ·ᵣ (t +ᵣ κ ·ᵣ v)
    distribute a b s t u v = ℝ!

  -- Move the threshold with the model error. This gives coefficient ONE,
  -- rather than κ, in the risk-budget perturbation estimate.
  objective-perturbation : ∀ (X Y : Vector n) t ε →
    (∀ i → X i ≤ᵣ ε +ᵣ Y i) →
    objective X (ε +ᵣ t) ≤ᵣ ε +ᵣ objective Y t
  objective-perturbation X Y t ε bound =
    isTrans≤≡ᵣ _ _ _ (objective-monotone X (λ i → ε +ᵣ Y i) (ε +ᵣ t) bound)
      (objective-cash Y t ε)

  UpperCertificate : Vector n → ℝ → Type₀
  UpperCertificate X budget = Σ[ t ∈ ℝ ] (objective X t ≤ᵣ budget)

  -- Propositional truncation hides the threshold without choosing one.
  Accepted : Vector n → ℝ → Type₀
  Accepted X budget = PT.∥ UpperCertificate X budget ∥₁

  accepted-isProp : ∀ X budget → isProp (Accepted X budget)
  accepted-isProp X budget = PT.squash₁

  accepted-from-scenario-bound : ∀ X budget → (∀ i → X i ≤ᵣ budget) → Accepted X budget
  accepted-from-scenario-bound X budget bound = PT.∣ budget ,
    ≡ᵣWeaken≤ᵣ _ _ (objective-at-upper-bound X budget bound) ∣₁

  accepted-monotone : ∀ X Y budget → (∀ i → X i ≤ᵣ Y i) →
    Accepted Y budget → Accepted X budget
  accepted-monotone X Y budget bound = PT.map
    (λ (t , p) → t , isTrans≤ᵣ _ _ _ (objective-monotone X Y t bound) p)

  accepted-sound : ∀ X budget → Accepted X budget →
    (Q : Distribution n) → Admissible Q → expectation Q X ≤ᵣ budget
  accepted-sound X budget accepted Q cap = PT.rec (isProp≤ᵣ _ _)
    (λ (t , bound) → isTrans≤ᵣ _ _ _ (weak-duality X Q cap t) bound) accepted

  accepted-weighted : ∀ X Y a b u v → 0 ≤ᵣ a → 0 ≤ᵣ b →
    Accepted X u → Accepted Y v →
    Accepted (λ i → a ·ᵣ X i +ᵣ b ·ᵣ Y i) (a ·ᵣ u +ᵣ b ·ᵣ v)
  accepted-weighted X Y a b u v a₊ b₊ = PT.map2
    (λ (s , ps) (t , pt) → (a ·ᵣ s +ᵣ b ·ᵣ t) ,
      isTrans≤ᵣ _ _ _ (objective-weighted X Y a b s t a₊ b₊)
        (≤ᵣMonotone+ᵣ _ _ _ _
          (≤ᵣ-o·ᵣ _ _ a a₊ ps) (≤ᵣ-o·ᵣ _ _ b b₊ pt)))

  accepted-perturbation : ∀ X Y ε budget →
    (∀ i → X i ≤ᵣ ε +ᵣ Y i) → Accepted Y budget → Accepted X (ε +ᵣ budget)
  accepted-perturbation X Y ε budget bound = PT.map
    (λ (t , p) → (ε +ᵣ t) ,
      isTrans≤ᵣ _ _ _ (objective-perturbation X Y t ε bound) (≤ᵣ-o+ _ _ ε p))

  -- This is a checkable certificate, NOT an assumption that every problem
  -- has an optimizer. A concrete example below constructs all four fields.
  record OptimalityCertificate (X : Vector n) : Type₀ where
    field
      threshold : ℝ
      dual : Distribution n
      dual-admissible : Admissible dual
      tight : objective X threshold ≡ expectation dual X
  open OptimalityCertificate public

  certifiedValue : ∀ X → OptimalityCertificate X → ℝ
  certifiedValue X cert = objective X (threshold cert)

  global-minimum : ∀ X (cert : OptimalityCertificate X) t →
    certifiedValue X cert ≤ᵣ objective X t
  global-minimum X cert t = isTrans≡≤ᵣ _ _ _ (tight cert)
    (weak-duality X (dual cert) (dual-admissible cert) t)

  certificate-value-unique : ∀ X (c d : OptimalityCertificate X) →
    certifiedValue X c ≡ certifiedValue X d
  certificate-value-unique X c d = isAntisym≤ᵣ _ _
    (global-minimum X c (threshold d)) (global-minimum X d (threshold c))

  -- A value is the attained global minimum, with attainment truncated so
  -- neither a preferred quantile nor a selected representative is exposed.
  IsCVaR : Vector n → ℝ → Type₀
  IsCVaR X r = (∀ t → r ≤ᵣ objective X t) ×
    PT.∥ Σ[ t ∈ ℝ ] (objective X t ≡ r) ∥₁

  isPropIsCVaR : ∀ X r → isProp (IsCVaR X r)
  isPropIsCVaR X r = isProp× (isPropΠ (λ _ → isProp≤ᵣ _ _)) PT.squash₁

  certified-CVaR : ∀ X (cert : OptimalityCertificate X) →
    IsCVaR X (certifiedValue X cert)
  certified-CVaR X cert = global-minimum X cert , PT.∣ threshold cert , refl ∣₁

  CVaR-unique : ∀ X r s → IsCVaR X r → IsCVaR X s → r ≡ s
  CVaR-unique X r s (lr , ar) (ls , as) = isAntisym≤ᵣ r s
    (PT.rec (isProp≤ᵣ r s) (λ (t , p) → isTrans≤≡ᵣ _ _ _ (lr t) p) as)
    (PT.rec (isProp≤ᵣ s r) (λ (t , p) → isTrans≤≡ᵣ _ _ _ (ls t) p) ar)

  isPropCVaRValue : ∀ X → isProp (Σ ℝ (IsCVaR X))
  isPropCVaRValue X (r , pr) (s , ps) =
    Σ≡Prop (isPropIsCVaR X) (CVaR-unique X r s pr ps)
