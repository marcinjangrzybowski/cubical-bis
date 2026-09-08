module Cubical.HITs.CauchyReals.Example.Financial.Margin.Base where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario as Scenario
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F

-- X i is the signed closeout amount owed TO the broker by one client
-- netting set, in domestic currency. C i is eligible collateral value in
-- the same scenario and currency. A negative claim is owed by the broker.
-- The call is the least NONNEGATIVE domestic cash top-up covering all
-- modeled scenarios. Calculating a call does not assert that it is paid.
requiredMargin : ∀ {n} → Vector (suc n) → Vector (suc n) → ℝ
requiredMargin X C = worstCase (λ i → stopLoss (X i) (C i))

requiredMargin-nonnegative : ∀ {n} (X C : Vector (suc n)) → 0 ≤ᵣ requiredMargin X C
requiredMargin-nonnegative X C = isTrans≤ᵣ _ _ _
  (stopLoss-nonnegative (X F.zero) (C F.zero))
  (worstCase-upper (λ i → stopLoss (X i) (C i)) F.zero)

margin-coverage : ∀ {n} (X C : Vector (suc n)) i →
  X i ≤ᵣ C i +ᵣ requiredMargin X C
margin-coverage X C i = isTrans≤ᵣ _ _ _ (stopLoss-reconstruct (X i) (C i))
  (≤ᵣ-o+ _ _ (C i) (worstCase-upper (λ j → stopLoss (X j) (C j)) i))

margin-bound→coverage : ∀ {n} (X C : Vector (suc n)) b →
  requiredMargin X C ≤ᵣ b → ∀ i → X i ≤ᵣ C i +ᵣ b
margin-bound→coverage X C b bound i = isTrans≤ᵣ _ _ _
  (margin-coverage X C i) (≤ᵣ-o+ _ _ (C i) bound)

margin-least : ∀ {n} (X C : Vector (suc n)) b → 0 ≤ᵣ b →
  (∀ i → X i ≤ᵣ C i +ᵣ b) → requiredMargin X C ≤ᵣ b
margin-least X C b b₊ coverage = worstCase-least (λ i → stopLoss (X i) (C i)) b
  (λ i → stopLoss-upper (X i) (C i) b b₊ (coverage i))

-- Every nonempty finite margin calculation instantiates the arbitrary
-- scenario certificate. No binding scenario needs to be selected.
finite-margin-certificate : ∀ {n} (X C : Vector (suc n)) →
  Scenario.MarginCertificate (λ _ → Unit) X C (requiredMargin X C)
finite-margin-certificate X C .Scenario.certificate-nonnegative = requiredMargin-nonnegative X C
finite-margin-certificate X C .Scenario.certificate-coverage i _ = margin-coverage X C i
finite-margin-certificate X C .Scenario.certificate-least b b₊ coverage =
  margin-least X C b b₊ (λ i → coverage i tt)

-- Exactness from a supplied binding index; this does not choose a maximizer
-- of arbitrary Cauchy-real data.
margin-exact-at : ∀ {n} (X C : Vector (suc n)) m → 0 ≤ᵣ m →
  (∀ i → X i ≤ᵣ C i +ᵣ m) → (i : Fin (suc n)) →
  X i -ᵣ C i ≡ m → requiredMargin X C ≡ m
margin-exact-at X C m m₊ coverage i equation = isAntisym≤ᵣ _ _
  (margin-least X C m m₊ coverage)
  (Scenario.coverage-forces-difference (X i) (C i) m equation _ (margin-coverage X C i))

-- Capital certificates and scenario coverage obligations are equivalent
-- propositions; univalence provides a path for dependent proof transport.
margin-bound≃coverage : ∀ {n} (X C : Vector (suc n)) b → 0 ≤ᵣ b →
  (requiredMargin X C ≤ᵣ b) ≃ (∀ i → X i ≤ᵣ C i +ᵣ b)
margin-bound≃coverage X C b b₊ = propBiimpl→Equiv
  (isProp≤ᵣ _ _) (isPropΠ (λ _ → isProp≤ᵣ _ _))
  (margin-bound→coverage X C b) (margin-least X C b b₊)

margin-policy-path : ∀ {n} (X C : Vector (suc n)) b → 0 ≤ᵣ b →
  (requiredMargin X C ≤ᵣ b) ≡ (∀ i → X i ≤ᵣ C i +ᵣ b)
margin-policy-path X C b b₊ = ua (margin-bound≃coverage X C b b₊)

margin-claim-monotone : ∀ {n} (X Y C : Vector (suc n)) →
  (∀ i → X i ≤ᵣ Y i) → requiredMargin X C ≤ᵣ requiredMargin Y C
margin-claim-monotone X Y C bound = worstCase-monotone _ _
  (λ i → stopLoss-monotone (X i) (Y i) (C i) (bound i))

margin-collateral-antitone : ∀ {n} (X C D : Vector (suc n)) →
  (∀ i → C i ≤ᵣ D i) → requiredMargin X D ≤ᵣ requiredMargin X C
margin-collateral-antitone X C D bound = worstCase-monotone _ _
  (λ i → stopLoss-antitone-threshold (X i) (C i) (D i) (bound i))

margin-covered-zero : ∀ {n} (X C : Vector (suc n)) →
  (∀ i → X i ≤ᵣ C i) → requiredMargin X C ≡ 0
margin-covered-zero {n} X C coverage =
  cong worstCase (funExt (λ i → stopLoss-zero-below (X i) (C i) (coverage i)))
  ∙ worstCase-constant {n} 0

-- postCash describes a changed collateral state: the cash has actually
-- been posted, is eligible at par, and remains available in every scenario.
postCash : ∀ {n} → Vector n → ℝ → Vector n
postCash C paid i = C i +ᵣ paid

postCash-nonnegative : ∀ {n} (C : Vector n) paid →
  (∀ i → 0 ≤ᵣ C i) → 0 ≤ᵣ paid → ∀ i → 0 ≤ᵣ postCash C paid i
postCash-nonnegative C paid C₊ paid₊ i = nonnegative-add (C i) paid (C₊ i) paid₊

sufficient-cash-zero : ∀ {n} (X C : Vector (suc n)) paid →
  requiredMargin X C ≤ᵣ paid → requiredMargin X (postCash C paid) ≡ 0
sufficient-cash-zero X C paid bound =
  margin-covered-zero X (postCash C paid) (margin-bound→coverage X C paid bound)

paid-required-margin-zero : ∀ {n} (X C : Vector (suc n)) →
  requiredMargin X (postCash C (requiredMargin X C)) ≡ 0
paid-required-margin-zero X C = sufficient-cash-zero X C (requiredMargin X C) (≤ᵣ-refl _)

-- An arbitrary previously paid domestic cash amount can be followed by a
-- residual call. This is an accounting decomposition, not a regulatory
-- definition of variation margin or initial margin.
paid-cash-and-residual-cover : ∀ {n} (X C : Vector (suc n)) paid i →
  X i ≤ᵣ C i +ᵣ (paid +ᵣ requiredMargin X (postCash C paid))
paid-cash-and-residual-cover X C paid i = isTrans≤≡ᵣ _ _ _
  (margin-coverage X (postCash C paid) i)
  (sym (+ᵣAssoc (C i) paid (requiredMargin X (postCash C paid))))

-- The residual call after a nonnegative actual cash payment is the
-- positive part of the original call less that payment. The hypothesis is
-- necessary: a withdrawal may first use collateral surplus discarded by
-- the original nonnegative call.
margin-postCash : ∀ {n} (X C : Vector (suc n)) paid → 0 ≤ᵣ paid →
  requiredMargin X (postCash C paid) ≡ stopLoss (requiredMargin X C) paid
margin-postCash X C paid paid₊ = isAntisym≤ᵣ _ _ residual≤request request≤residual
  where
  request residual : ℝ
  request = stopLoss (requiredMargin X C) paid
  residual = requiredMargin X (postCash C paid)

  request₊ : 0 ≤ᵣ request
  request₊ = stopLoss-nonnegative (requiredMargin X C) paid

  residual₊ : 0 ≤ᵣ residual
  residual₊ = requiredMargin-nonnegative X (postCash C paid)

  residual≤request : residual ≤ᵣ request
  residual≤request = margin-least X (postCash C paid) request request₊ λ i →
    isTrans≤≡ᵣ _ _ _
      (margin-bound→coverage X C (paid +ᵣ request)
        (stopLoss-reconstruct (requiredMargin X C) paid) i)
      (+ᵣAssoc (C i) paid request)

  original-covered : requiredMargin X C ≤ᵣ paid +ᵣ residual
  original-covered = margin-least X C (paid +ᵣ residual)
    (nonnegative-add paid residual paid₊ residual₊)
    (paid-cash-and-residual-cover X C paid)

  request≤residual : request ≤ᵣ residual
  request≤residual = stopLoss-upper (requiredMargin X C) paid residual residual₊ original-covered

-- Aggregation applies inside a modeled netting set. It does not establish
-- any right to net claims or collateral belonging to different clients.
margin-subadditive : ∀ {n} (X Y C D : Vector (suc n)) →
  requiredMargin (λ i → X i +ᵣ Y i) (λ i → C i +ᵣ D i)
    ≤ᵣ requiredMargin X C +ᵣ requiredMargin Y D
margin-subadditive X Y C D = isTrans≤ᵣ _ _ _
  (worstCase-monotone _ _ (λ i → stopLoss-subadditive (X i) (Y i) (C i) (D i)))
  (worstCase-subadditive (λ i → stopLoss (X i) (C i)) (λ i → stopLoss (Y i) (D i)))

-- This conic bound also proves convexity when a + b = 1.
margin-weighted : ∀ {n} (X Y C D : Vector (suc n)) a b → 0 ≤ᵣ a → 0 ≤ᵣ b →
  requiredMargin (λ i → a ·ᵣ X i +ᵣ b ·ᵣ Y i) (λ i → a ·ᵣ C i +ᵣ b ·ᵣ D i)
    ≤ᵣ a ·ᵣ requiredMargin X C +ᵣ b ·ᵣ requiredMargin Y D
margin-weighted X Y C D a b a₊ b₊ = isTrans≤ᵣ _ _ _
  (worstCase-monotone _ _
    (λ i → stopLoss-weighted-bound a b (X i) (Y i) (C i) (D i) a₊ b₊))
  (worstCase-weighted (λ i → stopLoss (X i) (C i))
    (λ i → stopLoss (Y i) (D i)) a b a₊ b₊)

-- A uniform upward claim error adds at most the same amount to the call.
margin-claim-perturbation : ∀ {n} (X Y C : Vector (suc n)) ε →
  0 ≤ᵣ ε → (∀ i → X i ≤ᵣ Y i +ᵣ ε) →
  requiredMargin X C ≤ᵣ requiredMargin Y C +ᵣ ε
margin-claim-perturbation X Y C ε ε₊ bound = worstCase-perturbation _ _ ε
  (λ i → stopLoss-perturbation (X i) (Y i) (C i) ε ε₊ (bound i))

-- spot is domestic currency per foreign unit. retention is the eligible
-- fraction AFTER a haircut, normally between 0 and 1. These functions do
-- not infer haircut rates or collateral eligibility from market data.
eligibleCollateral : ℝ → ℝ → ℝ → ℝ → ℝ
eligibleCollateral domestic retention spot foreign =
  domestic +ᵣ (retention ·ᵣ spot) ·ᵣ foreign

eligibleCollateral-nonnegative : ∀ domestic retention spot foreign →
  0 ≤ᵣ domestic → 0 ≤ᵣ retention → 0 ≤ᵣ spot → 0 ≤ᵣ foreign →
  0 ≤ᵣ eligibleCollateral domestic retention spot foreign
eligibleCollateral-nonnegative domestic retention spot foreign d₊ r₊ s₊ f₊ =
  nonnegative-add domestic _ d₊
    (nonnegative-mul _ foreign (nonnegative-mul retention spot r₊ s₊) f₊)

eligibleCollateral-at-most-market : ∀ domestic retention spot foreign →
  retention ≤ᵣ 1 → 0 ≤ᵣ spot → 0 ≤ᵣ foreign →
  eligibleCollateral domestic retention spot foreign ≤ᵣ domestic +ᵣ spot ·ᵣ foreign
eligibleCollateral-at-most-market domestic retention spot foreign r≤one s₊ f₊ =
  ≤ᵣ-o+ _ _ domestic
    (≤ᵣ-·ᵣo _ _ foreign f₊
      (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo retention 1 spot s₊ r≤one) (·IdLᵣ spot)))

eligibleCollateral-spot-monotone : ∀ domestic retention spot spot' foreign →
  0 ≤ᵣ retention → 0 ≤ᵣ foreign → spot ≤ᵣ spot' →
  eligibleCollateral domestic retention spot foreign
    ≤ᵣ eligibleCollateral domestic retention spot' foreign
eligibleCollateral-spot-monotone domestic retention spot spot' foreign r₊ f₊ bound =
  ≤ᵣ-o+ _ _ domestic
    (≤ᵣ-·ᵣo _ _ foreign f₊ (≤ᵣ-o·ᵣ spot spot' retention r₊ bound))

eligibleCollateral-retention-monotone : ∀ domestic retention retention' spot foreign →
  0 ≤ᵣ spot → 0 ≤ᵣ foreign → retention ≤ᵣ retention' →
  eligibleCollateral domestic retention spot foreign
    ≤ᵣ eligibleCollateral domestic retention' spot foreign
eligibleCollateral-retention-monotone domestic retention retention' spot foreign s₊ f₊ bound =
  ≤ᵣ-o+ _ _ domestic
    (≤ᵣ-·ᵣo _ _ foreign f₊ (≤ᵣ-·ᵣo retention retention' spot s₊ bound))

currencyCollateral : ∀ {n} → ℝ → ℝ → Vector n → ℝ → Vector n
currencyCollateral domestic retention spots foreign i =
  eligibleCollateral domestic retention (spots i) foreign

currencyCollateral-nonnegative : ∀ {n} domestic retention (spots : Vector n) foreign →
  0 ≤ᵣ domestic → 0 ≤ᵣ retention → (∀ i → 0 ≤ᵣ spots i) → 0 ≤ᵣ foreign →
  ∀ i → 0 ≤ᵣ currencyCollateral domestic retention spots foreign i
currencyCollateral-nonnegative domestic retention spots foreign d₊ r₊ spots₊ f₊ i =
  eligibleCollateral-nonnegative domestic retention (spots i) foreign d₊ r₊ (spots₊ i) f₊

-- Only collateral FX is varied here: the claim vector is held fixed.
-- If the claims also depend on spot, their change must be modeled separately.
currency-margin-spot-antitone : ∀ {n} (X spots spots' : Vector (suc n))
  domestic retention foreign → 0 ≤ᵣ retention → 0 ≤ᵣ foreign →
  (∀ i → spots i ≤ᵣ spots' i) →
  requiredMargin X (currencyCollateral domestic retention spots' foreign)
    ≤ᵣ requiredMargin X (currencyCollateral domestic retention spots foreign)
currency-margin-spot-antitone X spots spots' domestic retention foreign r₊ f₊ bound =
  margin-collateral-antitone X (currencyCollateral domestic retention spots foreign)
    (currencyCollateral domestic retention spots' foreign)
    (λ i → eligibleCollateral-spot-monotone domestic retention (spots i) (spots' i)
      foreign r₊ f₊ (bound i))
