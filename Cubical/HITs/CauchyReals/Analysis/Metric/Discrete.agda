module Cubical.HITs.CauchyReals.Analysis.Metric.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int as ℤ
open import Cubical.Data.Rationals as ℚ

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; fromNatℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
  using (≤ᵣ-o+)
  renaming (+IdL to +ᵣIdL ; +IdR to +ᵣIdR)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Analysis.Metric.Base

DiscreteMetricStr : ∀ {ℓ} {A : Type ℓ} → Discrete A → MetricSpaceStr A
DiscreteMetricStr _≟_ = ww
 where

 module _ (x y : _) where
  discDist : Dec (x ≡ y) → ℝ
  discDist (yes p) = 0
  discDist (no ¬p) = 1

  discDistNonNeg : ∀ d → 0 ≤ᵣ discDist d
  discDistNonNeg (yes p) = decℚ≤ᵣ?
  discDistNonNeg (no ¬p) = decℚ≤ᵣ?

  discDist0→ : ∀ d → 0 ≡ discDist d → x ≡ y
  discDist0→ (yes p) x = p
  discDist0→ (no ¬p) x = ⊥.rec (ℤ.0≢1-ℤ (ℚ.eq/⁻¹ _ _ (inj-rat _ _ x)))

 discDistSym : ∀ x y d d' → discDist x y d ≡ discDist y x d'
 discDistSym x y (yes p) (yes p₁) = refl
 discDistSym x y (yes p) (no ¬p) = ⊥.rec (¬p (sym p))
 discDistSym x y (no ¬p) (yes p) = ⊥.rec (¬p (sym p))
 discDistSym x y (no ¬p) (no ¬p₁) = refl

 discDistTriangle : ∀ x y z d d' d'' →
      discDist x z d ≤ᵣ
      discDist x y d' +ᵣ discDist y z d''
 discDistTriangle x y z (yes p) d' d'' =
   snd (NonNegativeReals._+₀₊_
     (_ , discDistNonNeg x y d') (_ , discDistNonNeg y z d''))
 discDistTriangle x y z (no ¬p) (yes p) (yes p₁) = ⊥.rec (¬p (p ∙ p₁))
 discDistTriangle x y z (no ¬p) (yes p) (no ¬p₁) =
   ≡ᵣWeaken≤ᵣ _ _ (sym (+ᵣIdL _))
 discDistTriangle x y z (no ¬p) (no ¬p₁) d'' =
  isTrans≡≤ᵣ _ _ _ (sym (+ᵣIdR _)) (≤ᵣ-o+ _ _ 1 (discDistNonNeg y z d''))
 open IsMetric

 w : IsMetric _ (λ x y → discDist _ _ (x ≟ y))
 w .is-set = Discrete→isSet _≟_
 w .𝑑-nonNeg x y = discDistNonNeg x y (x ≟ y)
 w .𝑑-sym x y = discDistSym x y (x ≟ y) (y ≟ x)
 w .𝑑-pos x y 0<d x=y =
   isIrrefl<ᵣ 0
     (isTrans<≡ᵣ _ _ _ 0<d (cong (discDist x y)
      (isPropDec (Discrete→isSet _≟_ x y) (x ≟ y) (yes x=y))))

 w .𝑑-zero→≡ x y = discDist0→ x y (x ≟ y)
 w .𝑑-≡→zero x y x=y = cong (discDist x y)
      (isPropDec (Discrete→isSet _≟_ x y) (yes x=y) (x ≟ y))
 w .𝑑-triangle x y z = discDistTriangle x y z
   (x ≟ z) (x ≟ y) (y ≟ z)

 ww : MetricSpaceStr _
 ww .MetricSpaceStr.𝑑[_,_] x y = discDist _ _ (x ≟ y)
 ww .MetricSpaceStr.isMetric = w

trivialMetricSpace : MetricSpace₀
trivialMetricSpace = _ , DiscreteMetricStr {A = Unit} λ _ _ → yes refl

isUContFromTrivialMetricSpace : ∀ {ℓ} (A : MetricSpace ℓ)
  (f : ⟨ trivialMetricSpace ⟩ → ⟨ A ⟩ )
  → IsUContMap (snd (trivialMetricSpace)) f (snd A)
isUContFromTrivialMetricSpace A f ε =
  1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ (sym (MA.𝑑-≡→zero _ _ refl)) (snd (ℚ₊→ℝ₊ ε))

 where
 module MA = MetricSpaceStr (snd A)
