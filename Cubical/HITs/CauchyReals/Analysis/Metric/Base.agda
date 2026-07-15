module Cubical.HITs.CauchyReals.Analysis.Metric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Embedding

open import Cubical.Data.Nat as ℕ hiding (_·_;_+_;_choose_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; _/2₊ ; min₊)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Algebra.CommRing.BinomialThm

record IsMetric {ℓ} (A : Type ℓ) (𝑑[_,_] : A → A → ℝ) : Type ℓ where

  constructor ismetric

  field
   is-set : isSet A
   𝑑-nonNeg : ∀ x y → 0 ≤ᵣ 𝑑[ x , y ]
   𝑑-sym : ∀ x y → 𝑑[ x , y ] ≡ 𝑑[ y , x ]
   𝑑-pos : ∀ x y → (0 <ᵣ 𝑑[ x , y ]) → x ≡ y → ⊥
   𝑑-zero→≡ : ∀ x y → 0 ≡ 𝑑[ x , y ] → x ≡ y
   𝑑-≡→zero : ∀ x y → x ≡ y → 0 ≡ 𝑑[ x , y ]
   𝑑-triangle : ∀ x y z → 𝑑[ x , z ] ≤ᵣ 𝑑[ x , y ] +ᵣ 𝑑[ y , z ]

  𝑑₊[_,_] : A → A → ℝ₀₊
  𝑑₊[ a , a' ] = _ , 𝑑-nonNeg a a'


record MetricSpaceStr {ℓ} (A : Type ℓ) : Type ℓ where

  constructor metricSpaceStr

  field
   𝑑[_,_] : A → A → ℝ
   isMetric : IsMetric A 𝑑[_,_]

  open IsMetric isMetric public

MetricSpace : ∀ ℓ → Type (ℓ-suc ℓ)
MetricSpace ℓ = TypeWithStr ℓ MetricSpaceStr

MetricSpace₀ = MetricSpace ℓ-zero

ℝMetricSpace : MetricSpace₀
ℝMetricSpace .fst = ℝ
ℝMetricSpace .snd .MetricSpaceStr.𝑑[_,_] x y = absᵣ (x -ᵣ y)
ℝMetricSpace .snd .MetricSpaceStr.isMetric = w
 where
  w : IsMetric _ λ x y → absᵣ (x -ᵣ y)
  w .IsMetric.is-set = isSetℝ
  w .IsMetric.𝑑-nonNeg _ _ = 0≤absᵣ _
  w .IsMetric.𝑑-sym = minusComm-absᵣ
  w .IsMetric.𝑑-pos _ _ 0<d x=y =
    ≤ᵣ→≯ᵣ (absᵣ _) 0
     (≡ᵣWeaken≤ᵣ _ _ (cong absᵣ (Rℝ.+InvR' _ _ x=y) ∙ absᵣ0)) 0<d
  w .IsMetric.𝑑-zero→≡ _ _ 0=d =
    Rℝ.equalByDifference _ _ (absᵣx=0→x=0 _ (sym 0=d))
  w .IsMetric.𝑑-≡→zero _ _ 0=d =
    sym absᵣ0 ∙ cong absᵣ (sym (Rℝ.+InvR' _ _ 0=d))
  w .IsMetric.𝑑-triangle = absᵣ-triangle-midpt

MetricSubSpaceStr : ∀ {ℓ} (A : Type ℓ) → (P : ℙ A)
  → MetricSpaceStr A
  → MetricSpaceStr (Σ A (_∈ P))
MetricSubSpaceStr A P msp = w
 where
 module M = MetricSpaceStr msp
 open IsMetric

 ww : IsMetric _ _
 ww .is-set = isSetΣ M.is-set (isProp→isSet ∘ ∈-isProp P)
 ww .𝑑-nonNeg _ _ = M.𝑑-nonNeg _ _
 ww .𝑑-sym _ _ = M.𝑑-sym _ _
 ww .𝑑-pos _ _ 0<d = M.𝑑-pos _ _ 0<d ∘ cong fst
 ww .𝑑-zero→≡ _ _ 0=d = Σ≡Prop (∈-isProp P) (M.𝑑-zero→≡ _ _ 0=d)
 ww .𝑑-≡→zero _ _ = M.𝑑-≡→zero _ _ ∘ cong fst
 ww .𝑑-triangle _ _ _ = M.𝑑-triangle _ _ _


 w : MetricSpaceStr (Σ A (_∈ P))
 w .MetricSpaceStr.𝑑[_,_] (x , _) (y , _) = M.𝑑[ x , y ]
 w .MetricSpaceStr.isMetric = ww

MetricSubSpace : ∀ {ℓ}
  → (A : MetricSpace ℓ) → (P : ℙ ⟨ A ⟩)
  → MetricSpace ℓ
MetricSubSpace A P = Σ ⟨ A ⟩ (_∈ P) , MetricSubSpaceStr _ P (snd A)

IsUContMap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
         (AM : MetricSpaceStr A) (f : A → B) (BM : MetricSpaceStr B)
         → Type ℓ
IsUContMap AM f BM =
 ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
   ∀ x y → AM.𝑑[ x , y ] <ᵣ rat (fst δ)
         → BM.𝑑[ f x , f y ] <ᵣ rat (fst ε)
 where
    module AM = MetricSpaceStr AM
    module BM = MetricSpaceStr BM

IsIsometry : ∀ {ℓ} {A : Type ℓ}
         (AM : MetricSpaceStr A) (f : A → A)
         → Type ℓ
IsIsometry AM f = ∀ x y → AM.𝑑[ x , y ] ≡ AM.𝑑[ f x , f y ]
 where
    module AM = MetricSpaceStr AM


IsIsometry→IsEmbedding : ∀ {ℓ} {A : Type ℓ}
         (AM : MetricSpaceStr A) (f : A → A)
         → IsIsometry AM f → isEmbedding f
IsIsometry→IsEmbedding AM f isIsom =
  injEmbedding AM.is-set
      (λ {x} {y} p →
         AM.𝑑-zero→≡ _ _ (AM.𝑑-≡→zero (f x) (f y) p ∙ sym (isIsom x y)))

 where
    module AM = MetricSpaceStr AM


UContMap : ∀ {ℓ ℓ'} → MetricSpace ℓ → MetricSpace ℓ' → Type (ℓ-max ℓ ℓ')
UContMap (_ , A) (_ , B) = Σ _ λ f → ∥ IsUContMap A f B ∥₁



subsSpaceInjUContMap : ∀ {ℓ}
  → (A : MetricSpace ℓ) (P : ℙ ⟨ A ⟩)
  → UContMap (MetricSubSpace A P) A
subsSpaceInjUContMap A P = fst ,
  ∣ (λ ε →  ε , λ _ _ <ε → <ε) ∣₁

uContMapConst : ∀ {ℓ ℓ'} →
  (A : MetricSpace ℓ) → (B : MetricSpace ℓ')
   → ⟨ B ⟩ → UContMap A B
uContMapConst A B b .fst _ = b
uContMapConst A B b .snd =
  ∣ (λ ε → 1 , λ _ _ _ → isTrans≡<ᵣ _ _ _ (sym (BM.𝑑-≡→zero b b refl))
   (snd (ℚ₊→ℝ₊ ε))) ∣₁

  where
    module BM = MetricSpaceStr (snd B)


isUContMap∘ : ∀ {ℓ ℓ' ℓ''}
 {A : MetricSpace ℓ} {B : MetricSpace ℓ'} {C : MetricSpace ℓ''}
         → ∀ f g
           → IsUContMap (snd B) f (snd C)
           → IsUContMap (snd A) g  (snd B)
           → IsUContMap (snd A) (f ∘ g) (snd C)
isUContMap∘ f g fucm gucm ε =
  let (δ , δ∼) = fucm ε
  in map-snd (λ X → λ _ _  → δ∼ _ _ ∘ X _ _) (gucm δ)


restrUContMap : ∀ {ℓ ℓ'} {A : MetricSpace ℓ} {B : MetricSpace ℓ'} (P : ℙ ⟨ A ⟩) (Q : ℙ ⟨ B ⟩) →
     (f : UContMap A B) →
     (f∈ : ∀ x → x ∈ P → fst f x ∈ Q)
    → UContMap (MetricSubSpace A P) (MetricSubSpace B Q)
restrUContMap P Q f f∈ .fst (x , x∈) = fst f x , f∈ x x∈
restrUContMap P Q f f∈ .snd = PT.map (λ X ε → map-snd (λ {δ} Y _ _ → Y _ _  ) (X ε)) (snd f)

UContMap∘ : ∀ {ℓ ℓ' ℓ''} {A : MetricSpace ℓ} {B : MetricSpace ℓ'} {C : MetricSpace ℓ''}
     → UContMap B C → UContMap A B → UContMap A C
UContMap∘ {A = A} {B} {C} (f , fucm) (g , gucm) =
 f ∘ g , PT.map2 (isUContMap∘ {A = A} {B} {C} f g) fucm gucm


IsUContinuous→UContMap :
         ∀ f → ∥ IsUContinuous f ∥₁
         → UContMap ℝMetricSpace ℝMetricSpace

IsUContinuous→UContMap f fUC =
  f , PT.map (λ X ε → map-snd (λ {δ} Y _ _ → fst (∼≃abs<ε _ _ _) ∘ Y _ _ ∘ invEq (∼≃abs<ε _ _ _)) (X ε)) fUC

UnitIntervalMetricSpace : MetricSpace₀
UnitIntervalMetricSpace = MetricSubSpace ℝMetricSpace (intervalℙ 0 1)

reversalMap : UContMap UnitIntervalMetricSpace UnitIntervalMetricSpace
reversalMap = restrUContMap {A = ℝMetricSpace} {ℝMetricSpace}
  (intervalℙ 0 1) (intervalℙ 0 1) (IsUContinuous→UContMap (λ x → 1 -ᵣ x)
    ∣ reversalUC ∣₁)
  λ x (0<x , x<1) → isTrans≡≤ᵣ _ _ _ (sym (+-ᵣ 1) ∙ x-ᵣy≡x+ᵣ[-ᵣy] _ _)  (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ _ _ x<1))
       , (isTrans≤≡ᵣ _ _ _
      (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ _ _ 0<x))
      ( sym (x-ᵣy≡x+ᵣ[-ᵣy] _ _) ∙ -ᵣ-rat₂ _ _))
 where
  reversalUC : IsUContinuous (λ x → 1 -ᵣ x)
  reversalUC ε = ε , λ u v u∼v →
    invEq (∼≃abs<ε _ _ _)
      (isTrans≡<ᵣ _ _ _
        (cong absᵣ ℝ! ∙ sym (minusComm-absᵣ u v))
        (fst (∼≃abs<ε _ _ _) u∼v))

Interval[_,_]MetricSpace : ℝ → ℝ → MetricSpace₀
Interval[ a , b ]MetricSpace = MetricSubSpace ℝMetricSpace (intervalℙ a b)
