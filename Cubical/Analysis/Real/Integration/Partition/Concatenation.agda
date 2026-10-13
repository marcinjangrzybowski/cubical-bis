module Cubical.Analysis.Real.Integration.Partition.Concatenation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; FinVec; _++Fin_)
import Cubical.Data.FinData as FD

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra


private
  joinNodes : ∀ {n m} → FinVec ℝ (suc n) → FinVec ℝ (suc m) →
    FinVec ℝ (suc (n ℕ.+ m))
  joinNodes {zero} p q = q
  joinNodes {suc n} p q FD.zero = p FD.zero
  joinNodes {suc n} p q (FD.suc i) = joinNodes (p ∘ FD.suc) q i

  joinFirst : ∀ {n m} (p : FinVec ℝ (suc n)) (q : FinVec ℝ (suc m)) →
    p (FD.fromℕ n) ≡ q FD.zero → joinNodes p q FD.zero ≡ p FD.zero
  joinFirst {zero} p q joined = sym joined
  joinFirst {suc n} p q joined = refl

  joinLast : ∀ {n m} (p : FinVec ℝ (suc n)) (q : FinVec ℝ (suc m)) →
    joinNodes p q (FD.fromℕ (n ℕ.+ m)) ≡ q (FD.fromℕ m)
  joinLast {zero} p q = refl
  joinLast {suc n} p q = joinLast (p ∘ FD.suc) q

  joinLefts : ∀ {n m} (p : FinVec ℝ (suc n)) (q : FinVec ℝ (suc m)) i →
    joinNodes p q (FD.weakenFin i) ≡
    ((p ∘ FD.weakenFin) ++Fin (q ∘ FD.weakenFin)) i
  joinLefts {zero} p q i = refl
  joinLefts {suc n} p q FD.zero = refl
  joinLefts {suc n} p q (FD.suc i) = joinLefts (p ∘ FD.suc) q i

  joinRights : ∀ {n m} (p : FinVec ℝ (suc n)) (q : FinVec ℝ (suc m)) →
    p (FD.fromℕ n) ≡ q FD.zero → ∀ i →
    joinNodes p q (FD.suc i) ≡ ((p ∘ FD.suc) ++Fin (q ∘ FD.suc)) i
  joinRights {zero} p q joined i = refl
  joinRights {suc n} p q joined FD.zero = joinFirst (p ∘ FD.suc) q joined
  joinRights {suc n} p q joined (FD.suc i) =
    joinRights (p ∘ FD.suc) q joined i

  appendRelation : ∀ {ℓ n m} (R : ℝ → ℝ → Type ℓ)
    (p p' : FinVec ℝ n) (q q' : FinVec ℝ m) →
    (∀ i → R (p i) (p' i)) → (∀ i → R (q i) (q' i)) →
    ∀ i → R ((p ++Fin q) i) ((p' ++Fin q') i)
  appendRelation {n = zero} R p p' q q' first second i = second i
  appendRelation {n = suc n} R p p' q q' first second FD.zero = first FD.zero
  appendRelation {n = suc n} R p p' q q' first second (FD.suc i) =
    appendRelation R (p ∘ FD.suc) (p' ∘ FD.suc) q q'
      (first ∘ FD.suc) second i

  appendTernary : ∀ {n m} (g : ℝ → ℝ → ℝ → ℝ)
    (p₁ p₂ p₃ : FinVec ℝ n) (q₁ q₂ q₃ : FinVec ℝ m) i →
    g ((p₁ ++Fin q₁) i) ((p₂ ++Fin q₂) i) ((p₃ ++Fin q₃) i) ≡
    ((λ j → g (p₁ j) (p₂ j) (p₃ j)) ++Fin
      (λ j → g (q₁ j) (q₂ j) (q₃ j))) i
  appendTernary {zero} g p₁ p₂ p₃ q₁ q₂ q₃ i = refl
  appendTernary {suc n} g p₁ p₂ p₃ q₁ q₂ q₃ FD.zero = refl
  appendTernary {suc n} g p₁ p₂ p₃ q₁ q₂ q₃ (FD.suc i) =
    appendTernary g (p₁ ∘ FD.suc) (p₂ ∘ FD.suc) (p₃ ∘ FD.suc) q₁ q₂ q₃ i


module _ {a b c : ℝ} (first : TaggedPartition[ a , b ])
    (second : TaggedPartition[ b , c ]) where
  private
    module P = Partition (TaggedPartition.partition first)
    module Q = Partition (TaggedPartition.partition second)
    module T = TaggedPartition first
    module U = TaggedPartition second

    joined : P.points (FD.fromℕ P.intervalCount) ≡ Q.points FD.zero
    joined = P.rightEndpoint ∙ sym Q.leftEndpoint

    nodes = joinNodes P.points Q.points
    samples = T.tags ++Fin U.tags

    monotone : ∀ i → nodes (FD.weakenFin i) ≤ℝ nodes (FD.suc i)
    monotone i =
      subst2 _≤ℝ_
        (sym (joinLefts P.points Q.points i))
        (sym (joinRights P.points Q.points joined i))
        (appendRelation _≤ℝ_
          (P.points ∘ FD.weakenFin) (P.points ∘ FD.suc)
          (Q.points ∘ FD.weakenFin) (Q.points ∘ FD.suc)
          P.monotone Q.monotone i)

    tagLower : ∀ i → nodes (FD.weakenFin i) ≤ℝ samples i
    tagLower i =
      subst (_≤ℝ samples i) (sym (joinLefts P.points Q.points i))
        (appendRelation _≤ℝ_ (P.points ∘ FD.weakenFin) T.tags
          (Q.points ∘ FD.weakenFin) U.tags T.lower≤tag U.lower≤tag i)

    tagUpper : ∀ i → samples i ≤ℝ nodes (FD.suc i)
    tagUpper i =
      subst (samples i ≤ℝ_) (sym (joinRights P.points Q.points joined i))
        (appendRelation _≤ℝ_ T.tags (P.points ∘ FD.suc)
          U.tags (Q.points ∘ FD.suc) T.tag≤upper U.tag≤upper i)

  concatenateTaggedPartitions : TaggedPartition[ a , c ]
  concatenateTaggedPartitions =
    ( (P.intervalCount ℕ.+ Q.intervalCount)
    , nodes
    , (joinFirst P.points Q.points joined ∙ P.leftEndpoint)
    , (joinLast P.points Q.points ∙ Q.rightEndpoint)
    , monotone )
    , samples , tagLower , tagUpper

  concatenateMeshBelow : ∀ δ →
    HasMeshBelow T.partition δ → HasMeshBelow U.partition δ →
    HasMeshBelow (TaggedPartition.partition concatenateTaggedPartitions) δ
  concatenateMeshBelow δ fineFirst fineSecond i =
    subst2 (λ l r → r - l <ℝ rat (fst δ))
      (sym (joinLefts P.points Q.points i))
      (sym (joinRights P.points Q.points joined i))
      (appendRelation (λ l r → r - l <ℝ rat (fst δ))
        (P.points ∘ FD.weakenFin) (P.points ∘ FD.suc)
        (Q.points ∘ FD.weakenFin) (Q.points ∘ FD.suc)
        fineFirst fineSecond i)

  riemannSum-concatenate : ∀ f →
    riemannSum concatenateTaggedPartitions f ≡
    riemannSum first f + riemannSum second f
  riemannSum-concatenate f =
    finiteSumExt (λ i →
      cong₂ (λ l r → (r - l) · f (samples i))
        (joinLefts P.points Q.points i) (joinRights P.points Q.points joined i)
      ∙ appendTernary (λ l r t → (r - l) · f t)
          (P.points ∘ FD.weakenFin) (P.points ∘ FD.suc) T.tags
          (Q.points ∘ FD.weakenFin) (Q.points ∘ FD.suc) U.tags i)
    ∙ finiteSumAppend
        (λ i → width T.partition i · f (T.tags i))
        (λ i → width U.partition i · f (U.tags i))
