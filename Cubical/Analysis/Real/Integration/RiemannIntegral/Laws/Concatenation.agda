module Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Concatenation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Concatenation
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


concatenatedPartitionsHaveVanishingMesh : ∀ {a b c}
  (first : ℕ → TaggedPartition[ a , b ])
  (second : ℕ → TaggedPartition[ b , c ]) →
  HasVanishingMesh first → HasVanishingMesh second →
  HasVanishingMesh (λ n → concatenateTaggedPartitions (first n) (second n))
concatenatedPartitionsHaveVanishingMesh first second fineFirst fineSecond δ =
  PT.map2 (λ { (K , left) (L , right) →
    ℕ.max K L , λ n max≤n → concatenateMeshBelow (first n) (second n) δ
      (left n (ℕ.≤-trans (ℕ.left-≤-max {m = K} {n = L}) max≤n))
      (right n (ℕ.≤-trans (ℕ.right-≤-max {n = L} {m = K}) max≤n)) })
    (fineFirst δ) (fineSecond δ)


-- Any three existing integrals on adjacent ordered intervals obey interval
-- additivity.  Synchronizing two fixed dyadic sequences needs no choice of
-- fine partitions or sequence of moduli.
opaque
  riemannIntegral-concatenate : ∀ f a b c → a ≤ℝ b → b ≤ℝ c →
    ∀ left right whole →
    HasRiemannIntegralOn f a b left →
    HasRiemannIntegralOn f b c right →
    HasRiemannIntegralOn f a c whole →
    whole ≡ left + right
  riemannIntegral-concatenate f a b c a≤b b≤c left right whole
      hasLeft hasRight hasWhole =
    cong fst (isPropSequenceLimit sums
      (whole , riemannSumsConverge f whole partitions fine hasWhole)
      ((left + right) , subst (λ s → isLimitSequence s (left + right))
        (sym (funExt (λ n → riemannSum-concatenate (p n) (q n) f)))
        (addPresIsLimitSequence
          (riemannSumsConverge f left p p-fine hasLeft)
          (riemannSumsConverge f right q q-fine hasRight))))
    where
    p : ℕ → TaggedPartition[ a , b ]
    p = dyadicLeftTaggedPartition a b a≤b
    q : ℕ → TaggedPartition[ b , c ]
    q = dyadicLeftTaggedPartition b c b≤c
    p-fine : HasVanishingMesh p
    p-fine = dyadicLeftTaggedPartitionsHaveVanishingMesh a b a≤b
    q-fine : HasVanishingMesh q
    q-fine = dyadicLeftTaggedPartitionsHaveVanishingMesh b c b≤c
    partitions : ℕ → TaggedPartition[ a , c ]
    partitions = λ n → concatenateTaggedPartitions (p n) (q n)
    sums : ℕ → ℝ
    sums = λ n → riemannSum (partitions n) f
    fine : HasVanishingMesh partitions
    fine = concatenatedPartitionsHaveVanishingMesh p q p-fine q-fine

  riemannIntegral-difference : ∀ f a b c → a ≤ℝ b → b ≤ℝ c →
    (left : IsRiemannIntegrableOn f a b)
    (right : IsRiemannIntegrableOn f b c)
    (whole : IsRiemannIntegrableOn f a c) →
    fst whole - fst left ≡ fst right
  riemannIntegral-difference f a b c a≤b b≤c left right whole =
    cong (_- fst left)
      (riemannIntegral-concatenate f a b c a≤b b≤c
        (fst left) (fst right) (fst whole) (snd left) (snd right) (snd whole))
    ∙ cong (_- fst left) (addComm (fst left) (fst right))
    ∙ sym (addAssoc (fst right) (fst left) (- fst left))
    ∙ cong (fst right +_) (subSelf (fst left))
    ∙ addIdR (fst right)
