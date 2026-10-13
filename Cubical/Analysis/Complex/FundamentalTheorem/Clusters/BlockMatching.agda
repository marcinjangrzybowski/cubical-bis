module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.BlockMatching where

-- Once two finite configurations have been split into separated blocks,
-- a sufficiently small matching restricts to a matching of each block.
-- This retains the bijections, rather than merely matching underlying sets.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; module FinSumChar)
open import Cubical.Data.Vec using (Vec; []; _∷_; _++_; lookup)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
import Cubical.Data.Rationals.Order as Q
open PositiveRationals using (ℚ₊; _≤₊_)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Order.Strict.Properties using (≤ℝ→≯)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Distance
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Geometry
import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.BlockPermutation as Block

private
  module C = PremetricStr (snd ℂPremetricSpace)

  atSum : ∀ {m n} → Vec ℂ m → Vec ℂ n → Fin m ⊎ Fin n → ℂ
  atSum xs ys (inl i) = lookup i xs
  atSum xs ys (inr j) = lookup j ys

  lookup-left : ∀ {m n} (xs : Vec ℂ m) (ys : Vec ℂ n) i →
    lookup (FinSumChar.fun m n (inl i)) (xs ++ ys) ≡ lookup i xs
  lookup-left (x ∷ xs) ys zero = refl
  lookup-left (x ∷ xs) ys (suc i) = lookup-left xs ys i

  lookup-right : ∀ {m n} (xs : Vec ℂ m) (ys : Vec ℂ n) j →
    lookup (FinSumChar.fun m n (inr j)) (xs ++ ys) ≡ lookup j ys
  lookup-right [] ys j = refl
  lookup-right (x ∷ xs) ys j = lookup-right xs ys j

  lookup-sum : ∀ {m n} (xs : Vec ℂ m) (ys : Vec ℂ n) u →
    lookup (FinSumChar.fun m n u) (xs ++ ys) ≡ atSum xs ys u
  lookup-sum xs ys (inl i) = lookup-left xs ys i
  lookup-sum xs ys (inr j) = lookup-right xs ys j

opaque
  matching-no-crossing-blocks : ∀ {m n} (xs xs′ : Vec ℂ m) (ys ys′ : Vec ℂ n) ε →
    (∀ i j → lookup i xs ∼ℂ[ ε ] lookup j ys′ → Empty.⊥) →
    (∀ i j → lookup i ys ∼ℂ[ ε ] lookup j xs′ → Empty.⊥) →
    MatchingClose (xs ++ ys) ε (xs′ ++ ys′) →
    MatchingClose xs ε xs′ × MatchingClose ys ε ys′
  matching-no-crossing-blocks {m} {n} xs xs′ ys ys′ ε no-left-right no-right-left =
    PT.rec (isProp× PT.isPropPropTrunc PT.isPropPropTrunc) restrict
    where
    restrict : (Σ[ σ ∈ (Fin (m Cubical.Data.Nat.+ n) ≃ Fin (m Cubical.Data.Nat.+ n)) ]
      (∀ i → lookup i (xs ++ ys) ∼ℂ[ ε ] lookup (equivFun σ i) (xs′ ++ ys′))) →
      MatchingClose xs ε xs′ × MatchingClose ys ε ys′
    restrict (σ , matched) =
      PT.∣ R.left , (λ i → subst (λ u → lookup i xs ∼ℂ[ ε ] atSum xs′ ys′ u)
        (R.left-law i) (sum-close (inl i))) ∣₁ ,
      PT.∣ R.right , (λ j → subst (λ u → lookup j ys ∼ℂ[ ε ] atSum xs′ ys′ u)
        (R.right-law j) (sum-close (inr j))) ∣₁
      where
      finiteSum : (Fin m ⊎ Fin n) ≃ Fin (m Cubical.Data.Nat.+ n)
      finiteSum = FinSumChar.Equiv m n

      e : (Fin m ⊎ Fin n) ≃ (Fin m ⊎ Fin n)
      e = compEquiv finiteSum (compEquiv σ (invEquiv finiteSum))

      sum-close : ∀ u → atSum xs ys u ∼ℂ[ ε ] atSum xs′ ys′ (equivFun e u)
      sum-close u = subst2 (λ z w → z ∼ℂ[ ε ] w) (lookup-sum xs ys u)
        (sym (cong (λ i → lookup i (xs′ ++ ys′)) (secEq finiteSum (equivFun σ (equivFun finiteSum u))))
          ∙ lookup-sum xs′ ys′ (equivFun e u)) (matched (equivFun finiteSum u))

      avoids-left-right : ∀ i j → equivFun e (inl i) ≡ inr j → Empty.⊥
      avoids-left-right i j equal = no-left-right i j
        (subst (λ u → lookup i xs ∼ℂ[ ε ] atSum xs′ ys′ u) equal (sum-close (inl i)))

      avoids-right-left : ∀ i j → equivFun e (inr i) ≡ inl j → Empty.⊥
      avoids-right-left i j equal = no-right-left i j
        (subst (λ u → lookup i ys ∼ℂ[ ε ] atSum xs′ ys′ u) equal (sum-close (inr i)))

      module R = Block.Restrict e avoids-left-right avoids-right-left

matching-separated-blocks-at : ∀ {m n} (xs xs′ : Vec ℂ m) (ys ys′ : Vec ℂ n) gap ε →
  ε ≤₊ (gap /2₊) →
  ConfigurationGap xs ys′ gap → ConfigurationGap ys xs′ gap →
  MatchingClose (xs ++ ys) ε (xs′ ++ ys′) →
  MatchingClose xs ε xs′ × MatchingClose ys ε ys′
matching-separated-blocks-at xs xs′ ys ys′ gap ε below first second =
  matching-no-crossing-blocks xs xs′ ys ys′ ε
    (λ i j close → ≤ℝ→≯ ⟦ gap ⟧₊ (distanceℂ (lookup i xs) (lookup j ys′)) (first i j)
      (closeness→distanceℂ< (lookup i xs) (lookup j ys′) gap
        (C.isMonotone≈≤ (lookup i xs) (lookup j ys′) ε (gap /2₊) below close)))
    (λ i j close → ≤ℝ→≯ ⟦ gap ⟧₊ (distanceℂ (lookup i ys) (lookup j xs′)) (second i j)
      (closeness→distanceℂ< (lookup i ys) (lookup j xs′) gap
        (C.isMonotone≈≤ (lookup i ys) (lookup j xs′) ε (gap /2₊) below close)))

matching-separated-blocks : ∀ {m n} (xs xs′ : Vec ℂ m) (ys ys′ : Vec ℂ n) gap →
  ConfigurationGap xs ys′ gap → ConfigurationGap ys xs′ gap →
  MatchingClose (xs ++ ys) (gap /2₊) (xs′ ++ ys′) →
  MatchingClose xs (gap /2₊) xs′ × MatchingClose ys (gap /2₊) ys′
matching-separated-blocks xs xs′ ys ys′ gap =
  matching-separated-blocks-at xs xs′ ys ys′ gap (gap /2₊) (Q.isRefl≤ (fst (gap /2₊)))
