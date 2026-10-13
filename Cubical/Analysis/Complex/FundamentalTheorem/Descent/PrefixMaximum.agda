module Cubical.Analysis.Complex.FundamentalTheorem.Descent.PrefixMaximum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (lookup; FinVec→Vec; FinVec→Vec→FinVec)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Finite

prefixInclude : ∀ {n} (bound : Fin n) → Fin (ℕ.suc (Fin.toℕ bound)) → Fin n
prefixInclude {n} bound i = Fin.fromℕ' n (Fin.toℕ i)
  (ℕ.≤<-trans (ℕ.pred-≤-pred (Fin.toℕ<n i)) (Fin.toℕ<n bound))

prefixInclude-index : ∀ {n} (bound : Fin n) i → Fin.toℕ (prefixInclude bound i) ≡ Fin.toℕ i
prefixInclude-index {n} bound i = Fin.toFromId' n (Fin.toℕ i) _

prefixInclude-bounded : ∀ {n} (bound : Fin n) i → Fin.toℕ (prefixInclude bound i) ℕ.≤ Fin.toℕ bound
prefixInclude-bounded bound i = subst (ℕ._≤ Fin.toℕ bound) (sym (prefixInclude-index bound i))
  (ℕ.pred-≤-pred (Fin.toℕ<n i))

private
  restrict : ∀ {n} (bound i : Fin n) → Fin.toℕ i ℕ.≤ Fin.toℕ bound → Fin (ℕ.suc (Fin.toℕ bound))
  restrict bound i bounded = Fin.fromℕ' _ (Fin.toℕ i) (ℕ.suc-≤-suc bounded)

  include-restrict : ∀ {n} (bound i : Fin n) bounded → prefixInclude bound (restrict bound i bounded) ≡ i
  include-restrict bound i bounded = Fin.inj-toℕ
    (prefixInclude-index bound (restrict bound i bounded)
      ∙ Fin.toFromId' _ (Fin.toℕ i) (ℕ.suc-≤-suc bounded))

-- The witness is confined to a supplied finite prefix, so successive
-- near-maximizers can be chosen with nonincreasing indices.
prefixApproximateMaximum : ∀ {n} (values : Fin n → ℝ) (bound : Fin n) (ε : ℚ₊) →
  ∥ Σ[ i ∈ Fin n ] (Fin.toℕ i ℕ.≤ Fin.toℕ bound) ×
    (∀ j → Fin.toℕ j ℕ.≤ Fin.toℕ bound → values j <ℝ values i + rat (fst ε)) ∥₁
prefixApproximateMaximum values bound ε = PT.map fromPrefix
  (finiteApproximateMaximum (FinVec→Vec prefixValues) ε)
  where
  prefixValues : Fin (ℕ.suc (Fin.toℕ bound)) → ℝ
  prefixValues i = values (prefixInclude bound i)

  lookup-value : ∀ i → lookup i (FinVec→Vec prefixValues) ≡ prefixValues i
  lookup-value i = funExt⁻ (FinVec→Vec→FinVec prefixValues) i

  fromPrefix : _ → _
  fromPrefix (i , maximal) = prefixInclude bound i , prefixInclude-bounded bound i , λ j bounded →
    subst2 _<ℝ_
      (lookup-value (restrict bound j bounded) ∙ cong values (include-restrict bound j bounded))
      (cong (_+ rat (fst ε)) (lookup-value i)) (maximal (restrict bound j bounded))
