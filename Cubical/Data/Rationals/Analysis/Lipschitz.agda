module Cubical.Data.Rationals.Analysis.Lipschitz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sum as ⊎

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties
open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)

IsLipschitzWithOn : ℚ₊ → ℙ ℚ → (ℚ → ℚ) → Type
IsLipschitzWithOn L P f =
  ∀ q → q ∈ P → ∀ r → r ∈ P → (ε : ℚ₊) →
    abs (q ℚ.- r) ℚ.< fst ε →
    abs (f q ℚ.- f r) ℚ.< fst (L ·₊ ε)

IsLipschitzWithOnOrdered : ℚ₊ → ℙ ℚ → (ℚ → ℚ) → Type
IsLipschitzWithOnOrdered L P f =
  ∀ q → q ∈ P → ∀ r → r ∈ P → r ℚ.< q →
    abs (f q ℚ.- f r) ℚ.≤ fst L ℚ.· (q ℚ.- r)

isLipschitzWithOnOrdered→isLipschitzWithOn :
  ∀ L P f → IsLipschitzWithOnOrdered L P f → IsLipschitzWithOn L P f
isLipschitzWithOnOrdered→isLipschitzWithOn L P f isLip q q∈ r r∈ ε q-r<ε
  with ℚ.Dichotomyℚ q r
... | inr r<q =
  ℚ.isTrans≤< _ _ _
    (isLip q q∈ r r∈ r<q)
    (ℚ.<-o· _ _ (fst L) (snd L)
      (subst (ℚ._< fst ε)
        (0<→abs≡id (q ℚ.- r) (ℚ.-< r q r<q))
        q-r<ε))
... | inl q≤r with ℚ.≤→≡⊎< q r q≤r
... | inl q≡r =
  subst (λ z → abs (f z ℚ.- f r) ℚ.< fst (L ·₊ ε)) (sym q≡r)
    (subst (ℚ._< fst (L ·₊ ε))
      (cong abs (sym (ℚ.+InvR (f r))))
      (snd (L ·₊ ε)))
... | inr q<r =
  subst (ℚ._< fst (L ·₊ ε))
    (sym (abs-Comm (f q) (f r)))
    (ℚ.isTrans≤< _ _ _
      (isLip r r∈ q q∈ q<r)
      (ℚ.<-o· _ _ (fst L) (snd L)
        (subst (ℚ._< fst ε)
          (0<→abs≡id (r ℚ.- q) (ℚ.-< q r q<r))
          (subst (ℚ._< fst ε) (abs-Comm q r) q-r<ε))))

-- Compatibility names for the former Cauchy-real bisection API.
Lipschitz-ℚ→ℚℙ : ℚ₊ → ℙ ℚ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚℙ = IsLipschitzWithOn

Lipschitz-ℚ→ℚℙ< : ℚ₊ → ℙ ℚ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚℙ< = IsLipschitzWithOnOrdered

Lipschitz-ℚ→ℚℙ<→Lipschitz-ℚ→ℚℙ :
  ∀ L P f → Lipschitz-ℚ→ℚℙ< L P f → Lipschitz-ℚ→ℚℙ L P f
Lipschitz-ℚ→ℚℙ<→Lipschitz-ℚ→ℚℙ =
  isLipschitzWithOnOrdered→isLipschitzWithOn
