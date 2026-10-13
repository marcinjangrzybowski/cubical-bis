module Cubical.Analysis.Real.Series.Successor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as Nat
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base

-- Restoring one initial term preserves native Cauchy data. Its global
-- modulus is the supplied tail modulus plus one; no convergence converse
-- or selection of separately truncated tails is used.
partialSum-successor : ∀ terms n →
  partialSum terms (suc n) ≡ terms zero + partialSum (terms ∘ suc) n
partialSum-successor terms zero = addIdL (terms zero) ∙ sym (addIdR (terms zero))
partialSum-successor terms (suc n) = cong (_+ terms (suc n)) (partialSum-successor terms n)
  ∙ sym (addAssoc (terms zero) (partialSum (terms ∘ suc) n) (terms (suc n)))

private
  successorChosenCauchy : ∀ terms → ChosenIsCauchySequence (partialSum (terms ∘ suc)) →
    ChosenIsCauchySequence (partialSum terms)
  successorChosenCauchy terms witness .fst ε = suc (fst witness ε)
  successorChosenCauchy terms witness .snd ε zero n lo hi = Empty.rec (Nat.¬-<-zero lo)
  successorChosenCauchy terms witness .snd ε (suc m) zero lo hi = Empty.rec (Nat.¬-<-zero hi)
  successorChosenCauchy terms witness .snd ε (suc m) (suc n) lo hi =
    subst2 (λ x y → x ∼[ ε ] y)
      (sym (partialSum-successor terms m)) (sym (partialSum-successor terms n))
      (add-pres∼₂ (terms zero) (partialSum (terms ∘ suc) m) (partialSum (terms ∘ suc) n) ε
        (snd witness ε m n (Nat.pred-≤-pred lo) (Nat.pred-≤-pred hi)))

successorSeriesReflectsIsCauchy : ∀ terms → IsCauchySeries (terms ∘ suc) → IsCauchySeries terms
successorSeriesReflectsIsCauchy terms = PT.map (successorChosenCauchy terms)
