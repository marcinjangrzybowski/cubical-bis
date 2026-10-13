module Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteIndices where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; doubleℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Vec using (Vec; []; _∷_; head)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Empty as ⊥

twiceIndexBound : ℕ → ℕ
twiceIndexBound = doubleℕ

NonIncreasingIndices : ∀ {n} → Vec ℕ n → Type₀
NonIncreasingIndices [] = Unit
NonIncreasingIndices (a ∷ []) = Unit
NonIncreasingIndices (a ∷ b ∷ tail) = (b ≤ a) × NonIncreasingIndices (b ∷ tail)

-- A certificate points to three adjacent entries, retaining their actual
-- equalities. Its input is a finite vector, not a selected infinite path.
data EqualIndexTriple : ∀ {n} → Vec ℕ n → Type₀ where
  here : ∀ {n a b c} {tail : Vec ℕ n} → a ≡ b → b ≡ c →
    EqualIndexTriple (a ∷ b ∷ c ∷ tail)
  later : ∀ {n a} {tail : Vec ℕ n} → EqualIndexTriple tail → EqualIndexTriple (a ∷ tail)

tripleOffset : ∀ {n} {values : Vec ℕ n} → EqualIndexTriple values → ℕ
tripleOffset (here _ _) = zero
tripleOffset (later triple) = suc (tripleOffset triple)

tripleOffset-bounded : ∀ {n} {values : Vec ℕ n} (triple : EqualIndexTriple values) →
  suc (suc (suc (tripleOffset triple))) ≤ n
tripleOffset-bounded (here _ _) = suc-≤-suc (suc-≤-suc (suc-≤-suc zero-≤))
tripleOffset-bounded (later triple) = suc-≤-suc (tripleOffset-bounded triple)

private
  tripleOrDrop : ∀ a b c → b ≤ a → c ≤ b → ((a ≡ b) × (b ≡ c)) ⊎ (c < a)
  tripleOrDrop a b c ba cb with ≤-split ba
  ... | inl less = inr (≤<-trans cb less)
  ... | inr equal with ≤-split cb
  ... | inl less = inr (<≤-trans less ba)
  ... | inr equal′ = inl (sym equal , sym equal′)

finiteEqualIndexTriple : (bound : ℕ)
  (values : Vec ℕ (suc (suc (suc (twiceIndexBound bound))))) →
  head values ≤ bound → NonIncreasingIndices values → EqualIndexTriple values
finiteEqualIndexTriple zero (a ∷ b ∷ c ∷ []) bounded (ba , cb , tt)
  with tripleOrDrop a b c ba cb
... | inl (ab , bc) = here ab bc
... | inr dropped = ⊥.rec (¬-<-zero (<≤-trans dropped bounded))
finiteEqualIndexTriple (suc bound) (a ∷ b ∷ c ∷ d ∷ e ∷ tail) bounded (ba , cb , rest)
  with tripleOrDrop a b c ba cb
... | inl (ab , bc) = here ab bc
... | inr dropped = later (later
  (finiteEqualIndexTriple bound (c ∷ d ∷ e ∷ tail)
    (pred-≤-pred (<≤-trans dropped bounded)) rest))
