{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Order.Quoset.Subset where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.Relation.Binary.Order.Quoset.Base
open import Cubical.Relation.Binary.Order.Quoset.Properties

private
  variable
    ℓ ℓ' ℓ'' : Level


PredicateQuoset : (Q : Quoset ℓ ℓ') → (S : ⟨ Q ⟩ → hProp ℓ'')
  → Quoset (ℓ-max ℓ ℓ'') ℓ'
PredicateQuoset Q S =
  quoset _ _
    (isQuosetInduced
      (QuosetStr.isQuoset (Q .snd)) _
      (EmbeddingΣProp λ x → S x .snd))
