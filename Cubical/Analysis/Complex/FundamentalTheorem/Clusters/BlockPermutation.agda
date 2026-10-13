module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.BlockPermutation where

-- A bijection which cannot cross either block restricts to bijections of
-- the blocks. Keeping inverse laws explicit preserves multiplicities.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum using (_⊎_; inl; inr; module ⊎Path; Iso⊎→Iso)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty

private
  select-left : ∀ {A B : Type₀} (x : A ⊎ B) →
    (∀ b → x ≡ inr b → Empty.⊥) → Σ[ a ∈ A ] x ≡ inl a
  select-left (inl a) absent = a , refl
  select-left (inr b) absent = Empty.rec (absent b refl)

module Restrict {A B C D : Type₀} (e : (A ⊎ B) ≃ (C ⊎ D))
  (no-left-right : ∀ a d → equivFun e (inl a) ≡ inr d → Empty.⊥)
  (no-right-left : ∀ b c → equivFun e (inr b) ≡ inl c → Empty.⊥) where

  private
    forward-left : ∀ a → Σ[ c ∈ C ] equivFun e (inl a) ≡ inl c
    forward-left a = select-left (equivFun e (inl a)) (no-left-right a)

    backward-left : ∀ c → Σ[ a ∈ A ] invEq e (inl c) ≡ inl a
    backward-left c = select-left (invEq e (inl c))
      (λ b equal → no-right-left b c (sym (cong (equivFun e) equal) ∙ secEq e (inl c)))

  leftIso : Iso A C
  leftIso .Iso.fun a = fst (forward-left a)
  leftIso .Iso.inv c = fst (backward-left c)
  leftIso .Iso.sec c = ⊎Path.encode _ _
    (sym (snd (forward-left (fst (backward-left c))))
      ∙ cong (equivFun e) (sym (snd (backward-left c))) ∙ secEq e (inl c)) .lower
  leftIso .Iso.ret a = ⊎Path.encode _ _
    (sym (snd (backward-left (fst (forward-left a))))
      ∙ cong (invEq e) (sym (snd (forward-left a))) ∙ retEq e (inl a)) .lower

  rightIso : Iso B D
  rightIso = Iso⊎→Iso leftIso (equivToIso e) (λ a → snd (forward-left a))

  left : A ≃ C
  left = isoToEquiv leftIso

  right : B ≃ D
  right = isoToEquiv rightIso

  left-law : ∀ a → equivFun e (inl a) ≡ inl (equivFun left a)
  left-law a = snd (forward-left a)

  right-law : ∀ b → equivFun e (inr b) ≡ inr (equivFun right b)
  right-law b with equivFun e (inr b) | inspect (equivFun e) (inr b)
  ... | inl c | [ value ]ᵢ = Empty.rec (no-right-left b c value)
  ... | inr d | [ value ]ᵢ = refl
