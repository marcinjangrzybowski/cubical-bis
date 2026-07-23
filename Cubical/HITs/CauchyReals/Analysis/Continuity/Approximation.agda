module Cubical.HITs.CauchyReals.Analysis.Continuity.Approximation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using
  (∼-monotone≤)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base using
  (IsUContinuousℙ)


-- Previous location: Continuity.Base.
ℚApproxℙ : (P : ℙ ℝ) (Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ P Q f =
  Σ[ f' ∈ (∀ q → rat q ∈ P → ℚ₊ → ℚ) ]
    ((∀ q q∈ ε → rat (f' q q∈ ε) ∈ Q) ×
      (Σ[ f'-cauchy ∈ (∀ q q∈P → _) ]
        (∀ q q∈P →
          lim (rat ∘ f' q q∈P) (f'-cauchy q q∈P) ≡
          fst (f (rat q) q∈P))))


-- Previous location: Continuity.Base.
ℚApprox : (f : ℝ → ℝ) → Type
ℚApprox f =
  Σ[ f' ∈ (ℚ → ℚ₊ → ℚ) ]
    Σ[ f'-cauchy ∈ (∀ q → _) ]
      (∀ q → lim (rat ∘ f' q) (f'-cauchy q) ≡ f (rat q))


-- Previous location: Continuity.Base.
ℚApproxℙ'Num : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) →
  ∀ q → (q∈P : rat q ∈ P) → Type
ℚApproxℙ'Num P Q f q q∈P =
  Σ[ f' ∈ (ℚ₊ → ℚ) ]
    ((∀ ε → rat (f' ε) ∈ Q) ×
      (Σ[ f'-cauchy ∈ _ ]
        (lim (rat ∘ f') f'-cauchy ≡ fst (f (rat q) q∈P))))


-- Previous location: Continuity.Base.
ℚApproxℙ' : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ' P Q f =
  ∀ q → (q∈P : rat q ∈ P) → ℚApproxℙ'Num P Q f q q∈P


-- Previous location: Continuity.Base.
Iso-ℚApproxℙ'-ℚApproxℙ : (P Q : ℙ ℝ) → ∀ f →
  Iso (ℚApproxℙ' P Q f) (ℚApproxℙ P Q f)
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.fun x =
  (λ q → fst ∘ x q) ,
  (λ q → fst ∘ snd ∘ x q) ,
  (λ q → fst ∘ snd ∘ snd ∘ x q) ,
  (λ q → snd ∘ snd ∘ snd ∘ x q)
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.inv = _
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.sec _ = refl
Iso-ℚApproxℙ'-ℚApproxℙ P Q f .Iso.ret _ = refl


-- Previous location: Continuity.Base.
ℚApproxℙ'≃ℚApproxℙ : (P Q : ℙ ℝ) → ∀ f →
  ℚApproxℙ' P Q f ≃ ℚApproxℙ P Q f
ℚApproxℙ'≃ℚApproxℙ P Q f =
  isoToEquiv (Iso-ℚApproxℙ'-ℚApproxℙ P Q f)


-- Previous location: Continuity.Base.
ℚApproxℙ'' : (P Q : ℙ ℝ) (f : ∀ x → x ∈ P → Σ ℝ (_∈ Q)) → Type
ℚApproxℙ'' P Q f =
  ∀ x → (x∈P : rat x ∈ P) (ε : ℚ₊) →
    Σ[ r ∈ ℚ ] ((rat r ∈ Q) × (rat r ∼[ ε ] fst (f (rat x) x∈P)))


-- Previous location: Continuity.Base.
ℚApproxℙ'→ℚApproxℙ'' : (P Q : ℙ ℝ) → ∀ f →
  ℚApproxℙ' P Q f → ℚApproxℙ'' P Q f
ℚApproxℙ'→ℚApproxℙ'' P Q f X x x∈P ε =
  fst (X x x∈P) (ε /2₊) ,
  fst (snd (X x x∈P)) (ε /2₊) ,
  subst (rat (fst (X x x∈P) (ε /2₊)) ∼[ ε ]_)
    (snd (snd (snd (X x x∈P))))
    (rat-lim _ _ _ (ε /2₊) _ <≤ℚ! (refl∼ _ _))


-- Previous location: Continuity.Base.
ℚApproxℙ∘ : ∀ P Q R g f
  → IsUContinuousℙ Q ((fst ∘_) ∘ g)
  → ℚApproxℙ'' Q R g
  → ℚApproxℙ'' P Q f
  → ℚApproxℙ'' P R (curry (uncurry g ∘ uncurry f))
ℚApproxℙ∘ P Q R g f gC gA fA q q∈ ε =
  let
    δ' , Δ = gC (ε /2₊)
    δ = min₊ δ' (ε /2₊)

    uu' : rat (fst (fA q q∈ δ)) ∈ Q
    uu' = fst (snd (fA q q∈ δ))

    zz : rat (fst (gA (fst (fA q q∈ δ)) uu' δ))
      ∼[ ε /2₊ +₊ ε /2₊ ]
      fst (g (fst (f (rat q) q∈)) (snd (f (rat q) q∈)))
    zz = triangle∼
      (∼-monotone≤ (ℚ.min≤' (gC (ε /2₊) .fst .fst) _)
        (snd (snd (gA (fst (fA q q∈ δ)) uu' δ))))
      (Δ _ _ uu' _
        (∼-monotone≤ (ℚ.min≤ _ _) (snd (snd (fA q q∈ δ)))))
  in
  fst (gA (fst (fA q q∈ δ)) uu' δ) ,
  fst (snd (gA (fst (fA q q∈ δ)) uu' δ)) ,
  subst∼ ℚ!! zz
