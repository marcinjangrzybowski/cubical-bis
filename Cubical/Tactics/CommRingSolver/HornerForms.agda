module Cubical.Tactics.CommRingSolver.HornerForms where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ;predℕ)
open import Cubical.Data.FinData hiding (punchOut)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as 𝟚

open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Tactics.CommRingSolver.Utility

open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ₐ)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression public



private
  variable
    ℓ ℓ' : Level

{-
  This defines the type of multivariate Polynomials over the RawRing R.
  The construction is based on the algebraic fact

    R[X₀][X₁]⋯[Xₙ] ≅ R[X₀,⋯,Xₙ]

  BUT: Contrary to algebraic convetions, we will give 'Xₙ' the lowest index
  in the definition of 'Variable' below. So if 'Variable n R k' is identified
  with 'Xₖ', then the RawRing we construct should rather be denoted with

    R[Xₙ][Xₙ₋₁]⋯[X₀]

  or, to be precise about the evaluation order:

    (⋯((R[Xₙ])[Xₙ₋₁])⋯)[X₀]

-}


module HornerForms (R@(⟨R⟩ , _) : CommRing ℓ)
                         -- (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R')
                         where
 open CommRingStr (snd R)
 RRng : RawRing ℓ
 RRng = rawring ⟨R⟩ 0r 1r _+_ _·_ (-_)
 open RingTheory (CommRing→Ring R)
 module R‵ where
   open CommRingStr (snd R') public
   open RingTheory (CommRing→Ring R') public

 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)

 RAlg : RawAlgebra RRng ℓ'
 RAlg = rawalgebra ⟨R'⟩ scalar‵ 0r‵ 1r‵ (_+‵_) (_·‵_) (-‵_)



 open Eval RRng RAlg public


 substE : ∀ {n} k (e δ : Expr RRng  ⟨R'⟩ n) 
    →  Σ[ e' ∈ Expr RRng ⟨R'⟩ n ]
          (∀ xs → ⟦ e ⟧ (update k (λ _ → (⟦ δ ⟧ xs)) xs) ≡ ⟦ e' ⟧ xs)   
 substE k (K x₁) δ = (K x₁) , (λ _ → refl)
 substE k (∣ k') δ = decRec (λ k≡k' → δ , λ xs →
         let xs' = (update k (λ x → ((⟦ δ ⟧ xs))) xs)
         in cong (λ k → lookup k' (update k (λ x → ⟦ δ ⟧ xs) xs)) (k≡k')
             ∙ updateHere k' _ xs  )
   (λ k≠k' → ∣ k' , λ xs → updateThere _ _ _ xs k≠k')
    (discreteFin k k')
 substE k (e +' e₁) δ =
  let (e' , p) = substE k e δ
      (e₁' , p₁) = substE k e₁ δ
  in e' +' e₁' , λ xs → cong₂ _+‵_ (p xs) (p₁ xs) 
 substE k (e ·' e₁) δ =
  let (e' , p) = substE k e δ
      (e₁' , p₁) = substE k e₁ δ
  in e' ·' e₁' , λ xs → cong₂ _·‵_ (p xs) (p₁ xs)
 substE k (-' e) δ =
  let (e' , p) = substE k e δ
  in -' e' , λ xs → cong -‵_ (p xs)


 substE' : ∀ {n} k (e : Expr RRng  ⟨R'⟩ n) (δ : Expr RRng  ⟨R'⟩ (predℕ n))
   
    →  Σ[ e' ∈ Expr RRng ⟨R'⟩ (predℕ n) ]
          (∀ xs → ⟦ δ ⟧ (drop' k xs) ≡ lookup k xs → ⟦ e' ⟧ (drop' k xs) ≡ ⟦ e ⟧ xs)   
 substE' k (K x₁) δ = (K x₁) , λ _ _ → refl
 substE' {ℕ.suc n} k (∣ k') δ = 
   decRec (λ k≡k' → δ , λ xs u →
             u ∙ ((cong lookup k≡k') ≡$ xs))
         (λ k≠k' →
          let k* , v = punchOut k k' (𝟚.fromWitness k≠k')
          in ∣ k* , λ xs _ → v xs )

    (discreteFin k k')


 substE' k (e +' e₁) δ  =
  let (e' , p) = substE' k e δ
      (e₁' , p₁) = substE' k e₁ δ
  in e' +' e₁' , λ xs u → cong₂ _+‵_ (p xs u) (p₁ xs u) 
 substE' k (e ·' e₁) δ =
  let (e' , p) = substE' k e δ
      (e₁' , p₁) = substE' k e₁ δ
  in e' ·' e₁' , λ xs u → cong₂ _·‵_ (p xs u) (p₁ xs u)
 substE' k (-' e) δ =
  let (e' , p) = substE' k e δ
  in -' e' , λ xs u → cong -‵_ (p xs u)


 data IteratedHornerForms : ℕ → Type ℓ where
   const : ⟨R⟩ → IteratedHornerForms ℕ.zero
   0H : {n : ℕ} → IteratedHornerForms (ℕ.suc n)
   _·X+_ : {n : ℕ} → IteratedHornerForms (ℕ.suc n) → IteratedHornerForms n
                   → IteratedHornerForms (ℕ.suc n)



 module IteratedHornerOperations where


  private
    1H' : (n : ℕ) → IteratedHornerForms n
    1H' ℕ.zero = const 1r
    1H' (ℕ.suc n) = 0H ·X+ 1H' n

    0H' : (n : ℕ) → IteratedHornerForms n
    0H' ℕ.zero = const 0r
    0H' (ℕ.suc n) = 0H

  1ₕ : {n : ℕ} → IteratedHornerForms n
  1ₕ {n = n} = 1H' n

  0ₕ : {n : ℕ} → IteratedHornerForms n
  0ₕ {n = n} = 0H' n

  X : (n : ℕ) (k : Fin n) → IteratedHornerForms n
  X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
  X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

  _+ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
               → IteratedHornerForms n
  (const r) +ₕ (const s) = const (r + s)
  0H +ₕ Q = Q
  (P ·X+ r) +ₕ 0H = P ·X+ r
  (P ·X+ r) +ₕ (Q ·X+ s) =
    let left = (P +ₕ Q)
        right = (r +ₕ s)
    in left ·X+ right

  -ₕ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
  -ₕ (const x) = const (- x)
  -ₕ 0H = 0H
  -ₕ (P ·X+ Q) = (-ₕ P) ·X+ (-ₕ Q)

  _⋆_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms (ℕ.suc n)
                → IteratedHornerForms (ℕ.suc n)
  _·ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
                → IteratedHornerForms n
  r ⋆ 0H = 0H
  r ⋆ (P ·X+ Q) =  (r ⋆ P) ·X+ (r ·ₕ Q)

  const x ·ₕ const y = const (x · y)
  0H ·ₕ Q = 0H
  (P ·X+ Q) ·ₕ S =
     let
        z = (P ·ₕ S)
     in (z ·X+ 0ₕ) +ₕ (Q ⋆ S)

  asRawRing : (n : ℕ) → RawRing ℓ
  RawRing.Carrier (asRawRing n) = IteratedHornerForms n
  RawRing.0r (asRawRing n) = 0ₕ
  RawRing.1r (asRawRing n) = 1ₕ
  RawRing._+_ (asRawRing n) = _+ₕ_
  RawRing._·_ (asRawRing n) = _·ₕ_
  RawRing.- (asRawRing n) =  -ₕ

 Variable : (n : ℕ) (k : Fin n) → IteratedHornerForms n
 Variable n k = IteratedHornerOperations.X n k

 Constant : (n : ℕ) (r : ⟨R⟩) → IteratedHornerForms n
 Constant ℕ.zero r = const r
 Constant (ℕ.suc n) r = IteratedHornerOperations.0ₕ ·X+ Constant n r
