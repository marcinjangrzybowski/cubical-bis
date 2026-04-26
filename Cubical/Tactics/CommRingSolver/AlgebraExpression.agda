module Cubical.Tactics.CommRingSolver.AlgebraExpression where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData hiding (punchOut)
open import Cubical.Data.Nat using (ℕ;predℕ)
open import Cubical.Data.Nat.Order using (zero-≤)
open import Cubical.Data.Vec.Base
open import Cubical.Data.Maybe
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra renaming (⟨_⟩ to ⟨_⟩ₐ)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)
open import Cubical.Reflection.Sugar

open import Cubical.Relation.Nullary

open import Cubical.Reflection.Base
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Variables

private
  variable
    ℓ ℓ' : Level

infixl 6 _+'_
infixl 7 -'_
infixl 8 _·'_

-- Expression in an R-Algebra A with n variables
data Expr' {ℓ} (R : Type ℓ) (A : Type ℓ') (n : ℕ) : Type ℓ where
  K : R → Expr' R A n
  ∣ : Fin n → Expr' R A n
  _+'_ : Expr' R A n → Expr' R A n → Expr' R A n
  _·'_ : Expr' R A n → Expr' R A n → Expr' R A n
  -'_ : Expr' R A n → Expr' R A n

Expr : ∀ {ℓ} (R : RawRing ℓ) (A : Type ℓ') (n : ℕ) → Type ℓ
Expr R = Expr' ⟨ R ⟩

module PrettyExpr {ℓ} (R : RawRing ℓ) (A : Type ℓ') (showScalar : ⟨ R ⟩ → TC String) where

 prettyExpr : ∀ {n} → Expr R A n → TC String
 prettyExpr (K x) = showScalar x
 prettyExpr (∣ x) = pure (mkNiceVar (toℕ x))
 prettyExpr (x +' x₁) = do
  x' ← prettyExpr x
  x₁' ← prettyExpr x₁
  pure (x' <> " + " <> x₁')
 prettyExpr (x ·' x₁) = do
  x' ← prettyExpr x
  x₁' ← prettyExpr x₁
  pure ("(" <> x' <> " · " <> x₁' <> ")")
 prettyExpr (-' x) = do
  x' ← prettyExpr x
  pure ("- (" <> x' <> ")")

punchOut : ∀ {ℓ A n} k k' → (𝟚.True (Dec¬ (discreteFin k k'))) →
  Σ[ k* ∈ Fin (predℕ n) ]
  ((xs : Vec {ℓ} A n) → lookup k* (drop' k xs) ≡ lookup k' xs)
punchOut (zero {n}) (suc k') w = k' , λ {(_ ∷ _) → refl }
punchOut (suc {ℕ.suc n} k) zero w = zero , λ {(_ ∷ _) → refl }
punchOut (suc {ℕ.suc n} k) (suc k') w = 
  let (u , v) = punchOut k k' (𝟚.fromWitness (𝟚.toWitness w ∘ cong suc))
  in suc u , λ {(_ ∷ _) → v _ }

tryPunchOut : ∀ {ℓ A n} k k' →
  (k ≡ k') ⊎ (Σ[ k* ∈ Fin (predℕ n) ]
  ((xs : Vec {ℓ} A n) → lookup k* (drop' k xs) ≡ lookup k' xs))
tryPunchOut k k' =
  decRec inl (inr ∘ punchOut k k' ∘ 𝟚.fromWitness) (discreteFin k k')

module Eval (R : RawRing ℓ) (A : RawAlgebra R ℓ') where
  open import Cubical.Data.Vec
  open RawAlgebra A renaming (scalar to scalarₐ)

  ⟦_⟧ : ∀ {n} → Expr R ⟨ A ⟩ₐ n → Vec ⟨ A ⟩ₐ n → ⟨ A ⟩ₐ
  ⟦ K r ⟧ v = scalarₐ r
  ⟦ ∣ k ⟧ v = lookup k v
  ⟦ x +' y ⟧ v = ⟦ x ⟧ v + ⟦ y ⟧ v
  ⟦ x ·' y ⟧ v = ⟦ x ⟧ v · ⟦ y ⟧ v
  ⟦ -' x ⟧ v = - ⟦ x ⟧ v

  FreeOfΣ : ∀ {n} → (e : Expr R ⟨ A ⟩ₐ n) → (k : Fin n) →
   Σ[ X ∈ Type ] (Dec X
     × (X → (∀ xs f → ⟦ e ⟧ xs ≡ ⟦ e ⟧ (update k f xs))) ×
      (X →
        Σ[ e' ∈ Expr R ⟨ A ⟩ₐ (predℕ n) ] (∀ xs → ⟦ e' ⟧ (drop' k xs) ≡ ⟦ e ⟧ xs))) 
  FreeOfΣ {n} (K x) k =
    _ , yes tt , (λ _ _ _ → refl) ,
     λ _ → ((K x) , λ _ → refl)
  FreeOfΣ {n} (∣ k') k =
   _ , Dec¬ (discreteFin k k') ,
     (λ k≠k' → λ xs f → sym (updateThere _ _ _ xs k≠k'))
     , λ y →
        let k* , v = punchOut k k' (𝟚.fromWitness y)
        in ∣ k* , v 
   

  FreeOfΣ {n} (e +' e₁) k =
    let _ , d , u , v = FreeOfΣ {n} e k
        _ , d₁ , u₁ , v₁ = FreeOfΣ {n} e₁ k
    in _ , Dec× d d₁
     , (λ (p , p₁) xs f → cong₂ _+_ (u p xs f) (u₁ p₁ xs f))
     , λ (p , p₁) → (fst (v p) +' fst (v₁ p₁)) ,
       λ xs i → snd (v p) xs i + snd (v₁ p₁) xs i
  FreeOfΣ {n} (e ·' e₁) k =
    let _ , d , u , v = FreeOfΣ {n} e k
        _ , d₁ , u₁ , v₁ = FreeOfΣ {n} e₁ k
    in _ , Dec× d d₁
     , (λ (p , p₁) xs f → cong₂ _·_ (u p xs f) (u₁ p₁ xs f))
     , λ (p , p₁) → (fst (v p) ·' fst (v₁ p₁)) ,
       λ xs i → snd (v p) xs i · snd (v₁ p₁) xs i
  FreeOfΣ {n} (-' e) k =
    let _ , d , u , v = FreeOfΣ {n} e k
    in _ , d
     , (λ p xs f → cong -_ (u p xs f))
     , λ p → ( -' fst (v p) ) ,
       λ xs i → - snd (v p) xs i 

  FreeOf : ∀ {n} → Expr R ⟨ A ⟩ₐ n → Fin n → Type
  FreeOf e k = fst (FreeOfΣ e k)
  
  ⟦⟧-FreeOf : ∀ {n} e k → FreeOf {n} e k → ∀ xs f → ⟦ e ⟧ xs ≡ ⟦ e ⟧ (update k f xs)
  ⟦⟧-FreeOf e k = fst (snd (snd (FreeOfΣ e k)))

  mbFreeOf : ∀ {n} e k → Maybe (FreeOf {n} e k)
  mbFreeOf e k = decToMaybe (fst (snd (FreeOfΣ e k)))
  
  injExpr : ∀ {n} → (x : Expr R ⟨ A ⟩ₐ n)
    → Σ[ x' ∈ Expr R ⟨ A ⟩ₐ (ℕ.suc n) ]
      (∀ xs → ⟦ x' ⟧ xs ≡ ⟦ x ⟧ (drop zero xs))
        × FreeOf x' zero
  injExpr (K x) = K x , (λ _ → refl) , tt
  injExpr (∣ x) =  ∣ (suc x) , (λ { (_ ∷ _) → refl}) , znots
  injExpr (x +' x₁) =
   let (x' , p' , q') = injExpr x
       (x₁' , p₁' , q₁') = injExpr x₁
   in x' +' x₁' , (λ xs → cong₂ _+_ (p' xs) (p₁' xs)) ,
      q' , q₁' --λ xs f → cong₂ _+_ (q' xs f) (q₁' xs f)
  injExpr (x ·' x₁) = 
   let (x' , p' , q') = injExpr x
       (x₁' , p₁' , q₁') = injExpr x₁
   in x' ·' x₁' , (λ xs → cong₂ _·_ (p' xs) (p₁' xs)) ,
      q' , q₁' -- λ xs f → cong₂ _·_ (q' xs f) (q₁' xs f)
  injExpr (-' x) = 
   let (x' , p' , q') = injExpr x
   in -' x' , cong -_ ∘ p' , q' -- λ xs f → cong -_ (q' xs f) 
