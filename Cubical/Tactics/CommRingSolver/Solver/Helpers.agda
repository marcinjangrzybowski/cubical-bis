module Cubical.Tactics.CommRingSolver.Solver.Helpers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ;suc;zero;predℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ using (zero-≤)
open import Cubical.Data.Vec as Vec
open import Cubical.Data.Sigma
import Cubical.Data.Prod as ×
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.NatPlusOne
open import Cubical.Data.List as L hiding (drop)
open import Cubical.Data.List.Dependent
open import Cubical.Data.Bool as 𝟚 hiding (_≟_)
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary

open import Cubical.Reflection.Sugar


open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.RawAlgebra hiding (⟨_⟩)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.RawRing hiding (⟨_⟩)
open import Cubical.Tactics.CommRingSolver.EvalHom
open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Algebra.Ring.BigOps

open import Agda.Builtin.String

import Cubical.Tactics.CommRingSolver.Polynomial.Core as PolyEval




module SansReflection (crs : CommRingSolverConfig) where

 open CommRingSolverConfig crs

 open PolyEval.SansReflection crs public

 RExpr : (n : ℕ) → Type _
 RExpr = Expr RRng ⟨ R` ⟩


 instance
  EvalInVecRAlgebraExpr : EvalInVecR RExpr
  EvalInVecRAlgebraExpr .EvalInVecR.evalInVecR = ⟦_⟧



 normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
 normalize {n = n} (K r) = Constant n r
 normalize {n = n} (∣ k) = Variable n k
 normalize (x +' y) =
   (normalize x) +ₕ (normalize y)
 normalize (x ·' y) =
   (normalize x) ·ₕ (normalize y)
 normalize (-' x) =  -ₕ (normalize x)

 evalConstant : ∀ n r xs → eval (Constant n r) xs ≡ scalar` r
 evalConstant zero r [] = refl
 evalConstant (suc n) r (x ∷ xs) =
   R`.+IdL' _ _ (R`.0LeftAnnihilates _)
      ∙ evalConstant n r xs

 isEqualToNormalform :
      {n : ℕ} (e : RExpr n) (xs : Vec (fst R`) n)
    → eval (normalize e) xs ≡ ⟦ e ⟧ xs


 isEqualToNormalform {n = n} (K r) xs = evalConstant n r xs

 isEqualToNormalform (∣ zero) (x ∷ xs) =
   eval 1ₕ (x ∷ xs) ·` x +` eval 0ₕ xs   ≡⟨ cong (λ u → u ·` x +` eval 0ₕ xs)
                                             (Eval1ₕ (x ∷ xs)) ⟩
   1r` ·` x +` eval 0ₕ xs                 ≡⟨ cong (λ u → 1r`  ·` x +` u ) (Eval0H xs) ⟩
   1r` ·` x +` 0r`                        ≡⟨ R`.+IdR _ ⟩
   1r` ·` x                             ≡⟨ R`.·IdL _ ⟩
   x ∎
 isEqualToNormalform {n = suc n} (∣ (suc k)) (x ∷ xs) =
     eval 0ₕ (x ∷ xs) ·` x +` eval (Variable n k) xs ≡⟨ cong (λ u → u ·` x +` eval (Variable n k) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r` ·` x +` eval (Variable n k) xs              ≡⟨ cong (λ u → u +` eval (Variable n k) xs)
                                                             (R`.0LeftAnnihilates _) ⟩
     0r` +` eval (Variable n k) xs                  ≡⟨ R`.+IdL _ ⟩
     eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
     ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

 isEqualToNormalform (-' e) [] =
   eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
   -` eval (normalize e) []    ≡⟨ cong -`_ (isEqualToNormalform e [] ) ⟩
   -` ⟦ e ⟧ [] ∎
 isEqualToNormalform (-' e) (x ∷ xs) =
   eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
   -` eval (normalize e) (x ∷ xs)    ≡⟨ cong -`_ (isEqualToNormalform e (x ∷ xs) ) ⟩
   -` ⟦ e ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e +' e₁) [] =
       eval (normalize e +ₕ normalize e₁) []
     ≡⟨ +Homeval (normalize e) _ [] ⟩
       eval (normalize e) []
       +` eval (normalize e₁) []
     ≡⟨ cong (λ u → u +` eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ []
       +` eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] +` u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] +` ⟦ e₁ ⟧ [] ∎
 isEqualToNormalform (e +' e₁) (x ∷ xs) =
       eval (normalize e +ₕ normalize e₁) (x ∷ xs)
     ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) +` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u +` eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +` u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +` ⟦ e₁ ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e ·' e₁) [] =
       eval (normalize e ·ₕ normalize e₁) []
     ≡⟨ ·Homeval (normalize e) _ [] ⟩
       eval (normalize e) [] ·` eval (normalize e₁) []
     ≡⟨ cong (λ u → u ·` eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ [] ·` eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] ·` u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] ·` ⟦ e₁ ⟧ [] ∎

 isEqualToNormalform (e ·' e₁) (x ∷ xs) =
       eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
     ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) ·` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u ·` eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·` eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·` u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·` ⟦ e₁ ⟧ (x ∷ xs) ∎

 Expr≑>IHF : RExpr ≑> IteratedHornerForms 
 Expr≑>IHF ._≑>_.to = normalize
 Expr≑>IHF ._≑>_.to≑ p xs = sym (isEqualToNormalform p xs)


 IHF→Expr : {n : ℕ} → (x : IteratedHornerForms n) →
   Σ (RExpr n) (x ≑'_)
 IHF→Expr (const x) = K x , evalConstant _ _
 IHF→Expr 0H = (K 0r) , λ _ → sym pres0
 IHF→Expr (x ·X+ x₁) =
  let x  , p  = IHF→Expr x
      x₁ , p₁ = IHF→Expr x₁
      y , q , u = injExpr x₁
  in (x ·' ∣ zero) +' y , λ {(u ∷ us) →
           cong₂ _+`_ (cong (_·` u) (p (u ∷ us)))
        (p₁ us ∙ sym (q (u ∷ us)))}
      
  
 IHF≑>Expr : IteratedHornerForms ≑> RExpr 
 IHF≑>Expr ._≑>_.to = fst ∘ IHF→Expr
 IHF≑>Expr ._≑>_.to≑ = snd ∘ IHF→Expr

 [_]ᵗʸ : ∀ {ℓ} → List (Type ℓ) → Type (ℓ-suc ℓ)
 [_]ᵗʸ = ListP (idfun _)

 ×[_]ᵗʸ : ∀ {ℓ} → List (Type ℓ) → Type ℓ
 ×[_]ᵗʸ = RepListP (idfun _)


 [X]? : ∀ {ℓ'} → Type ℓ'  → Type (ℓ-max (ℓ-suc ℓ) ℓ')
 [X]? A = (Σ (List (Type ℓ)) (λ XS → (([ XS ]ᵗʸ → A) ×
               (ListP (λ X → Discrete ⟨ R ⟩ → Maybe X) XS))))

 ×-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → [X]? A → [X]? A' → [X]? (A × A')
 ×-[X]? (XS , f , d) (XS' , f' , d') =
   XS L.++ XS' , (map-× f f') ∘S splitP {xs = XS} {XS'} , (d ++P d')

 map-[X]? : ∀ {ℓ'} → {A A' : Type ℓ'} → (A → A')
           → [X]? A → [X]? A'
 map-[X]? f = map-snd (map-fst (f ∘S_))

 is0H : ∀ {n} → IteratedHornerForms n → Type ℓ
 is0H  (const x) = x ≡ 0r
 is0H  HornerForms.0H = Unit*
 is0H  _ = ⊥*
 NormalizedNonZero : ∀ {n} → IteratedHornerForms n → Type ℓ
 Normalized : ∀ {n} → IteratedHornerForms n → Type ℓ
 Normalized ihf = is0H ihf ⊎ NormalizedNonZero ihf

 NonBothZero : ∀ {n} → (P : IteratedHornerForms (suc n)) (Q : IteratedHornerForms n) →
   Normalized P × Normalized Q → Type
 NonBothZero P Q (inl _ , inl _) = ⊥
 NonBothZero P Q _ = Unit
 NormalizedNonZero (const x) = ¬ (x ≡ 0r)
 NormalizedNonZero 0H = ⊥*
 NormalizedNonZero (P ·X+ Q) =
  Σ (Normalized P × Normalized Q) (NonBothZero P Q)
 IHR?0 : ∀ {n} → ∀ (e : IteratedHornerForms n) →
           [X]?  (e ≑ 0ₕ)
 IHR?0 (const x) =
    ([ x ≡ 0r ]) , (λ { (p ∷ []) [] → cong scalar` p} )
    , ((λ _≟_ → decRec just (λ _ → nothing) (x ≟ 0r)) ∷ [])
 IHR?0 0H = [] , (λ _ xs → Eval0H xs) , []
 IHR?0 (e ·X+ e₁) =
   map-[X]?
     (λ (f , f') → λ {(v ∷ vs) →
      cong₂ R`._+_
           (R`.0LeftAnnihilates'  _ _  (f (v ∷ vs)))
           (f' vs) ∙ R`.+IdR' _ _ (Eval0H vs) })
     (×-[X]? (IHR?0 e) (IHR?0 e₁))


 IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) →
     [X]? (e₁ ≑ e₂)
 IHR? (const x) (const x') = [ x ≡ x' ] , (( λ { (p ∷ []) [] → cong scalar` p }) ,
   (λ _≟_ → decToMaybe (x ≟ x')) ∷ [])
 IHR? 0H e = map-[X]?
  (λ f → λ { (v ∷ vs) → sym   (f (v ∷ vs)) }) (IHR?0 e)
 IHR? e 0H =
    map-[X]?
  (λ f → λ { (v ∷ vs) → (f (v ∷ vs)) }) (IHR?0 e)
 IHR? (e ·X+ e₁) (e' ·X+ e₁') =
  map-[X]?
    ((λ (f , f') → λ {(v ∷ vs) →
       cong₂ R`._+_ (cong (_·` v)  (f (v ∷ vs))) (f' vs)}))
    (×-[X]? (IHR? e e') (IHR? e₁ e₁'))





 IHR?-refl : ∀ {n} → ∀ (e : IteratedHornerForms n) → [ fst (IHR? e e) ]ᵗʸ
 IHR?-refl (const x) = refl ∷ []
 IHR?-refl 0H = []
 IHR?-refl (e ·X+ e₁) = IHR?-refl e ++P IHR?-refl e₁
