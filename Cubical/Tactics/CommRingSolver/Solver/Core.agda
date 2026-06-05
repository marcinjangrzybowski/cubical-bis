module Cubical.Tactics.CommRingSolver.Solver.Core where

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

import Cubical.Tactics.CommRingSolver.Solver.Helpers as SolverHelpers


module SansReflection (crs : CommRingSolverConfig) where

 open CommRingSolverConfig crs
 open SolverHelpers.SansReflection crs public
 solve :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solve e₁ e₂ xs z =
   ⟦ e₁ ⟧ xs               ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨ (fst (snd (IHR? (normalize e₁) (normalize e₂))) z xs) ⟩
   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
   ⟦ e₂ ⟧ xs ∎

 solveByDec :
   (n : ℕ) (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
   → [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
        ⁇→ (⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs)
 solveByDec _ e₁ e₂ xs = ⁇λ solve e₁ e₂ xs


 IsConstPossiblyNonNull : ∀ {n} → IteratedHornerForms n → Type (ℓ-suc ℓ)
 IsConstPossiblyNonNull (const x) = Unit*
 IsConstPossiblyNonNull 0H = ⊥*
 IsConstPossiblyNonNull (P ·X+ Q) = [ fst (IHR?0 P)  ]ᵗʸ × IsConstPossiblyNonNull Q

 IsConstPossiblyNonNull→ev : ∀ {n} e → IsConstPossiblyNonNull {n} e → Σ[ a ∈ ⟨ R ⟩ ] (∀ xs → eval e xs ≡ scalar` a )
 IsConstPossiblyNonNull→ev (const a) _ = a , λ { [] → refl }
 IsConstPossiblyNonNull→ev (P ·X+ Q) (u , v) =
  let (a , p) = IsConstPossiblyNonNull→ev Q v
  in a , λ { (x ∷ xs) → R`.+IdL' _ _
    (R`.0LeftAnnihilates'  _ _ (fst (snd (IHR?0 P)) u (x ∷ xs)))
     ∙ p xs }

 FreeOfVar : ∀ {n} → IteratedHornerForms n → Fin n → Type (ℓ-suc ℓ)
 FreeOfVar 0H _ = Unit*
 FreeOfVar (P ·X+ Q) zero = [ fst (IHR?0 P)  ]ᵗʸ
 FreeOfVar (P ·X+ Q) (suc k) = FreeOfVar P (suc k) × FreeOfVar Q k

 FreeOfVar→ev : ∀ {n} P k → FreeOfVar {suc n} P k
    → Σ[ P' ∈ IteratedHornerForms n ] (∀ xs → eval P xs ≡ eval P' (Vec.drop k xs) )
 FreeOfVar→ev 0H k _ = 0ₕ , λ xs → sym (Eval0H (Vec.drop k xs))

 FreeOfVar→ev (P ·X+ Q) zero u = Q ,
   λ { (x ∷ xs) → R`.+IdL' _ _ (R`.0LeftAnnihilates' _ _
     ((fst (snd (IHR?0 P)) u (x ∷ xs)))) }
 FreeOfVar→ev {suc n} (P HornerForms.·X+ Q) (suc k) (p , q) =
   let (P' , p') = FreeOfVar→ev P (suc k) p
       (Q' , q') = FreeOfVar→ev Q k q
   in (P' ·X+ Q') , λ { (x ∷ xs) →
     cong₂ _+`_ (cong (_·` x) (p' (x ∷ xs))) (q' xs) }


 substHF : ∀ {n} k (e δ : IteratedHornerForms n) 
   → Σ[ e' ∈ IteratedHornerForms n ]
          (∀ xs → eval e
            (update k (λ _ → (eval δ xs)) xs) ≡ eval e' xs)  
 substHF {suc n} k e δ = 
   let e' , e=' = IHF→Expr e
       δ' , δ=' = IHF→Expr δ
       (ee , ee=) = substE k e' δ'        
   in (normalize ee) , λ xs →
         (e=' _ ∙ cong (λ ys → ⟦ e' ⟧ (update k (λ _ → ys) xs))
            (δ=' xs) )
          ∙∙ ee= xs
          ∙∙ sym (isEqualToNormalform ee xs)


 substHF' : ∀ {n} k (e : IteratedHornerForms n) (δ : IteratedHornerForms (predℕ n))
   
    →  Σ[ e' ∈ IteratedHornerForms (predℕ n) ]
          (∀ xs → eval δ  (drop' k xs) ≡ lookup k xs → eval e' (drop' k xs) ≡ eval e xs)   
 substHF' {suc n} k e δ =
   let e' , e=' = IHF→Expr e
       δ' , δ=' = IHF→Expr δ
       (ee , ee=) = substE' k e' δ'        
   in (normalize ee) , λ xs p →   
           isEqualToNormalform ee (drop' k xs)
          ∙∙ ee= xs (sym (δ=' _) ∙ p)
           ∙∙ sym (e=' xs)
          

 HeadVarOnlyInPow : ∀ {n} → IteratedHornerForms (suc n) → ℕ → Type (ℓ-suc ℓ)
 HeadVarOnlyInPow h zero = FreeOfVar h zero
 HeadVarOnlyInPow 0H (suc k) = ⊥*
 HeadVarOnlyInPow (P HornerForms.·X+ Q) (suc k) =
    HeadVarOnlyInPow P k × [ fst (IHR?0 Q)  ]ᵗʸ

 record Elimination {n : ℕ} {ℓ} {A : ℕ → Type ℓ} {{eiv : EvalInVecR A}}
          (P : A (suc n))
          (iX : Fin (suc n)) (k : ℕ₊₁) : Type (ℓ-max ℓ` ℓ) where

  field
   S Q : A n
   S·xᵏ+Q≡P : ∀ xs →
       (evalInVecR S (drop iX xs) ·` (lookup iX xs ^ ℕ₊₁→ℕ k)) +` evalInVecR Q (drop iX xs)
          ≡ evalInVecR P xs

  

 IsolatedPowerHeadVar : ∀ {n} → IteratedHornerForms (suc n) → ℕ → Type (ℓ-suc ℓ)
 IsolatedPowerHeadVar 0H _ = ⊥*
 IsolatedPowerHeadVar (P ·X+ Q) m = HeadVarOnlyInPow P m

 HeadVarOnlyInPow→ev : ∀ {n} P m → HeadVarOnlyInPow {n} P m →
    Σ[ P' ∈ IteratedHornerForms n ]
      (∀ x xs → eval P' xs ·` x ^ m ≡ eval P (x ∷ xs) )
 HeadVarOnlyInPow→ev P zero v =
   map-snd (λ u x xs → R`.·IdR _ ∙ sym (u (x ∷ xs))) (FreeOfVar→ev _ _ v)
 HeadVarOnlyInPow→ev (P ·X+ Q) (suc m) (u , v) =
   map-snd (λ w x xs →
           (cong₂ _·`_ refl (R`.·Comm _ _)
         ∙∙ R`.·Assoc _ _ _
         ∙∙ cong (_·` x) (w x xs))
      ∙ sym (R`.+IdR' _ _ (fst (snd (IHR?0 Q)) v xs ∙ Eval0H xs)))
     (HeadVarOnlyInPow→ev P m u)



 IsolatedPowerVar : ∀ {n} → IteratedHornerForms n → Fin n → ℕ → Type (ℓ-suc ℓ)
 IsolatedPowerVar {suc n} 0H _ _ = ⊥*
 IsolatedPowerVar {suc n} (P ·X+ Q) zero m =
   HeadVarOnlyInPow P m
 IsolatedPowerVar {suc n} (P ·X+ Q) (suc k) m =
   (IsolatedPowerVar P (suc k) m × IsolatedPowerVar Q k m)
    ⊎ ((IsolatedPowerVar P (suc k) m × FreeOfVar Q k)
    ⊎ (FreeOfVar P (suc k) × IsolatedPowerVar Q k m))

 toElimination : ∀ {n} P → ∀ k m →  IsolatedPowerVar {suc n} P k m
    → Elimination P k (1+ m)
 toElimination {n} (P ·X+ Q) zero m hvm =
   let (S , eqtion) = HeadVarOnlyInPow→ev P m hvm
   in record { S = S
             ; Q = Q
             ; S·xᵏ+Q≡P = λ { (x ∷ xs) →
                    cong₂ _+`_
                      ( cong₂ _·`_ refl (R`.·Comm _ _)
                          ∙∙  R`.·Assoc _ _ _
                          ∙∙ cong (_·` x) (eqtion x xs))
                      refl } }
   
 toElimination {suc n} (P ·X+ R) (suc k) m (inl (p , r)) =
   let module PE = Elimination (toElimination {suc n} P (suc k) m p)
       module RE = Elimination (toElimination {n} R k m r)
       
   in record { S = PE.S ·X+ RE.S ; Q = PE.Q ·X+ RE.Q ;
        S·xᵏ+Q≡P = λ {(x ∷ xs) →
                 cong  (_+` eval (PE.Q ·X+ RE.Q) (x ∷ drop k xs))
                   (R`.·DistL+ _ _ _ ∙
                     cong (_+` (eval RE.S (drop k xs) ·` lookup k xs ^ ℕ₊₁→ℕ (1+ m)))
                      (R`.·CommAssocr _ _ _))
                   
              ∙∙ R`.+ShufflePairs _ _ _ _
                ∙∙ cong₂ _+`_
                 (sym (R`.·DistL+ _ _ _) ∙ cong (_·` x) (PE.S·xᵏ+Q≡P (x ∷ xs)))
                 (RE.S·xᵏ+Q≡P xs) } }
   where open Elimination
 toElimination {suc n} (P ·X+ R) (suc k) m (inr (inl (p , r))) = 
   let module PE = Elimination (toElimination {suc n} P (suc k) m p)
       
       (REQ , REQ=) = FreeOfVar→ev R k r
       RES = 0ₕ

   in record { S = PE.S ·X+ RES ; Q = PE.Q ·X+ REQ ;
        S·xᵏ+Q≡P = λ {(x ∷ xs) →
                 cong  (_+` eval (PE.Q ·X+ REQ) (x ∷ drop k xs))
                   (R`.·DistL+ _ _ _ ∙
                     cong (_+` (eval RES (drop k xs) ·` lookup k xs ^ ℕ₊₁→ℕ (1+ m)))
                      (R`.·CommAssocr _ _ _))
                   
              ∙∙ R`.+ShufflePairs _ _ _ _
                ∙∙ cong₂ _+`_
                 (sym (R`.·DistL+ _ _ _) ∙ cong (_·` x) (PE.S·xᵏ+Q≡P (x ∷ xs)))
                 (R`.+IdL' _ _ (R‵.0LeftAnnihilates' _ _ (Eval0H (drop k xs)))  ∙ sym (REQ= xs))
                 } }
   where open Elimination
 toElimination {suc n} (P ·X+ R) (suc k) m (inr (inr (p , r))) =
   let module RE = Elimination (toElimination {n} R k m r)
       
       (PEQ , PEQ=) = FreeOfVar→ev P (suc k) p
       PES = 0ₕ
   in record { S = PES ·X+ RE.S ; Q = PEQ ·X+ RE.Q ;
        S·xᵏ+Q≡P = λ {(x ∷ xs) →
                 cong  (_+` eval (PEQ ·X+ RE.Q) (x ∷ drop k xs))
                   (R`.·DistL+ _ _ _ ∙
                     cong (_+` (eval RE.S (drop k xs) ·` lookup k xs ^ ℕ₊₁→ℕ (1+ m)))
                      (R`.·CommAssocr _ _ _))
                   
              ∙∙ R`.+ShufflePairs _ _ _ _
                ∙∙ cong₂ _+`_
                 (sym (R`.·DistL+ _ _ _) ∙ cong (_·` x) (
                   R`.+IdL' _ _ (R‵.0LeftAnnihilates _)
                   ∙ sym (PEQ= (x ∷ xs))))
                 (RE.S·xᵏ+Q≡P xs) } }
   where open Elimination

 module Decidable {requireDiscreteScalar : IsJust mbDiscreteScalars}
                  where

  _≟_ : Discrete ⟨ R ⟩
  _≟_ = fromIsJust requireDiscreteScalar

  prettyCoeffTerm : ∀ {n} → (pt : PolynomialTerm n) →
    Σ[ pt' ∈ _ ] ((∀ xs →
     ((evalPolynomialTerm pt xs ≡ evalPolynomialTerm pt' xs)))
     )
  prettyCoeffTerm (b , mbK , mm) =
   let (b' , mbK') , p = w b mbK
   in (b' , mbK' , mm) , (λ xs →
       cong -`[ b ] (fromJust-def-mb·`mb (map-Maybe scalar` mbK) _)
          ∙ sym (-`[ b ]· _ _) ∙∙
         cong₂ _·`_ p refl
         ∙∙ (-`[ b' ]· (Mb.fromJust-def 1r`
               (map-Maybe scalar` mbK')) _
           ∙ cong -`[ b' ]
             (sym (fromJust-def-mb·`mb (map-Maybe scalar` mbK')
               (evalMonomial mm xs)) )))

   where
    w : ∀ (b : Bool) (mbK : Maybe ⟨ R ⟩) →
       Σ[ (b' , mbK') ∈ _ × _ ] ((
        ((-`[ b ] (Mb.fromJust-def 1r`
               (map-Maybe scalar` mbK))
           ≡ -`[ b' ] (Mb.fromJust-def 1r`
                   (map-Maybe scalar` mbK'))))))
    w b nothing = (b , nothing) , refl
    w b (just x) with x ≟ 1r | x ≟ (- 1r) | mbNeg?Scalar <* x
    ... | yes p | _ | _ = (b , nothing) ,
     cong -`[ b ] (cong scalar` p ∙ pres1)
    w false (just x) | _ | yes p | _ = (true , nothing) ,
      (sym (pres- _) ∙∙ cong scalar` (cong -_ p ∙ -Idempotent _ ) ∙∙ pres1 )
    w true (just x) | _ | yes p | _ = (false , nothing) ,
      cong scalar` p ∙∙ pres- _ ∙∙ cong -`_ pres1
    w false (just x) | _ | _ | just (just (-x , p)) = (true , just -x ) ,
       cong (-`_ ∘ scalar`) (sym p) ∙ sym (pres- _) ∙ cong scalar` (-Idempotent _)
    w true (just x) | _ | _ | just (just (-x , p)) = (false , just -x ) ,
      cong scalar` (sym p) ∙ pres- _
    ... | _ | _ | _ = (b , just x) , refl



  prettyCoeff : ∀ {n} → (P : Polynomial n) →
    Σ[ P' ∈ _ ] (∀ xs → evalPolynomial P xs ≡ evalPolynomial P' xs )
  prettyCoeff [] = [] , λ _ → refl
  prettyCoeff (x ∷ P) =
   let P' , p = prettyCoeff P
       x' , q = prettyCoeffTerm x
   in x' ∷ P' , λ xs → evalPolynomial∷ x P xs
      ∙ cong₂ _+`_ (p xs) (q xs) ∙ sym (evalPolynomial∷ x' P' xs)

  commonDenom : ∀ a b → CommonDenom a b
  commonDenom = fromJust-def trivialCD mbCommonDenom

  open CommonMonomial commonDenom
  open PolyUtils




  HF-Maybe-prfₕ : {n : ℕ} (e₁ e₂ : IteratedHornerForms n)
                   → Maybe [ fst (IHR? e₁ e₂) ]ᵗʸ
  HF-Maybe-prfₕ e₁ e₂ =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR? e₁ e₂))))


  HF-Maybe-prf : (n : ℕ) (e₁ e₂ : RExpr n)
                   → Maybe [ fst (IHR? (normalize e₁) (normalize e₂)) ]ᵗʸ
  HF-Maybe-prf _ e₁ e₂ = HF-Maybe-prfₕ (normalize e₁) (normalize e₂)

  mbIsConstPossiblyNonNull : {n : ℕ}
        → (e : IteratedHornerForms n)
        → Maybe (IsConstPossiblyNonNull e)
  mbIsConstPossiblyNonNull (const _) = just _
  mbIsConstPossiblyNonNull 0H = nothing
  mbIsConstPossiblyNonNull (P ·X+ Q) =
    ⦇ (sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P)))))
    , (mbIsConstPossiblyNonNull Q) ⦈

  mbFreeOfVar : ∀ {n} P k → Maybe (FreeOfVar {n} P k)
  mbFreeOfVar 0H k = just _
  mbFreeOfVar (P ·X+ Q) zero =
   sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 P))))
  mbFreeOfVar (P ·X+ Q) (suc k) =
    ⦇ (mbFreeOfVar P (suc k)) , (mbFreeOfVar Q k) ⦈


  mbHeadVarOnlyInPow : {n : ℕ}
        → (P : IteratedHornerForms (suc n))
        → Maybe (Σ _ (HeadVarOnlyInPow P))
  mbHeadVarOnlyInPow 0H = just (0 , _)
  mbHeadVarOnlyInPow P+Q@(P ·X+ Q) =
   Mb.rec (do
      v ← sequenceP (mapOverIdfun (λ _ f → f _≟_) _ (snd (snd (IHR?0 Q))))
      (m , u) ← mbHeadVarOnlyInPow P
      pure (suc m , u , v))
     (just ∘ (0 ,_))
     (mbFreeOfVar P+Q zero)


  mbIsolatedPowerVarHead : ∀ {n} P → Maybe (Σ _ (IsolatedPowerHeadVar {n} P))
  mbIsolatedPowerVarHead {n} 0H = nothing
  mbIsolatedPowerVarHead {n} (P ·X+ P₁) = mbHeadVarOnlyInPow P

  mbIsolatedPowerVar : ∀ {n} P k → Maybe (Σ _ (IsolatedPowerVar {n} P k))
  mbIsolatedPowerVar 0H k = nothing
  mbIsolatedPowerVar (P ·X+ Q) zero = mbHeadVarOnlyInPow P
  mbIsolatedPowerVar (P ·X+ Q) (suc k) = 
    h (mbFreeOfVar P (suc k)) (mbFreeOfVar Q k)
      (mbIsolatedPowerVar P (suc k)) (mbIsolatedPowerVar Q k)
      
    where
     h : Maybe _ → Maybe _ → Maybe _ → Maybe _ → _
     h (just fr) nothing nothing (just (m' , u')) = just (m' , inr (inr (fr , u'))) 
     h nothing (just fr') (just (m , u)) nothing = just (m , inr (inl (u , fr')))
     h nothing nothing (just (m , u)) (just (m' , u')) =
        decRec
         (λ m≡m' →
           just (m , inl (u , subst (IsolatedPowerVar Q k) (sym m≡m') u')))
          (λ _ → nothing)
         (ℕ.discreteℕ m m')
     h _ _ _ _ = nothing


  const·ₕ : ∀ {n} a (e : IteratedHornerForms n) →
           Σ[ e' ∈ IteratedHornerForms n ] (∀ xs → eval e' xs ≡ (scalar` a ·` eval e xs))
  const·ₕ a (const x) = HornerForms.const (a · x) , λ { [] → (pres· _ _)}
  const·ₕ a 0H = 0H , λ _ → sym (R`.0RightAnnihilates _) 
  const·ₕ a (e ·X+ e₁) =
     let e' , e=' = const·ₕ a e
         e₁' , e₁=' = const·ₕ a e₁
     in e' ·X+ e₁' , λ { (x ∷ xs) →
         cong₂ _+`_ (cong (_·` _) (e=' (x ∷ xs)) ∙
           sym (R`.·Assoc _ _ _) ) (e₁=' xs) ∙
            sym (R`.·DistR+ (scalar` a) _ _ ) }
  
  Normalized0ₕ : ∀ n → Normalized (0ₕ {n})
  Normalized0ₕ zero = inl refl
  Normalized0ₕ (suc n) = inl tt*
  
  normalizeIHF'' : ∀ {n} → (e : IteratedHornerForms n) →
    ((e ≑ 0ₕ) ⊎ (Σ[ e' ∈ _ ] ((e ≑ e' ) × NormalizedNonZero e')))
  normalizeIHF''  (const x) =
     decRec (λ x≡0 → inl λ xs i → eval (HornerForms.const (x≡0 i)) xs)
      (λ x≠0 → inr (HornerForms.const x , (λ _ → refl) , x≠0)) (x ≟ 0r)
  normalizeIHF'' 0H = inl λ _ → refl
  normalizeIHF'' e@(e₀ ·X+ e₁) = h (normalizeIHF'' e₀) (normalizeIHF'' e₁)
    where
    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ _) → ((e₁ ≑ 0ₕ) ⊎ Σ _ _) → ((e ≑ 0ₕ) ⊎ Σ _ _)
    h (inl x₀) (inl x₁) = inl λ { (v ∷ vs) →
       cong₂ R`._+_
           (R`.0LeftAnnihilates'  _ _  (x₀ (v ∷ vs)))
           (x₁ vs) ∙ R`.+IdR' _ _ (Eval0H vs) }
    h (inl y₀) (inr (u₁ , y₁ , n₁)) =
       inr ((0H ·X+ u₁) , (λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·` v +` y₁ vs i  })
         , (inl tt* , inr n₁) , tt)
    h (inr (u₀ , y₀ , n₀)) (inl y₁) =
       inr (u₀ ·X+ 0ₕ , (λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·` v +` y₁ vs i })
         , ((inr n₀) , Normalized0ₕ _) , tt)
    h (inr (u₀ , y₀ , n₀)) (inr (u₁ , y₁ , n₁)) = 
       inr (u₀ ·X+ u₁ , (λ { (v ∷ vs) i → y₀ (v ∷ vs) i ·` v +` y₁ vs i }) ,
         ((inr n₀) , inr n₁) , tt)




  normalizeIHFN : ∀ {n} → (e : IteratedHornerForms n) →
   (Σ[ e' ∈ _ ] ((e ≑ e' ) × Normalized e'))
  normalizeIHFN {n} = ⊎.rec (λ a=0 → _ , a=0 , Normalized0ₕ n) (map-snd (map-snd inr)) ∘ normalizeIHF''



  normalizeIHF : ∀ {n} → (e : IteratedHornerForms n) → Σ _ (e ≑_ )
  normalizeIHF = map-snd fst ∘ normalizeIHFN

  
  IHF≑>normalizedIHF : IteratedHornerForms ≑> IteratedHornerForms 
  IHF≑>normalizedIHF ._≑>_.to p = fst (normalizeIHF p)
  IHF≑>normalizedIHF ._≑>_.to≑ p = snd (normalizeIHF p)


  IsConst?Normalized : ∀ n e → Normalized {n} e →
    Maybe (Σ[ c ∈ ⟨ R ⟩ ] ((¬ c ≡ 0r) × ∀ xs → eval e xs ≡ scalar` c ) )
  IsConst?Normalized n (const x₁) (inl x) = nothing
  IsConst?Normalized n (const x₁) (inr x) = just (x₁ , (x , λ {  [] → refl }))
  IsConst?Normalized n 0H x = nothing
  IsConst?Normalized (suc n) (0H ·X+ e₁) (inr ((inl v , x₁) , _)) =
   map-Maybe (map-snd (map-snd (λ { u (x ∷ xs) → R`.+IdL' _ _
    (R`.0LeftAnnihilates _) ∙ u xs})))
    (IsConst?Normalized n e₁ x₁)
  IsConst?Normalized n _ _ = nothing

  IsConst? : ∀ n e → 
    Maybe (Σ[ c ∈ ⟨ R ⟩ ] ((¬ c ≡ 0r) × ∀ xs → eval {n} e xs ≡ scalar` c ) )
  IsConst? n e =
    let (e' , e'= , eN) = normalizeIHFN e 
    in map-Maybe (map-snd (map-snd (e'= _ ∙_ ∘_))) (IsConst?Normalized n e' eN)
    
  eval' : {n : ℕ} (P : IteratedHornerForms n)
         → (xs : Vec ⟨ R` ⟩ n) → Σ ⟨ R` ⟩ (_≡ eval P xs )
  eval' (const x) xs = _ , refl
  eval' 0H xs = _ , refl
  eval' P@(e₀ ·X+ e₁) vvs@(v ∷ vs) =
    h (normalizeIHF'' e₀) (normalizeIHF'' e₁)
   where


    ₕ·` : Σ ⟨ R` ⟩ (_≡ fst (eval' e₀ vvs) ·` v )
    ₕ·` with HF-Maybe-prfₕ e₀ (1ₕ) | HF-Maybe-prfₕ e₀ (-ₕ 1ₕ)
    ... | nothing | nothing = _ , refl
    ... | just x | _ = v , sym (R`.·IdL' _ _
       ((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (1ₕ))) x vvs) ∙∙
        Eval1ₕ vvs))
    ... | _ | just x = -` v , sym (R`.·IdL' _ _
       (cong -`_ (((snd (eval' e₀ vvs)) ∙∙ (fst (snd (IHR? e₀ (-ₕ 1ₕ))) x vvs) ∙∙
          (-EvalDist 1ₕ vvs ∙ cong -`_ (Eval1ₕ vvs))))
        ∙ R`.-Idempotent _))
     ∙ R`.-Dist· _ _




    h : ((e₀ ≑ 0ₕ) ⊎ Σ _ _) → ((e₁ ≑ 0ₕ) ⊎ Σ _ _) → Σ ⟨ R` ⟩ (_≡ eval P vvs )
    h (inl x₀) (inl x₁) =  0r` ,
            sym (R`.0LeftAnnihilates'  _ _  (x₀ vvs))
        ∙ sym (R`.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
    h x₀@(inr _) (inl x₁) =  _ ,
      snd ₕ·` ∙ cong (_·` v) (snd (eval' e₀ vvs))
        ∙ sym (R`.+IdR' _ _ (x₁ vs ∙ Eval0H vs))
    h (inl x₁) (inr _) = _ , snd (eval' e₁ vs) ∙ sym (R`.+IdL' _ _
       (R`.0LeftAnnihilates'  _ _  (x₁ vvs)))
    h (inr x₁) (inr _) = _ , cong₂ _+`_
      (snd ₕ·` ∙ cong (_·` v) (snd (eval' e₀ vvs)))
      (snd (eval' e₁ vs))



  normalizeByDec :
    (n : ℕ) (e : RExpr n) (xs : Vec (fst R`) n)
    →  Σ _ (⟦ e ⟧ xs ≡_)
  normalizeByDec n e xs =
    let (P , =P) = Horner→Poly (fst (normalizeIHF (normalize e)))
        ((Smm , Sp) , P=) =  factorOutMonomial P
        (Sp' , =Sp') = prettyCoeff Sp
        ((Smm* , Sp'*) , (_ , Smm*·Sp'*) ) = simplifyPolyTermTimesPoly n Smm Sp'
    in _ ,
              sym (isEqualToNormalform e xs)
           ∙∙ snd (normalizeIHF (normalize e)) xs
           ∙∙ sym (=P xs)
             ∙∙ P= xs
             ∙∙ cong₂ _·`_ refl (=Sp' xs)
              ∙ sym (Smm*·Sp'* xs)

  tryElimination : ∀ {n : ℕ} (e₁ e₂ : RExpr (suc n)) k →
    Maybe (Σ _ _)
  tryElimination e₁ e₂ k =
     do let (ihf , v) = normalizeIHF (normalize (e₁ +' -' e₂))
        (m , u) ← mbIsolatedPowerVar ihf k
        just (1+ m , toElimination ihf k m u)

  record PreElim {n} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n)) : Type (ℓ-max ℓ ℓ`) where
   field
     Smm : PolynomialTerm n
     Sp : Polynomial n
     Qmm : PolynomialTerm n
     Qp : Polynomial n
     m : ℕ
     ep : evalPolynomialTerm Smm (drop zero xs) ·`
           evalPolynomial Sp (drop zero xs)
          ·` lookup zero xs pow1+ suc m
          ≡
          evalPolynomialTerm Qmm (drop zero xs) ·`
          evalPolynomial Qp (drop zero xs)


   solveForHead' : (Σ ((fst R`) × (fst R`)) λ (lhs , rhs) → lhs ≡ rhs)
   solveForHead' =
         let (_ , (niceS , _)) = simplifyPolyTermTimesPoly _ Smm Sp
             ((Qmm' , Qp') , (_ , niceQ)) = simplifyPolyTermTimesPoly _ Qmm Qp
         in (_
               , niceS _ (drop zero xs) ∙ ep ∙ sym (niceQ (drop zero xs)))


  preElimHead : {n : ℕ} (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n))
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs →
     Maybe (PreElim e₁ e₂ xs)
  preElimHead e₁ e₂ xss@(x ∷ xs) e₁≡e₂ = do
         let (ihf , v) = normalizeIHF (normalize (e₁ +' -' e₂))
         (m , u) ← mbIsolatedPowerVar ihf zero
         let p = toElimination ihf zero m u
             (ihfS , eqS) = normalizeIHF (S p)
             (polyS , polyS=) = Horner→Poly ihfS
             (ihfQ , eqQ) = normalizeIHF (-ₕ (Q p))
             (polyQ , polyQ=) = Horner→Poly ihfQ
             ((Smm , Sp) , SeqCFM) =  factorOutMonomial polyS
             ((Qmm , Qp) , QeqCFM) =  factorOutMonomial polyQ
             p =          cong₂ _+`_ (cong₂ _·`_ (polyS= xs
                         ∙ sym (eqS xs))
                     (pow1+≡^ x (suc m)))
                    (cong -`_ (polyQ= xs ∙
                     sym (eqQ xs) ∙ -EvalDist (Q p) _) ∙
                      R`.-Idempotent _)
                     ∙∙ S·xᵏ+Q≡P p xss  ∙∙
                    sym (v xss) ∙ isEqualToNormalform (e₁ +' -' e₂) xss
                      ∙ R`.+InvR' _ _ e₁≡e₂
         just (record { Smm = Smm ; Sp = Sp ; Qmm = Qmm ; Qp = Qp ; m = m ;
               ep = cong (_·` x pow1+ suc m) (sym (SeqCFM xs))
              ∙∙  (R`.equalByDifference _ _ p)
              ∙∙ QeqCFM xs })
    where open Elimination

  solveForHead : (n : ℕ) (e₁ e₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n))
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs → Maybe (Σ ((fst R`) × (fst R`)) λ (lhs , rhs) → lhs ≡ rhs)
  solveForHead _ e₁ e₂ xs p = map-Maybe PreElim.solveForHead' (preElimHead e₁ e₂ xs p)



  solveByDifference :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
     → fst (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs) ≡ 0r`
     → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solveByDifference e₁ e₂ xs ev=0 =
      R`.equalByDifference _ _ $
         cong₂ _+`_ (sym (isEqualToNormalform e₁ xs))
          (cong -`_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
            snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs ∙
             sym (snd (eval' (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) xs)) ∙ ev=0


  solveByDifference' :  {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R`) n)
     → evalPolynomial (Horner→Poly
      (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . fst) xs
       ≡ 0r` → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
  solveByDifference' e₁ e₂ xs ev=0 =
      R`.equalByDifference _ _ $
         cong₂ _+`_ (sym (isEqualToNormalform e₁ xs))
          (cong -`_ (sym (isEqualToNormalform e₂ xs)) ∙ sym (-EvalDist (normalize e₂) xs))
          ∙ sym (+Homeval (normalize e₁) (-ₕ (normalize e₂)) xs) ∙
              (snd (normalizeIHF (normalize (e₁ +' -' e₂))) xs)
             ∙ sym ((Horner→Poly
              (fst (normalizeIHF (normalize (e₁ +' -' e₂)))) . snd) xs) ∙ ev=0


  module SolveIntegalDomains
             (·`lCancel : ∀ c m n → c ·` m ≡ c ·` n → (c ≡ 0r` → ⊥) → m ≡ n)
             (notZeroRing : 1r` ≡ 0r` → ⊥)
            where

    intDom` = fst R`.·lCancel≃integralDomain ·`lCancel

    fromJust-def≡0 : ∀ x → fromJust-def 1r` x ≡ 0r` → x ≡ just 0r`
    fromJust-def≡0 nothing p = ⊥.rec (notZeroRing p)
    fromJust-def≡0 (just x) = cong just

    PolyTerm≡0-Cases : ∀ {n} mm xs → Σ[ ys ∈ List (Type ℓ`) ]
       ([ ys ]ᵗʸ → (evalMonomial {n} mm xs ≡ just 0r` → ⊥))

    PolyTerm≡0-Cases [] xs = [] , λ _ → ¬nothing≡just
    PolyTerm≡0-Cases (zero ∷ mm) (x ∷ xs) =
       map-snd ((λ {a} x₁ x₂ p  →
                   let z = sym (mb·`mbIdR _)
                              ∙∙ sym (evalMonomial∷ zero mm x xs)
                              ∙∙ p
                    in x₁ x₂ z))
        (PolyTerm≡0-Cases mm xs)
    PolyTerm≡0-Cases (suc m ∷ mm) (x ∷ xs) =
       let ys , u = PolyTerm≡0-Cases mm xs
       in (x ≡ 0r` → ⊥) ∷ ys ,
            λ { (x≢0 ∷ v) p →
               let z =    cong₂ _·`_ (cong (fromJust-def 1r`) (sym (powMaybe-suc x m))) refl ∙ R`.·Comm _ _
                       ∙∙ sym (fromJust-def-mb·`mb (evalMonomial mm xs) (x powMaybe suc m))
                       ∙∙ cong (fromJust-def 1r`) (sym (evalMonomial∷ (suc m) mm x xs) ∙ p)

                   w = intDom` (x ^ (suc m)) (fromJust-def 1r` (evalMonomial mm xs))
                         z
                          (IntegralDomain.x≢0→x^sn≢0 intDom` x m x≢0)
               in u v (fromJust-def≡0 _ w) }

    PolyTerm·Poly≡0-Cases : ∀ {n} mm P xs
     → Maybe (Σ[ ys ∈ List (Type ℓ`) ]
       ((evalPolynomialTerm mm xs ·` evalPolynomial {n} P xs ≡ 0r`) →  [ ys ]ᵗʸ →
         evalPolynomial {n} P xs ≡ 0r`))
    PolyTerm·Poly≡0-Cases mmm@(b , nothing , mm) P xs =
          let u , v = PolyTerm≡0-Cases mm xs
          in just (u , λ p ys → intDom` (evalPolynomialTerm mmm xs) _
               p (v ys ∘S (fromJust-def≡0 _) ∘S _∙ -`[ b ]0 ∘S -`[ b ]-flip≡ _ _))



    PolyTerm·Poly≡0-Cases mmm@(b , just k , mm) P xs =
      decRec (λ _ → nothing)
        (λ ¬k≡0 →
          let u , v = PolyTerm≡0-Cases mm xs
          in Mb.rec
              (just (_ ∷ u , λ p → λ {(y ∷ ys) →
                intDom` (evalPolynomialTerm mmm xs) _
               p (v ys ∘S (fromJust-def≡0 _) ∘S flip (intDom` _ _) (y)
                 ∘S sym (fromJust-def-mb·`mb (just (scalar` k)) (evalMonomial mm xs))
                   ∙∙_∙∙ -`[ b ]0 ∘S  -`[ b ]-flip≡ _ _)}))
              (λ ≢0r→≢0r` →
              just (u , λ p ys → intDom` (evalPolynomialTerm mmm xs) _
               p (v ys ∘S (fromJust-def≡0 _) ∘S flip (intDom` _ _) (≢0r→≢0r` _ ¬k≡0)
                 ∘S sym (fromJust-def-mb·`mb (just (scalar` k)) (evalMonomial mm xs))
                   ∙∙_∙∙ -`[ b ]0 ∘S  -`[ b ]-flip≡ _ _)))
                   mb≢0r→≢0r`) (k ≟ 0r)

  eliminateHead : (n : ℕ) (e₁ e₂ e'₁ e'₂ : RExpr (suc n)) (xs : Vec (fst R`) (suc n))
    → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs → ⟦ e'₁ ⟧ xs ≡ ⟦ e'₂ ⟧ xs →
      String ⊎ (Σ[ (xs , lhs) ∈ List (Type ℓ`) × (fst R`) ] ([ xs ]ᵗʸ → lhs ≡ 0r`))
  eliminateHead _ e₁ e₂ e'₁ e'₂ xxs@(x ∷ xs) e₁≡e₂ e'₁≡e'₂ = do
    pe ← maybeToSum "unable to elim from first eq" (preElimHead e₁ e₂ xxs e₁≡e₂)
    pe' ← maybeToSum "unable to elim from snd eq" (preElimHead e'₁ e'₂ xxs e'₁≡e'₂)
    let (peSmm* , pe'Smm* , c) , peSmm*·c≡peSmm , pe'Smm*·c≡pe'Smm
             = commonDenomPolynomialTerm _ (pe .Smm) (pe' .Smm)
    maybeToSum "unimplemented - solved var extractend with different powers"
      (decToMaybe (ℕ.discreteℕ (pe .m) (pe' .m)) >>=
      λ m≡m' →  do
         let pe'Sp·peQp = Polynomial· (pe' .Sp) (pe .Qp)
             peSp·pe'Qp = Polynomial· (pe .Sp) (pe' .Qp)
             polyLHS = (L.map (PolynomialTerm· (PolynomialTerm· pe'Smm* (pe .Qmm)))
                    (fst pe'Sp·peQp))
             polyRHS = (L.map (PolynomialTerm· (PolynomialTerm· peSmm* (pe' .Qmm)))
                      (fst peSp·pe'Qp))
             polyDiff = Polynomial+ polyLHS (polynomialNeg polyRHS)
             ((Smm , Sp) , SeqCFM) =  factorOutMonomial (fst polyDiff)
             pp : evalPolynomial polyLHS xs
                    ≡
                    evalPolynomial polyRHS xs
             pp = sym (evalPolynomialTermTimesPolynomial
                    (PolynomialTerm· pe'Smm* (pe .Qmm)) (fst pe'Sp·peQp) xs)
                ∙ cong₂ (_·`_) (PolynomialTerm·-sound pe'Smm* (pe .Qmm) xs)
                  (snd pe'Sp·peQp xs)
                 ∙∙ R`.·CommAssocSwap _ _ _ _
                 ∙∙ (cong₂ (_·`_) (R`.·Comm _ _) (sym (pe .ep) ∙
                  cong₂ _·`_ (cong₂ _·`_ (peSmm*·c≡peSmm xs) refl) refl)
                ∙∙ R`.·Assoc _ _ _ ∙∙
                  cong₂ _·`_ ( (sym (R`.·Assoc _ _ _)
                     ∙ cong₂ _·`_ refl
                        (   cong₂ _·`_ refl
                          (sym (R`.·Assoc _ _ _) ∙∙ R`.·Comm _ _ ∙∙ sym (R`.·Assoc _ _ _))
                         ∙∙ R`.·Assoc _ _ _
                         ∙∙ R`.·Comm _ _))
                    ∙∙ R`.·Comm _ _
                    ∙∙ sym (R`.·Assoc _ _ _))
                    (cong ((x pow1+_) ∘ suc) m≡m')
                  ∙∙ sym (R`.·Assoc _ _ _)
                ∙∙ cong₂ (_·`_) (R`.·Comm _ _)
                  (cong₂ _·`_ (cong₂ _·`_ (sym (pe'Smm*·c≡pe'Smm xs)) refl) refl
                 ∙ pe' .ep )) ∙∙ R`.·CommAssocSwap _ _ _ _
                  ∙∙ cong₂ (_·`_) (sym (PolynomialTerm·-sound peSmm* (pe' .Qmm) xs))
                  (sym (snd peSp·pe'Qp xs))
                  ∙ (evalPolynomialTermTimesPolynomial
                    (PolynomialTerm· peSmm* (pe' .Qmm)) (fst peSp·pe'Qp) xs)
             pp' =
                   sym (SeqCFM xs)
                ∙  snd polyDiff xs
                ∙∙ cong₂ _+`_ refl (sym (evalPolynomialNeg polyRHS xs))
                ∙∙ R`.differenceByEqual _ _ pp
         zzz ← pure {A = ℕ} 3

         (do pt-cases ← (λ (a , y) → ((a , evalPolynomial Sp xs) , y pp')) <$>_
                  <$> ((PolyTerm·Poly≡0-Cases <$> mb·`lCancel <*> mbNotZeroRing) <*'
                                _ <* Smm <* Sp <* xs)

             pt-cases) <|> pure (([] , _) , λ _ → pp'))


   where
    open PreElim
    open SolveIntegalDomains




