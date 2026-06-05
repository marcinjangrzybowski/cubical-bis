module Cubical.Tactics.CommRingSolver.Polynomial.Core where

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

module PrettyPoly {ℓ} (⟨R⟩ : Type ℓ) where

 Monomial : ℕ → Type
 Monomial n = Vec ℕ n

 PolynomialTerm : ℕ → Type ℓ
 PolynomialTerm n = Bool × (Maybe ⟨R⟩) × Monomial n

 Polynomial : ℕ → Type ℓ
 Polynomial n = List (PolynomialTerm n)


module SansReflection (crs : CommRingSolverConfig) where

 open CommRingSolverConfig crs

 open HomomorphismProperties R  R` (snd commAlg) public


 maybeEq : ∀ x y → Maybe (x ≡ y)
 maybeEq x y = mbDiscreteScalars <* x <* y >>= decToMaybe

 module PolyEval where

  open PrettyPoly ⟨ R ⟩ public

  infix 9 _pow1+_
 
  _pow1+_ : ⟨ R` ⟩ → ℕ → ⟨ R` ⟩
  f pow1+ zero = 1r`
  f pow1+ suc zero = f
  f pow1+ n@(suc (suc _)) = (f ^ n)
 
  pow1+≡^ : ∀ x k → x pow1+ k ≡  x ^ k
  pow1+≡^ x zero = refl
  pow1+≡^ x (suc zero) = sym (R`.·IdR _)
  pow1+≡^ x (suc (suc k)) = refl
 
 
 
  _powMaybe_ : ⟨ R` ⟩ → ℕ → Maybe ⟨ R` ⟩
  x powMaybe zero = nothing
  x powMaybe suc zero = just x
  x powMaybe suc n = just (x pow1+ (suc n) )
 
  powMaybe≡^ : ∀ x k → fromJust-def 1r` (x powMaybe k) ≡  x ^ k
  powMaybe≡^ x zero = refl
  powMaybe≡^ x (suc zero) = sym (R`.·IdR _)
  powMaybe≡^ x (suc (suc k)) = refl
 
 
 
  powMaybe-suc : ∀ v m → v powMaybe suc m ≡ just (v ^ (suc m))
  powMaybe-suc v zero = cong just (sym (R`.·IdR v))
  powMaybe-suc v (suc m) = refl
 
 
  pow1+-suc : ∀ m v → v pow1+ suc m ≡ v pow1+ m ·` v
  pow1+-suc zero v = sym (R`.·IdL _)
  pow1+-suc one v = cong (v ·`_) (R`.·IdR _)
  pow1+-suc (suc (suc m)) v = R`.·Comm _ _
 
  _mb·`mb_ : Maybe ⟨ R` ⟩ → Maybe ⟨ R` ⟩ → Maybe ⟨ R` ⟩
  nothing mb·`mb x₁ = x₁
  just x mb·`mb y = just (Mb.rec x (x ·`_) y)
 
 
  powMaybe-+ : ∀ {x} e f → (x powMaybe (e ℕ.+ f)) ≡ ((x powMaybe e) mb·`mb (x powMaybe f))
  powMaybe-+ zero f = refl
  powMaybe-+ one zero = refl
  powMaybe-+ {x} one one = cong (λ x' → just (x ·` (x'))) (R`.·IdR _)
  powMaybe-+ one (suc (suc f)) = refl
  powMaybe-+ {x} (suc (suc e)) zero =
    cong (λ e → just (x ·` (x ·` x ^ e))) (ℕ.+-zero e)
  powMaybe-+ {x} (suc (suc e)) one = cong just
    (sym (·-of-^-is-^-of-+ x (suc (suc e)) 1) ∙
     cong₂ _·`_ refl (R`.·IdR _))
  powMaybe-+ {x} (suc (suc e)) (suc (suc f)) = cong just
    (sym (·-of-^-is-^-of-+ x (suc (suc e)) (suc (suc f))))
 
 
  mb·`mbIdR : ∀ x → x mb·`mb nothing ≡ x
  mb·`mbIdR nothing = refl
  mb·`mbIdR (just x) = refl
 
 
  evalMonomial : ∀ {n} → Monomial n → Vec ⟨ R` ⟩ n → Maybe ⟨ R` ⟩
  evalMonomial {n = 0} _ _ = nothing
  evalMonomial {n = 1} (m ∷ _) (v ∷ _) = v powMaybe m
  evalMonomial {n = suc (suc _)} (m ∷ xs) (v ∷ vs) = (evalMonomial xs vs) mb·`mb (v powMaybe m)
 
  evalMonomial∷ : ∀ {n} m ms v vs → evalMonomial {suc n} (m ∷ ms) (v ∷ vs) ≡
                                    ((evalMonomial ms vs) mb·`mb (v powMaybe m))
  evalMonomial∷ m [] v [] = refl
  evalMonomial∷ m (x ∷ ms) v (x₁ ∷ vs) = refl
 
 
  fromJust-def-scalar : ∀ k → fromJust-def 1r` (map-Maybe scalar` k)
       ≡ scalar` (fromJust-def 1r k)
  fromJust-def-scalar nothing = sym pres1
  fromJust-def-scalar (just x) = refl
 
  -[_] : Bool → ⟨ R ⟩ → ⟨ R ⟩
  -[ false ] = -_
  -[ true ] = idfun _
 
 
  -`[_] : Bool → ⟨ R` ⟩ → ⟨ R` ⟩
  -`[ false ] = -`_
  -`[ true ] = idfun _
 
  -`[not] : ∀ b x → -` (-`[ b ] x) ≡ -`[ not b ] x
  -`[not] false x = R`.-Idempotent x
  -`[not] true x = refl
 
  -`[_]distR+ : ∀ b x y → -`[ b ] (x +` y) ≡ -`[ b ] x +` -`[ b ] y
  -`[ false ]distR+ x y = sym (R`.-Dist _ _)
  -`[ true ]distR+ x y = refl
 
  -`[_]· : ∀ b x y → (-`[ b ] x) ·` y ≡ -`[ b ] (x ·` y)
  -`[ false ]· x y = R`.-DistL· _ _
  -`[ true ]· x y = refl
 
  -`[]-fromJust-def-scalar : ∀ b k →
      -`[ b ] (fromJust-def 1r` (map-Maybe scalar` k))
       ≡
       scalar` (-[ b ] (fromJust-def 1r k))
  -`[]-fromJust-def-scalar false k = cong (-`_) (fromJust-def-scalar k) ∙ sym (pres- _)
  -`[]-fromJust-def-scalar true k = fromJust-def-scalar k
 
  _mb·`_ : Maybe ⟨ R` ⟩ → ⟨ R` ⟩ → ⟨ R` ⟩
  nothing mb·` y = y
  just x mb·` y = x ·` y
 
  -`[_]0 : ∀ b → -`[ b ] 0r` ≡ 0r`
  -`[ false ]0 =  R`.0Selfinverse
  -`[ true ]0 = refl
 
  -`[_]-flip≡ : ∀ b x y → -`[ b ] x ≡ y → x ≡ -`[ b ] y
  -`[ false ]-flip≡ x y p = sym (R`.-Idempotent x) ∙ cong -`_ p
  -`[ true ]-flip≡ x y p = p
 
  evalPolynomialTerm' : ∀ {n} → ((Maybe ⟨ R ⟩) × Monomial n) → Vec ⟨ R` ⟩ n → ⟨ R` ⟩
  evalPolynomialTerm' (mbK , m) xs =  (Mb.fromJust-def 1r`
    (map-Maybe scalar` mbK mb·`mb evalMonomial m xs))
 
 
  evalPolynomialTerm : ∀ {n} → PolynomialTerm n → Vec ⟨ R` ⟩ n → ⟨ R` ⟩
  evalPolynomialTerm (b , mbK , m) xs = -`[ b ] (evalPolynomialTerm' ( mbK , m) xs)
 
 
 
  evalPolynomial :  ∀ {n} → Polynomial n → Vec ⟨ R` ⟩ n → ⟨ R` ⟩
  evalPolynomial [] vs = 0r`
  evalPolynomial P[ x ] vs = evalPolynomialTerm x vs
  evalPolynomial ((false , x@(mbK , m)) ∷ xs@(_ ∷ _)) vs =
   evalPolynomial xs vs -` evalPolynomialTerm' x vs
  evalPolynomial ((true , x@(mbK , m)) ∷ xs@(_ ∷ _)) vs =
   evalPolynomial xs vs +` evalPolynomialTerm' x vs
 
  instance
   EvalInVecRPolynomial : EvalInVecR Polynomial
   EvalInVecRPolynomial .EvalInVecR.evalInVecR = evalPolynomial
 
 
  Poly·X : ∀ {n} → Polynomial (suc n) → Polynomial (suc n)
  Poly·X {n} = L.map (map-snd (map-snd λ { (x ∷ xs) → suc x ∷ xs  }))
 
  Poly↑ : ∀ {n} → Polynomial n → Polynomial (suc n)
  Poly↑ {n} = L.map (map-snd (map-snd (zero ∷_)))
 
  evalPolynomial∷ : ∀ {n} t p vs → evalPolynomial {n = n} (t ∷ p) vs
                          ≡ evalPolynomial p vs +` evalPolynomialTerm t vs
  evalPolynomial∷ t [] vs = sym (R`.+IdL _)
  evalPolynomial∷ (false , _) (x ∷ p) vs = refl
  evalPolynomial∷ (true , _) (x ∷ p) vs = refl
 
  evalPolynomial++ : ∀ {n} p₀ p₁ vs → evalPolynomial {n = n} (p₀ L.++ p₁) vs
                          ≡ evalPolynomial p₁ vs +` evalPolynomial p₀ vs
  evalPolynomial++ [] p₁ vs = sym (R`.+IdR _)
  evalPolynomial++ (x ∷ p₀) p₁ vs =
       evalPolynomial∷ x (p₀ L.++ p₁) vs
    ∙∙ cong (_+` _) (evalPolynomial++ p₀ p₁ vs)
       ∙ sym (R`.+Assoc _ _ _)
    ∙∙ cong (evalPolynomial p₁ vs +`_) (sym (evalPolynomial∷ x p₀ vs)  )
 
  evalMonomial·X : ∀ n m ms v vs → evalMonomial {suc n} (suc m ∷ ms) (v ∷ vs)
                              ≡ (evalMonomial {suc n} (m ∷ ms) (v ∷ vs) mb·`mb just v)
  evalMonomial·X n m ms v vs =
       evalMonomial∷ (suc m) ms v vs
       ∙∙ hlp (evalMonomial ms vs) m
    ∙∙ cong (_mb·`mb just v) (sym (evalMonomial∷ m ms v vs))
   where
 
 
 
    hlp : ∀ u m → (u mb·`mb (v powMaybe suc m)) ≡
       ((u mb·`mb (v powMaybe m)) mb·`mb just v)
    hlp nothing zero = refl
    hlp nothing one = cong just (cong (v ·`_) (R`.·IdR _))
    hlp nothing (suc (suc m)) = cong just (R`.·Comm _ _)
    hlp (just x) zero = refl
    hlp (just x) one = cong just
      (cong (x ·`_) (cong (v ·`_) (R`.·IdR _)) ∙ R`.·Assoc _ _ _ )
    hlp (just x) (suc (suc m)) = cong just
      (cong (x ·`_) (R`.·Comm _ _) ∙ R`.·Assoc _ _ _)
 
 
  evalPolynomial·X : ∀ {n} p v vs →
       evalPolynomial (Poly·X {n} p) (v ∷ vs) ≡
       evalPolynomial p (v ∷ vs) ·` v
  evalPolynomial·X [] v vs = sym (R`.0LeftAnnihilates _)
  evalPolynomial·X {n} (x@(b , k , m ∷ ms) ∷ p) v vs =
       evalPolynomial∷ _ (Poly·X p) (v ∷ vs)
     ∙∙ cong₂ _+`_
         (evalPolynomial·X p v vs)
         (cong -`[ b ] (
                 (cong (λ u → fromJust-def 1r` ((map-Maybe scalar` k) mb·`mb u))
                  (evalMonomial·X n m ms v vs) ∙
                   hlp (evalMonomial (m ∷ ms) (v ∷ vs)) (map-Maybe scalar` k))
              ∙ sym (∘fromJust-def (_·` v) 1r`
               ((map-Maybe scalar` k) mb·`mb evalMonomial (m ∷ ms) (v ∷ vs))))
            ∙ sym (-`[ b ]· _ _))
     ∙∙ sym (R`.·DistL+ _ _ v)
       ∙ cong (_·` v) (sym (evalPolynomial∷ _ p _))
   where
   hlp : ∀ u k → fromJust-def 1r` (k mb·`mb (u mb·`mb just v))
               ≡ fromJust-def (1r` ·` v) (map-Maybe (_·` v) (k mb·`mb u))
   hlp nothing nothing = sym (R`.·IdL _)
   hlp nothing (just x) = refl
   hlp (just x) nothing = refl
   hlp (just x) (just x₁) = R`.·Assoc _ _ _
 
  evalPolynomial↑ : ∀ {n} p v vs →
                     evalPolynomial (Poly↑ p) (v ∷ vs) ≡
                      evalPolynomial {n = n} p (vs)
  evalPolynomial↑ [] v vs = refl
  evalPolynomial↑ (x ∷ p) v vs =
        evalPolynomial∷ _ (Poly↑ p) (v ∷ vs)
     ∙∙ cong₂ _+`_ (evalPolynomial↑ p v vs)
         (cong (-`[ x .fst ] ∘ fromJust-def 1r` ∘ (map-Maybe scalar` (x .snd .fst)) mb·`mb_)
           (   evalMonomial∷ _ _ v vs
            ∙ mb·`mbIdR _))
     ∙∙ sym (evalPolynomial∷ _ p vs)
 
 
  -- sign multiplication: false = “negated”, true = “unchanged”
  _combineSign_ : Bool → Bool → Bool
  true  combineSign b = b
  false combineSign true  = false
  false combineSign false = true
 
  -- Maybe-coefficient multiplication, with `nothing` = implicit 1
  _mb·mb_ : Maybe ⟨ R ⟩ → Maybe ⟨ R ⟩ → Maybe ⟨ R ⟩
  nothing mb·mb y = y
  just x  mb·mb y = just (Mb.rec x (x ·_) y)
 
  -- Monomial multiplication = add exponents pointwise
  mon· : ∀ {n} → Monomial n → Monomial n → Monomial n
  mon· [] [] = []
  mon· (e ∷ es) (f ∷ fs) = (ℕ._+_ e f) ∷ mon· es fs
 
 
  PolynomialTerm'· : ∀ {n} → (Maybe ⟨ R ⟩) × Monomial n → (Maybe ⟨ R ⟩) × Monomial n → (Maybe ⟨ R ⟩) × Monomial n
  PolynomialTerm'· {n} (k₁ , m₁) (k₂ , m₂) =
    ( k₁ mb·mb k₂
    , mon· m₁ m₂
    )
 
 
  PolynomialTerm· : ∀ {n} → PolynomialTerm n → PolynomialTerm n → PolynomialTerm n
  PolynomialTerm· {n} (b₁ , a₁) (b₂ , a₂) =
    ( b₁ combineSign b₂ , PolynomialTerm'· a₁ a₂
    )
 
 
  -- sign action respects multiplication
  -`[]-combineSign : ∀ b₁ b₂ x y →
    -`[ b₁ combineSign b₂ ] (x ·` y) ≡ (-`[ b₁ ] x) ·` (-`[ b₂ ] y)
  -`[]-combineSign true true x y = refl
  -`[]-combineSign true false x y = sym (R`.-DistR· x y)
  -`[]-combineSign false true x y = sym (R`.-DistL· x y)
  -`[]-combineSign false false x y =  sym (R`.-Dist· x y)
 
 
 
  map-Maybe-mb·mb : ∀ k₁ k₂ →
    map-Maybe scalar` (k₁ mb·mb k₂)
    ≡ (map-Maybe scalar` k₁) mb·`mb (map-Maybe scalar` k₂)
  map-Maybe-mb·mb nothing k₂ = refl
  map-Maybe-mb·mb (just x) nothing = refl
  map-Maybe-mb·mb (just x) (just y) =
    cong just (pres· x y)
 
 
  fromJust-def-mb·`mb :
    ∀ a b →
    fromJust-def 1r` (a mb·`mb b)
    ≡ fromJust-def 1r` a ·` fromJust-def 1r` b
  fromJust-def-mb·`mb nothing nothing =
    sym (R`.·IdR _)
  fromJust-def-mb·`mb nothing (just y) =
    sym (R`.·IdL _)
  fromJust-def-mb·`mb (just x) nothing =
    sym (R`.·IdR _)
  fromJust-def-mb·`mb (just x) (just y) = refl
 
  mb·`mb-comm : ∀ x y → x mb·`mb y ≡ y mb·`mb x
  mb·`mb-comm nothing nothing = refl
  mb·`mb-comm nothing (just y) = refl
  mb·`mb-comm (just x) nothing = refl
  mb·`mb-comm (just x) (just y) =
    cong just (R`.·Comm x y)
 
  mb·`mb-assoc : ∀ x y z → (x mb·`mb y) mb·`mb z ≡ x mb·`mb (y mb·`mb z)
  mb·`mb-assoc nothing y z = refl
  mb·`mb-assoc (just x) nothing z = refl
  mb·`mb-assoc (just x) (just y) nothing = refl
  mb·`mb-assoc (just x) (just y) (just z) =
    cong just (sym (R`.·Assoc x y z))
 
  evalMonomial-mon· : ∀ {n} (m₁ m₂ : Monomial n) (xs : Vec ⟨ R` ⟩ n) →
    evalMonomial (mon· m₁ m₂) xs ≡ evalMonomial m₁ xs mb·`mb evalMonomial m₂ xs
  evalMonomial-mon· {n = 0} [] [] _ = refl
  evalMonomial-mon· {n = 1} (e ∷ []) (f ∷ []) (x ∷ []) = powMaybe-+ e f
  evalMonomial-mon· {n = suc (suc n)} (e ∷ es) (f ∷ fs) (x ∷ xs) =
    let z = evalMonomial-mon· es fs xs
    in cong₂ (_mb·`mb_) z (powMaybe-+ e f)
       ∙∙ mb·`mb-assoc (evalMonomial es xs) _ _
       ∙∙ cong ((evalMonomial es xs) mb·`mb_) (sym (mb·`mb-assoc (evalMonomial fs xs) (x powMaybe e) (x powMaybe f))
          ∙∙ cong (_mb·`mb (x powMaybe f)) (mb·`mb-comm (evalMonomial fs xs) (x powMaybe e))
          ∙∙ (mb·`mb-assoc (x powMaybe e) (evalMonomial fs xs) (x powMaybe f)))
       ∙ sym (mb·`mb-assoc (evalMonomial es xs) _ _)
 
  PolynomialTerm'·-sound : ∀ {n} t₁ t₂ → (xs : Vec ⟨ R` ⟩ n) →
    evalPolynomialTerm' {n} (PolynomialTerm'· t₁ t₂) xs
    ≡ evalPolynomialTerm' t₁ xs ·` evalPolynomialTerm' t₂ xs
  PolynomialTerm'·-sound (k₁ , m₁) (k₂ , m₂) xs =
   (fromJust-def-mb·`mb (map-Maybe scalar` (k₁ mb·mb k₂)) (evalMonomial (mon· m₁ m₂) xs))
         ∙∙  cong₂ _·`_
                (cong (fromJust-def 1r`) (map-Maybe-mb·mb k₁ k₂)
                ∙ fromJust-def-mb·`mb (map-Maybe scalar` k₁) (map-Maybe scalar` k₂) )
                (cong (fromJust-def 1r`) (evalMonomial-mon· m₁ m₂ xs)
                 ∙ fromJust-def-mb·`mb (evalMonomial m₁ xs) _)
            ∙ R`.·CommAssocSwap _ _ _ _
         ∙∙ cong₂ _·`_
           (sym (fromJust-def-mb·`mb (map-Maybe scalar` k₁) (evalMonomial m₁ xs)))
           (sym (fromJust-def-mb·`mb (map-Maybe scalar` k₂) (evalMonomial m₂ xs)))
 
  PolynomialTerm·-sound : ∀ {n} (t₁ t₂ : PolynomialTerm n) (xs : Vec ⟨ R` ⟩ n) →
    evalPolynomialTerm (PolynomialTerm· t₁ t₂) xs
    ≡ evalPolynomialTerm t₁ xs ·` evalPolynomialTerm t₂ xs
  PolynomialTerm·-sound (b₁ , a₁) (b₂ , a₂) xs =
      cong (-`[ b₁ combineSign b₂ ]) (PolynomialTerm'·-sound a₁ a₂ xs)
      ∙ -`[]-combineSign b₁ b₂ _ _

  trivialCD : ∀ a b → CommonDenom a b
  trivialCD a b = (a , (b , 1r)) , sym (·IdR _) , sym (·IdR _)
 
  PoorFactor : ∀ {n} → (P : IteratedHornerForms n) → Type (ℓ-max ℓ ℓ`)
 
  PoorFactor {n} P = Σ[ a ∈ Maybe ⟨ R ⟩ ] Σ[ m ∈ Monomial n ]
                         Σ[ P' ∈ IteratedHornerForms n ]
                          (∀ xs → just (eval P xs) ≡
                              (      (map-Maybe scalar` a
                              mb·`mb (evalMonomial m xs))
                              mb·`mb (just (eval P' xs))))
 
  unitPolynomialTerm : ∀ {n} → PolynomialTerm n
  unitPolynomialTerm = (true , (nothing , replicate zero))
 
  unitPolynomialTerm? : ∀ {n} x → Dec (x ≡ unitPolynomialTerm {n})
  unitPolynomialTerm? (true , nothing , xs) =
    mapDec (cong (λ xs → true , nothing , xs))
           (_∘ cong (snd ∘ snd))
      (VecPath.discreteA→discreteVecA ℕ.discreteℕ _ xs (replicate zero))
  unitPolynomialTerm? (false , _ , _) = no (false≢true ∘ cong fst)
  unitPolynomialTerm? (_ , just x , _) = no (¬just≡nothing ∘ cong (fst ∘ snd))
 
  evalUnitPolynomialTerm : ∀ {n} xs → evalPolynomialTerm (unitPolynomialTerm {n}) xs ≡ 1r`
  evalUnitPolynomialTerm [] = refl
  evalUnitPolynomialTerm (x ∷ xs) =
 
   cong (fromJust-def 1r`) (evalMonomial∷ zero (replicate zero) x xs)
     ∙∙ fromJust-def-mb·`mb (evalMonomial (replicate zero) xs) nothing
     ∙∙ R`.·IdL' _ _ (evalUnitPolynomialTerm xs)
 
  evalPolynomialTermTimesPolynomial :  ∀ {n} mm P xs →
       (evalPolynomialTerm mm xs ·` evalPolynomial P xs)
     ≡ evalPolynomial (L.map (PolynomialTerm· {n} mm) P) xs
  evalPolynomialTermTimesPolynomial mm [] xs = R‵.0RightAnnihilates _
  evalPolynomialTermTimesPolynomial mm (x ∷ P) xs =
    cong (evalPolynomialTerm mm xs ·`_) (evalPolynomial∷ x P xs)
     ∙∙ R`.·DistR+ _ _ _
     ∙∙ (cong₂ _+`_ (evalPolynomialTermTimesPolynomial mm P xs)
        (sym (PolynomialTerm·-sound mm x xs) )
       ∙ sym (evalPolynomial∷ _ (L.map (PolynomialTerm· mm) P) xs))
 
  module PolyUtils where
 
 
   maybeNegateScalar : (x : ⟨ R ⟩) → Maybe (Σ[ -x ∈ ⟨ R ⟩ ] - -x ≡ x)
   maybeNegateScalar x = do y ← mbNeg?Scalar ; y x
 
   PolynomialTermNormalize : ∀ {n} mm → Σ[ mm' ∈ _ ] ∀ xs →
        evalPolynomialTerm {n} mm xs ≡ evalPolynomialTerm {n} mm' xs
   PolynomialTermNormalize mm@(b , nothing , mms) = mm , λ _ → refl
   PolynomialTermNormalize mm@(b , just k , mms) =
     Mb.rec (mm , λ _ → refl)
       (λ (-k , p) → (not b , just -k , mms) ,
          λ xs → sym (R`.-Idempotent _)
            ∙∙ cong -`_ (-`[not] b  _)
            ∙∙ (R`.-IsMult-1 _
             ∙∙ R`.·Comm _ _
             ∙∙ (-`[ not b ]· _ _
               ∙ cong (-`[ not b ])
                (cong₂ _·`_ (fromJust-def-mb·`mb (map-Maybe scalar` (just k)) (evalMonomial mms xs)) refl
                  ∙∙ R`.·Comm _ _ ∙ sym (R`.-IsMult-1 _)
                     ∙ sym (R`.-DistL· _ _)
                       ∙ cong₂ _·`_ ((λ i → pres- (p (~ i)) (~ i))
                          ∙ cong scalar` (-Idempotent -k)) refl
                  ∙∙ sym (fromJust-def-mb·`mb (map-Maybe scalar` (just -k)) (evalMonomial mms xs))) )))
       (maybeNegateScalar k)
 
 
   combineLikeTerms-sameSign : ∀ {n} b k k' mn xs →
     evalPolynomialTerm {n} (b , k , mn) xs +`
       evalPolynomialTerm (b , k' , mn) xs
       ≡
       evalPolynomialTerm
       (b , just (fromJust-def 1r k + fromJust-def 1r k') , mn) xs
   combineLikeTerms-sameSign b k k' mn xs = sym (-`[ b ]distR+ _ _) ∙
     cong (-`[ b ]) (
         cong₂ _+`_ (fromJust-def-mb·`mb (map-Maybe scalar` k) (evalMonomial mn xs))
                    (fromJust-def-mb·`mb (map-Maybe scalar` k') (evalMonomial mn xs))
       ∙∙ sym (R`.·DistL+ _ _ _)
       ∙∙ (cong (_·` fromJust-def 1r` (evalMonomial mn xs))
         (cong₂ _+`_ (fromJust-def-scalar k) (fromJust-def-scalar k')
          ∙ sym (pres+ _ _))
         ∙ sym (fromJust-def-mb·`mb (map-Maybe scalar`
           (just (fromJust-def 1r k + fromJust-def 1r k'))) (evalMonomial mn xs))))
 
   combineLikeTerms-dec : ∀ {n} → ∀ b k b' k' mn →
      Maybe ((Σ[ (b'' , k'') ∈ _ × _ ]
        (∀ xs → evalPolynomialTerm {n} (b , k , mn) xs +` evalPolynomialTerm {n} (b' , k' , mn) xs
             ≡ evalPolynomialTerm {n} (b'' , k'' , mn) xs)) ⊎
       (∀ xs → evalPolynomialTerm {n} (b , k , mn) xs +` evalPolynomialTerm {n} (b' , k' , mn) xs ≡ 0r`))
   combineLikeTerms-dec false k false k' mn = just (inl ((false ,
    just (Mb.fromJust-def 1r k + Mb.fromJust-def 1r k')) , combineLikeTerms-sameSign false k k' mn))
   combineLikeTerms-dec false nothing true nothing mn = just (inr λ _ → R`.+InvL _)
   combineLikeTerms-dec false nothing true (just x) mn = nothing
   combineLikeTerms-dec false (just x) true nothing mn = nothing
   combineLikeTerms-dec false (just x) true (just x₁) mn = nothing
   combineLikeTerms-dec true nothing false nothing mn = just (inr λ _ → R`.+InvR _)
   combineLikeTerms-dec true nothing false (just x) mn = nothing
   combineLikeTerms-dec true (just x) false nothing mn = nothing
   combineLikeTerms-dec true (just x) false (just x₁) mn = nothing
   combineLikeTerms-dec true k true k' mn =
    just (inl ((true , (just (Mb.fromJust-def 1r k + Mb.fromJust-def 1r k'))) ,
    combineLikeTerms-sameSign true k k' mn))
 
   combineLikeTerms-general : ∀ {n} → ∀ b k b' k' mn → Σ[ (b'' , k'') ∈ _ × _ ]
        (∀ xs → evalPolynomialTerm {n} (b , k , mn) xs +` evalPolynomialTerm {n} (b' , k' , mn) xs
             ≡ evalPolynomialTerm {n} (b'' , k'' , mn) xs)
   combineLikeTerms-general b k b' k' mn =
     let k'' = -[ b ] (Mb.fromJust-def 1r k) + -[ b' ] (Mb.fromJust-def 1r k')
     in (true , just k'') ,
        λ xs → cong₂ _+`_ (cong (-`[ b ])
               (fromJust-def-mb·`mb (map-Maybe scalar` k) (evalMonomial mn xs))
                ∙ sym (-`[ b ]· _ _) ∙ cong₂ _·`_ (-`[]-fromJust-def-scalar b k) refl)
               (cong (-`[ b' ]) (fromJust-def-mb·`mb (map-Maybe scalar` k') (evalMonomial mn xs))
                ∙ sym (-`[ b' ]· _ _) ∙ cong₂ _·`_ (-`[]-fromJust-def-scalar b' k') refl)
               ∙∙ sym (R`.·DistL+ _ _ _)
                ∙∙ (cong₂ _·`_ (sym (pres+ _ _)) refl
                 ∙ sym (fromJust-def-mb·`mb
                              (map-Maybe scalar` (just k''))
                              (evalMonomial mn xs)))
 
   combineLikeTerms : ∀ {n} → ∀ b k b' k' mn →
       ((Σ[ (b'' , k'') ∈ _ × _ ]
        (∀ xs → evalPolynomialTerm {n} (b , k , mn) xs +` evalPolynomialTerm {n} (b' , k' , mn) xs
             ≡ evalPolynomialTerm {n} (b'' , k'' , mn) xs)) ⊎
       (∀ xs → evalPolynomialTerm {n} (b , k , mn) xs +` evalPolynomialTerm {n} (b' , k' , mn) xs ≡ 0r`))
   combineLikeTerms b k b' k' mn =
     ⊎.map (idfun _)
           (idfun _) $
     fromJust-def (inl (combineLikeTerms-general b k b' k' mn))
       (Mb.rec (combineLikeTerms-dec b k b' k' mn) (λ _≟_ →
         decRec
           (λ p → just $ inr λ xs →
              cong₂ _+`_ (cong (-`[ b ])
               (fromJust-def-mb·`mb (map-Maybe scalar` k) (evalMonomial mn xs))
                ∙ sym (-`[ b ]· _ _))
               (cong (-`[ b' ]) (fromJust-def-mb·`mb (map-Maybe scalar` k') (evalMonomial mn xs))
                ∙ sym (-`[ b' ]· _ _))
               ∙∙ sym (R`.·DistL+ _ _ _)
                ∙∙ R`.0LeftAnnihilates' _ _
                 (((cong₂ _+`_ (-`[]-fromJust-def-scalar b k) (-`[]-fromJust-def-scalar b' k')
                    ∙ sym (pres+ _ _))
                  ∙ cong scalar` p) ∙ pres0))
           (λ _ → nothing)
          ((-[ b ] (Mb.fromJust-def 1r k) + -[ b' ] (Mb.fromJust-def 1r k')) ≟ 0r) ) mbDiscreteScalars)
 
 
   Term+Polynomial : ∀ {n} → (mm : PolynomialTerm n) (P : Polynomial n) →
          Σ[ mm+P ∈ Polynomial n ]
           (∀ xs → evalPolynomial mm+P xs ≡
             (evalPolynomialTerm mm xs +` evalPolynomial P xs))
   Term+Polynomial mm [] = [ mm ] , λ _ → sym (R`.+IdR _)
   Term+Polynomial mm@(b , k , mn) (mm'@(b' , k' , mn') ∷ P) =
     decRec (λ mn≡mn' →
               ⊎.rec
                 (λ ((b'' , k'') , u) → (b'' , k'' , mn) ∷ P ,
                    λ xs → evalPolynomial∷ (b'' , k'' , mn) P xs  ∙
                      R`.+Comm _ _ ∙ cong₂ _+`_ (sym (u xs) ∙
                        cong₂ _+`_ refl ((cong
                       (λ mn →  evalPolynomialTerm (b' , k' , mn) xs)
                        mn≡mn'))) refl
                       ∙∙ sym (R`.+Assoc _ _ _)
                     ∙∙ cong₂ _+`_ refl (R`.+Comm _ _ ∙ sym (evalPolynomial∷ mm' P xs)))
                 (λ u → P , λ xs →
                     sym (R`.+IdL' _ _
                      (cong₂ _+`_ refl (cong
                       (λ mn →  evalPolynomialTerm (b' , k' , mn) xs)
                        (sym mn≡mn')) ∙ u xs))
                       ∙∙ sym (R`.+Assoc _ _ _)
            ∙∙ cong₂ _+`_ refl (R`.+Comm _ _ ∙ sym (evalPolynomial∷ mm' P xs)))
                 (combineLikeTerms b k b' k' mn)
                 )
        (λ _ →
          let mm+P , u = Term+Polynomial mm P
          in mm' ∷ mm+P , λ xs →
                evalPolynomial∷ mm' mm+P xs
            ∙∙  cong₂ _+`_ (u xs) refl
              ∙  sym (R`.+Assoc _ _ _)
            ∙∙ cong₂ _+`_ refl (sym (evalPolynomial∷ mm' P xs)))
       (VecPath.discreteA→discreteVecA ℕ.discreteℕ _ mn mn')
 
   Polynomial+ : ∀ {n} → (P Q : Polynomial n) →
          Σ[ P+Q ∈ Polynomial n ]
           (∀ xs → evalPolynomial P+Q xs ≡
             (evalPolynomial P xs +` evalPolynomial Q xs))
   Polynomial+ [] Q = Q , λ xs → sym (R`.+IdL _)
   Polynomial+ (mm ∷ P) Q =
    let P+Q , v = Polynomial+ P Q
    in map-snd (λ u xs → u xs ∙∙ cong (evalPolynomialTerm mm xs +`_) (v xs)
            ∙∙ (R`.+Assoc _ _ _ ∙
              cong₂ _+`_ (R`.+Comm _ _ ∙ sym (evalPolynomial∷ mm P xs)) refl ))
        (Term+Polynomial mm P+Q)
 
 
   Polynomial· : ∀ {n} → (P Q : Polynomial n) →
          Σ[ P·Q ∈ Polynomial n ]
           (∀ xs → evalPolynomial P·Q xs ≡
             (evalPolynomial P xs ·` evalPolynomial Q xs))
   Polynomial· [] Q = [] , λ _ → sym (R`.0LeftAnnihilates _)
   Polynomial· (mm ∷ P) Q =
    let P·Q , v = Polynomial· P Q
    in map-snd (λ u xs → u xs ∙∙
              cong₂ (_+`_) (v xs) (sym (evalPolynomialTermTimesPolynomial mm Q xs))
              ∙∙ sym (R`.·DistL+ _ _ _) ∙
               cong₂ _·`_ (sym (evalPolynomial∷ mm P xs)) refl)
         (Polynomial+ P·Q (L.map (PolynomialTerm· mm) Q))
 
 
  module CommonMonomial (commonDenom : ∀ a b → CommonDenom a b) where
 
   commonDenomPow : ∀ a b → Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                      (∀ x → x powMaybe a ≡ ((x powMaybe a') mb·`mb (x powMaybe c)))
                       ×
                      (∀ x → x powMaybe b ≡ ((x powMaybe b') mb·`mb (x powMaybe c)))
   commonDenomPow a b =
    let a' = a ℕ.∸ ℕ.min a b
        b' = b ℕ.∸ ℕ.min a b
        c = ℕ.min a b
    in (a' , b' , c)
        , (λ x → cong (x powMaybe_) (sym (ℕ.≤-∸-+-cancel {c} {a} (ℕ.min-≤-left {a} {b}))) ∙ powMaybe-+ {x} a' c)
        , (λ x → cong (x powMaybe_) (sym (ℕ.≤-∸-+-cancel {c} {b} (ℕ.min-≤-right {a} {b}))) ∙ powMaybe-+ {x} b' c)
 
 
   toMaybeKnownOne : ∀ x → Σ[ x' ∈ Maybe _ ] Mb.fromJust-def 1r x' ≡ x
   toMaybeKnownOne x = Mb.rec (just x , refl) (λ 1=x → nothing , 1=x) (maybeEq 1r x)
 
 
   commonDenomPolynomialTerm' : ∀ n a b →
             Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                 (∀ xs → (evalPolynomialTerm' {n} a xs ≡
                           evalPolynomialTerm' {n} a' xs ·` evalPolynomialTerm' {n} c xs))
                  ×
                 (∀ xs → (evalPolynomialTerm' {n} b xs ≡
                           evalPolynomialTerm' {n} b' xs ·` evalPolynomialTerm' {n} c xs))
   commonDenomPolynomialTerm' zero (nothing , []) (nothing , []) =
     ((nothing , []) , (nothing , []) , (nothing , [])) ,
      (λ _ → sym (R`.·IdR _)) , λ _ → sym (R`.·IdR _)
   commonDenomPolynomialTerm' zero (nothing , []) (just x , []) =
     ((nothing , []) , (just x , []) , (nothing , [])) ,
      (λ _ → sym (R`.·IdR _)) , λ _ → sym (R`.·IdR _)
   commonDenomPolynomialTerm' zero (just x , []) (nothing , []) =
     ((just x , []) , (nothing , []) , (nothing , [])) ,
      (λ _ → sym (R`.·IdR _)) , λ _ → sym (R`.·IdR _)
   commonDenomPolynomialTerm' zero (just x₀ , []) (just x₁ , []) =
     let (x₀' , x₁' , y) , p , q = commonDenom x₀ x₁
     in ((just x₀' , []) , (just x₁' , []) , (just y , []))
          , (λ xs → cong scalar` p ∙ (λ i → pres· x₀' y i) ∙
                   cong (evalPolynomialTerm' (just x₀' , []) xs ·`_)
                      (sym (fromJust-def-scalar (just y)) ∙
                       cong (fromJust-def (CommRingStr.1r (snd (fst commAlg))))
                         (sym (mb·`mbIdR
                          (map-Maybe (fst (snd commAlg)) (just y))))))
            , (λ xs → cong scalar` q ∙ (λ i → pres· x₁' y i) ∙
                   cong (evalPolynomialTerm' (just x₁' , []) xs ·`_)
                      (sym (fromJust-def-scalar (just y)) ∙
                       cong (fromJust-def (CommRingStr.1r (snd (fst commAlg))))
                         (sym (mb·`mbIdR
                          (map-Maybe (fst (snd commAlg)) (just y))))))
 
   commonDenomPolynomialTerm' (suc n) (k₀ , x₀ ∷ ms₀) (k₁ , x₁ ∷ ms₁) =
    let ((k₀' , ms₀') , (k₁' , ms₁') , (k₂' , ms₂')) , p , q =
          commonDenomPolynomialTerm' n (k₀ , ms₀) (k₁ , ms₁)
        (x₀' , x₁' , y) , u , v = commonDenomPow x₀ x₁
    in ((k₀' , x₀' ∷ ms₀') , (k₁' , x₁' ∷ ms₁') , (k₂' , y ∷ ms₂'))
         , (λ { (x ∷ xs) →
                 (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₀) (evalMonomial∷ x₀ ms₀ x xs i) i)
                 ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₀) ·`_)
                      (fromJust-def-mb·`mb (evalMonomial ms₀ xs) (x powMaybe x₀))
                 ∙∙ R`.·Assoc _ _ _
               ∙∙ cong₂ _·`_
                    (   sym (fromJust-def-mb·`mb (map-Maybe scalar` k₀) (evalMonomial ms₀ xs))
                     ∙∙ p xs
                     ∙∙ cong₂ _·`_
                           (fromJust-def-mb·`mb (map-Maybe scalar` k₀') (evalMonomial ms₀' xs))
                           (fromJust-def-mb·`mb (map-Maybe scalar` k₂') (evalMonomial ms₂' xs)))
                    (cong (fromJust-def 1r`) (u x)
                     ∙ fromJust-def-mb·`mb (x powMaybe x₀') _ )
                 ∙ R`.·CommAssocSwap _ _ _ _
               ∙∙ cong₂ _·`_
                   (sym (R`.·Assoc _ _ _)
                    ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₀') ·`_)
                      (sym (fromJust-def-mb·`mb (evalMonomial ms₀' xs) (x powMaybe x₀')))
                     ∙∙
                    (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₀')
                            (evalMonomial∷ x₀' ms₀' x xs (~ i)) (~ i)))
                   (sym (R`.·Assoc _ _ _)
                    ∙ cong (fromJust-def 1r` (map-Maybe scalar` k₂') ·`_)
                      (sym (fromJust-def-mb·`mb (evalMonomial ms₂' xs) (x powMaybe y))) ∙
                    (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₂')
                          (evalMonomial∷ y ms₂' x xs (~ i)) (~ i)))})
         , (λ { (x ∷ xs) →
                 (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₁) (evalMonomial∷ x₁ ms₁ x xs i) i)
                 ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₁) ·`_)
                      (fromJust-def-mb·`mb (evalMonomial ms₁ xs) (x powMaybe x₁))
                 ∙∙ R`.·Assoc _ _ _
               ∙∙ cong₂ _·`_
                    (   sym (fromJust-def-mb·`mb (map-Maybe scalar` k₁) (evalMonomial ms₁ xs))
                     ∙∙ q xs
                     ∙∙ cong₂ _·`_
                           (fromJust-def-mb·`mb (map-Maybe scalar` k₁') (evalMonomial ms₁' xs))
                           (fromJust-def-mb·`mb (map-Maybe scalar` k₂') (evalMonomial ms₂' xs)))
                    (cong (fromJust-def 1r`) (v x)
                     ∙ fromJust-def-mb·`mb (x powMaybe x₁') _ )
                 ∙ R`.·CommAssocSwap _ _ _ _
               ∙∙ cong₂ _·`_
                   (sym (R`.·Assoc _ _ _)
                    ∙∙ cong (fromJust-def 1r` (map-Maybe scalar` k₁') ·`_)
                      (sym (fromJust-def-mb·`mb (evalMonomial ms₁' xs) (x powMaybe x₁')))
                     ∙∙
                    (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₁')
                            (evalMonomial∷ x₁' ms₁' x xs (~ i)) (~ i)))
                   (sym (R`.·Assoc _ _ _)
                    ∙ cong (fromJust-def 1r` (map-Maybe scalar` k₂') ·`_)
                      (sym (fromJust-def-mb·`mb (evalMonomial ms₂' xs) (x powMaybe y))) ∙
                    (λ i → fromJust-def-mb·`mb (map-Maybe scalar` k₂')
                          (evalMonomial∷ y ms₂' x xs (~ i)) (~ i)))})
 
   commonDenomPolynomialTerm : ∀ n a b →
             Σ[ (a' , b' , c ) ∈ _ × _ × _ ]
                 (∀ xs → (evalPolynomialTerm {n} a xs ≡
                           evalPolynomialTerm {n} a' xs ·` evalPolynomialTerm {n} c xs))
                  ×
                 (∀ xs → (evalPolynomialTerm {n} b xs ≡
                           evalPolynomialTerm {n} b' xs ·` evalPolynomialTerm {n} c xs))
   commonDenomPolynomialTerm n (false , a₀) (false , a₁) =
     let (a₀' , a₁' , c) , p , q =
            commonDenomPolynomialTerm' n a₀ a₁
     in ((true , a₀') , (true , a₁') , false , c)
         , (λ xs → cong -`_ (p xs) ∙ sym (R`.-DistR· _ _))
         , (λ xs → cong -`_ (q xs) ∙ sym (R`.-DistR· _ _))
   commonDenomPolynomialTerm n (b₀ , a₀) (b₁ , a₁) =
     let (a₀' , a₁' , c) , p , q =
            commonDenomPolynomialTerm' n a₀ a₁
     in ((b₀ , a₀') , (b₁ , a₁') , true , c)
         , (λ xs → cong -`[ b₀ ] (p xs) ∙ sym (-`[ b₀ ]· _ _))
         , (λ xs → cong -`[ b₁ ] (q xs) ∙ sym (-`[ b₁ ]· _ _))
 
   polynomialNeg  : ∀ {n} → Polynomial n → Polynomial n
   polynomialNeg = L.map (map-fst not)
 
   evalPolynomialNeg :  ∀ {n} P xs →
        -` (evalPolynomial {n} P xs)
      ≡ evalPolynomial (polynomialNeg P) xs
   evalPolynomialNeg [] xs = R`.0Selfinverse
   evalPolynomialNeg (x ∷ P) xs =
     cong -`_ (evalPolynomial∷ x P xs)
       ∙∙ sym (R`.-Dist _ _)
       ∙∙ (cong₂ _+`_ (evalPolynomialNeg P xs)
           (-`[not] (fst x) _)
         ∙ sym (evalPolynomial∷ _ (polynomialNeg P) xs))
 
 
   factorOutMonomial : ∀ {n} (P : Polynomial n) →
                          Σ[ (mm , P') ∈ PolynomialTerm n × Polynomial n ]
                             (∀ xs → evalPolynomial P xs ≡ (evalPolynomialTerm mm xs ·` evalPolynomial P' xs))
   factorOutMonomial [] = (unitPolynomialTerm , []) ,
     λ xs → sym (R`.0RightAnnihilates _)
   factorOutMonomial (mm ∷ []) = (mm , [ unitPolynomialTerm ]) ,
     λ xs → sym (R`.·IdR' _ _ (evalUnitPolynomialTerm xs))
   factorOutMonomial (x ∷ ms) =
     let (mm , P') , u = factorOutMonomial ms
         (x' , mm' , c) , p , q =
            commonDenomPolynomialTerm _ x mm
         P'' = L.map (PolynomialTerm· mm') P'
     in (c , x' ∷ P'') ,
          λ xs  → evalPolynomial∷ x ms xs
           ∙∙ cong₂ _+`_
               (u xs ∙ cong (_·` evalPolynomial P' xs) (q xs ∙ R`.·Comm _ _)
                 ∙∙ sym (R`.·Assoc _ _ _)
                 ∙∙ cong (evalPolynomialTerm c xs ·`_)
                      (evalPolynomialTermTimesPolynomial mm' P' xs))
               (p xs ∙ R`.·Comm _ _)
             ∙ sym (R`.·DistR+ _ _ _)
           ∙∙ cong ( evalPolynomialTerm c xs ·`_) (sym (evalPolynomial∷ x' P'' xs))
 
 
  simplifyPolyTermTimesPoly : ∀ n → (mm : PolynomialTerm n) (P : Polynomial n) →
                         Σ[ (mm' , P') ∈ Maybe (PolynomialTerm n) × Maybe (Polynomial n) ]
                           ((∀ x xs → ((map-Maybe (flip evalPolynomialTerm xs) mm'
                              mb·`mb map-Maybe (flip evalPolynomial xs) P')
                              mb·` x) ≡ ((evalPolynomialTerm mm xs ·` evalPolynomial P xs)
                                 ·` x) )) ×
                                 (∀ xs → (fromJust-def 1r` (map-Maybe (flip evalPolynomialTerm xs) mm'
                              mb·`mb map-Maybe (flip evalPolynomial xs) P'))
                               ≡ ((evalPolynomialTerm mm xs ·` evalPolynomial P xs)))
 
  simplifyPolyTermTimesPoly n mm P = w (unitPolynomialTerm? mm) (ww P)
   where
    ww : ∀ P → Dec (P ≡ [ unitPolynomialTerm {n} ])
    ww [] = no ¬nil≡cons
    ww P[ x ] = mapDec (cong (_∷ [])) (_∘ cong (flip (L.lookupAlways mm) ℕ.zero) ) (unitPolynomialTerm? x)
    ww (x ∷ x₁ ∷ P) = no (ℕ.snotz ∘ cong (ℕ.predℕ ∘ L.length))
 
    w : Dec (mm ≡ unitPolynomialTerm) → Dec (P ≡ [ unitPolynomialTerm ]) → _
    w (yes p) (yes p₁) = (nothing , nothing) ,
      ((λ x xs → sym (R`.·IdL' _ _ (R`.·IdL' _ _
       (cong (flip evalPolynomialTerm xs) p
         ∙ evalUnitPolynomialTerm xs) ∙
          cong (flip evalPolynomial xs) (p₁)
            ∙ evalUnitPolynomialTerm xs))) ,
       λ xs → sym (R`.·IdL' _ _
       (cong (flip evalPolynomialTerm xs) p
         ∙ evalUnitPolynomialTerm xs) ∙
          cong (flip evalPolynomial xs) (p₁)
            ∙ evalUnitPolynomialTerm xs) )
    w (yes p) (no ¬p) = (nothing , just P) ,
      (λ x xs → cong (_·` x) (sym (R`.·IdL' _ _
       (cong (flip evalPolynomialTerm xs) p
         ∙ evalUnitPolynomialTerm xs)))) , λ xs →
           sym (R`.·IdL' _ _
       (cong (flip evalPolynomialTerm xs) p
         ∙ evalUnitPolynomialTerm xs))
    w (no ¬p) (yes p) = (just mm , nothing) , (λ x xs →
      cong (_·` x)
        (sym (R`.·IdR' _ _ (cong (flip evalPolynomial xs) p
         ∙ evalUnitPolynomialTerm xs)))) ,
         λ xs → (sym (R`.·IdR' _ _ (cong (flip evalPolynomial xs) p
         ∙ evalUnitPolynomialTerm xs)))
    w (no ¬p) (no ¬p₁) = (just mm , just P) , (λ _ _ → refl) , λ _ → refl
 
  Horner→Poly' : Maybe (Discrete ⟨ R ⟩)
                   → ∀ {n} → (h : IteratedHornerForms n)
                      → Σ (Polynomial n) λ pf → ∀ xs → evalPolynomial pf xs ≡ eval h xs
  Horner→Poly' nothing (const x) = [ true , (just x) , [] ] , λ {[] → refl}
  Horner→Poly' (just _≟_) (const x) =
     hlp (x ≟ 0r) (x ≟ 1r) (Mb.rec nothing (_$ x) mbNeg?Scalar) (x ≟ (- 1r))
   where
   hlp : Dec _ →  Dec _ → Maybe _ → Dec _ → _
   hlp (yes x≡0) _ _ _ = [] , λ {[] → sym (pres0) ∙ cong scalar` (sym x≡0) }
   hlp _ (yes x≡1) _ x₁ =
     [ true , nothing , [] ] , λ {[] → sym (pres1) ∙ cong scalar` (sym x≡1)}
   hlp _ (no ¬p) _ (yes x≡-1) =
     [ false , nothing , [] ] , λ {[] → sym (pres- 1r
       ∙ cong -`_ pres1) ∙ cong scalar` (sym x≡-1)}
   hlp _ (no ¬p) (just (-x , p)) _ = [ false , (just -x) , [] ] ,
     λ { [] → sym (pres- -x) ∙
             cong scalar` p}
   hlp _ (no ¬p) _ (no ¬p₁) = [ true , (just x) , [] ] , λ {[] → refl}
 
  Horner→Poly' _  0H = [] , λ _ → refl
  Horner→Poly' mbD (h₀ ·X+ h₁) =
   let p₀ , q₀ = Horner→Poly' mbD h₀
       p₁ , q₁ = Horner→Poly' mbD h₁
   in Poly·X p₀ L.++ Poly↑ p₁ , λ { vvs@(v ∷ vs) →
           evalPolynomial++ (Poly·X p₀) (Poly↑ p₁) vvs
        ∙ R`.+Comm _ _ ∙ cong₂ _+`_
           (evalPolynomial·X p₀ v vs ∙ cong (_·` v) (q₀ (v ∷ vs)))
           (evalPolynomial↑ p₁ v vs ∙ q₁ vs)}
 
  Horner→Poly : ∀ {n} → (h : IteratedHornerForms n)
                      → Σ (Polynomial n) λ pf → ∀ xs → evalPolynomial pf xs ≡ eval h xs
  Horner→Poly = Horner→Poly' mbDiscreteScalars
 
  IHF≑>Poly : IteratedHornerForms ≑> Polynomial
  IHF≑>Poly ._≑>_.to p = fst (Horner→Poly p)
  IHF≑>Poly ._≑>_.to≑ p xs = sym (snd (Horner→Poly p) xs)
 open PolyEval public
