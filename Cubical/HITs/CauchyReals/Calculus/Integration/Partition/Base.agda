module Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order.Inductive as ℕᵗ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; ℕ₊₁→ℤ; _·_; _-_)
import Cubical.Data.Int.Fast.Properties as ℤ
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne



open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
  hiding (IsContinuous-₂∘)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
  using (IsContinuous-₂∘)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp using
  ( clampᵣ∈intervalℙ
  ; x≤→clampᵣ≡
  ; ≤x→clampᵣ≡
  ; clamp-monotone-≤ᵣ
  )
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation
  hiding (ElimFinSS; go-tail-finj; go-tail-flast)


open import Cubical.Tactics.CauchyReals.ExpressionLifting


open import Cubical.HITs.CauchyReals.Foundation.Rationals


open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.Tactics.CauchyReals.ExpressionLifting


finj-pred : ∀ {n} → Fin (predℕ n) → Fin n
finj-pred {zero} ()
finj-pred {suc n} k = finj k

fsuc-pred : ∀ {n} → Fin (predℕ n) → Fin n
fsuc-pred {zero} ()
fsuc-pred {suc n} k = fsuc k

toℕ-finj-pred : ∀ {n} (k : Fin (predℕ n)) →
  fst (finj-pred {n = n} k) ≡ fst k
toℕ-finj-pred {zero} ()
toℕ-finj-pred {suc n} k = refl

toℕ-fsuc-pred : ∀ {n} (k : Fin (predℕ n)) →
  fst (fsuc-pred {n = n} k) ≡ suc (fst k)
toℕ-fsuc-pred {zero} ()
toℕ-fsuc-pred {suc n} k = refl

split<ᵗ-pred-elim : ∀ {ℓ} {k len} {C : Type ℓ} →
  k ℕᵗ.<ᵗ len →
  (k ℕᵗ.<ᵗ predℕ len → C) →
  (suc k ≡ len → C) →
  C
split<ᵗ-pred-elim {len = zero} ()
split<ᵗ-pred-elim {k = k} {len = suc n} p ltCase lastCase =
  ℕᵗ.split<ᵗ-suc-elim {k = k} {len = n} p ltCase
    (lastCase ∘ cong suc)


record Partition[_,_] (a b : ℝ) : Type₀ where
 field
  len : ℕ
  pts : Fin len → ℝ
  endpoints≤ : a ≤ᵣ b
  a≤pts : ∀ k → a ≤ᵣ pts k
  pts≤b : ∀ k → pts k ≤ᵣ b
  pts≤pts : (k : Fin (predℕ len)) →
    pts (finj-pred {n = len} k) ≤ᵣ pts (fsuc-pred {n = len} k)

 a≤b : a ≤ᵣ b
 a≤b = endpoints≤

 pts'Σ-R : ElimFinSS (Σ _ (_∈ intervalℙ a b)) len
 pts'Σ-R .ElimFinSS.a₀ = a , ≤ᵣ-refl a , a≤b
 pts'Σ-R .ElimFinSS.f k = pts k , a≤pts _ , pts≤b _
 pts'Σ-R .ElimFinSS.aₙ = b , a≤b , ≤ᵣ-refl b

 pts'Σ : Fin (2 ℕ.+ len) → (Σ _ (_∈ intervalℙ a b))
 pts'Σ = ElimFinSS.go pts'Σ-R

 pts' : Fin (2 ℕ.+ len) → ℝ
 pts' = fst ∘ pts'Σ

 pts'-mid : (j : Fin len) → pts' (fsuc (finj j)) ≡ pts j
 pts'-mid j =
   cong fst (go-tail-finj pts'Σ-R len
     (ElimFinSS.f pts'Σ-R) (ElimFinSS.aₙ pts'Σ-R) j)

 pts'-last : pts' (flast {k = 1 ℕ.+ len}) ≡ b
 pts'-last =
   cong fst (go-tail-flast pts'Σ-R len
     (ElimFinSS.f pts'Σ-R) (ElimFinSS.aₙ pts'Σ-R))

 a≤pts' : ∀ k → a ≤ᵣ pts' k
 a≤pts' = fst ∘ snd ∘ pts'Σ

 pts'≤b : ∀ k → pts' k ≤ᵣ b
 pts'≤b = snd ∘ snd ∘ pts'Σ

 pts'≤pts' : ∀ k → pts' (finj k) ≤ᵣ pts' (fsuc k)
 pts'≤pts' k'@(zero , _) = a≤pts' (fsuc k')
 pts'≤pts' k'@(suc k , p) =
   split<ᵗ-pred-elim {len = len} p
     (λ k<len →
       let j : Fin (predℕ len)
           j = k , k<len
           pL : finj k' ≡ fsuc (finj (finj-pred {n = len} j))
           pL = toℕ-injective {k = 2 ℕ.+ len}
             (cong suc (sym (toℕ-finj-pred {n = len} j)))
           pR : fsuc k' ≡ fsuc (finj (fsuc-pred {n = len} j))
           pR = toℕ-injective {k = 2 ℕ.+ len}
             (cong suc (sym (toℕ-fsuc-pred {n = len} j)))
           lEq : pts' (finj k') ≡ pts (finj-pred {n = len} j)
           lEq = cong pts' pL ∙ pts'-mid (finj-pred {n = len} j)
           rEq : pts' (fsuc k') ≡ pts (fsuc-pred {n = len} j)
           rEq = cong pts' pR ∙ pts'-mid (fsuc-pred {n = len} j)
       in subst2 _≤ᵣ_ (sym lEq) (sym rEq) (pts≤pts j))
     (λ sk≡len →
       let j : Fin len
           j = k , p
           pL : finj k' ≡ fsuc (finj j)
           pL = toℕ-injective {k = 2 ℕ.+ len} refl
           pR : fsuc k' ≡ flast {k = 1 ℕ.+ len}
           pR = toℕ-injective {k = 2 ℕ.+ len} (cong suc sk≡len)
           lEq : pts' (finj k') ≡ pts j
           lEq = cong pts' pL ∙ pts'-mid j
           rEq : pts' (fsuc k') ≡ b
           rEq = cong pts' pR ∙ pts'-last
       in subst2 _≤ᵣ_ (sym lEq) (sym rEq) (pts≤b j))

 diffs : Fin (1 ℕ.+ len) → Σ ℝ (0 ≤ᵣ_)
 diffs k = _ , x≤y→0≤y-x (pts' (finj k)) _ (pts'≤pts' k)

 mesh : ℝ
 mesh = foldlFin {n = 1 ℕ.+ len} maxᵣ 0 (fst ∘ diffs)

 isStrictPartition : Type
 isStrictPartition = ∀ k → pts' (finj k) <ᵣ pts' (fsuc k)

 mesh≤ᵣ : ℝ → Type
 mesh≤ᵣ δ = ∀ k →  pts' (fsuc k) -ᵣ pts' (finj k)  ≤ᵣ δ

 record Sample : Type₀ where
  field
   samples : Fin (1 ℕ.+ len) → ℝ
   pts'≤samples : (k : Fin (1 ℕ.+ len)) → pts' (finj k) ≤ᵣ samples k
   samples≤pts' : (k : Fin (1 ℕ.+ len)) → samples k ≤ᵣ pts' (fsuc k)


  a≤samples : ∀ k → a  ≤ᵣ samples k
  a≤samples k = isTrans≤ᵣ a _ _ (a≤pts' (finj k)) (pts'≤samples k)

  samples≤b : ∀ k → samples k ≤ᵣ b
  samples≤b k = isTrans≤ᵣ (samples k) _ b (samples≤pts' k) (pts'≤b (fsuc k))

  samplesΣ : Fin (1 ℕ.+ len) → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
  samplesΣ k = samples k , a≤samples k , samples≤b k

  riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
  riemannSum f = foldlFin {n = 1 ℕ.+ len}
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
     (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum' : (ℝ → ℝ) → ℝ
  riemannSum' f = foldlFin {n = 1 ℕ.+ len}
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t) ) 0
     (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum'≡ : (f g : ℝ → ℝ) → (∀ x → x ∈ intervalℙ a b → f x ≡ g x) →
                     riemannSum' f ≡ riemannSum' g
  riemannSum'≡ f g f≡g =
    cong (λ g → foldlFin {n = 1 ℕ.+ len}
        g 0)
        (funExt₂ (λ S ((t , a≤t , t≤b) , b-a) →
           cong ((S +ᵣ_) ∘ (b-a ·ᵣ_))
               (f≡g t (a≤t , t≤b))))
         ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum-clamp : (f : ∀ r → r ∈ intervalℙ a b → ℝ)
    → riemannSum (curry ∘ f) ≡
      riemannSum'
      (λ x₁ →  f (clampᵣ a b x₁) (clampᵣ∈intervalℙ a b a≤b x₁))
  riemannSum-clamp f =
    cong (λ g → foldlFin {n = 1 ℕ.+ len}
        g 0)
        (funExt₂ (λ S ((t , a≤t , t≤b) , b-a) →
           cong ((S +ᵣ_) ∘ (b-a ·ᵣ_))
             (cong (uncurry f)
               (Σ≡Prop (∈-isProp (intervalℙ a b))
                (∈ℚintervalℙ→clampᵣ≡ a b t (a≤t , t≤b))))))
         ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum'+ : (f g : ℝ → ℝ) →
    riemannSum' f +ᵣ riemannSum' g
      ≡ riemannSum' (λ x → f x +ᵣ g x)
  riemannSum'+ f g = zip-foldFin+ᵣ' (1 ℕ.+ len)
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
    _ _ 0 0
   ∙ (cong₂ (foldlFin {n = 1 ℕ.+ len}) (funExt₂
    λ S y → cong (S +ᵣ_) (sym (·DistL+ _ _ _)))
   (+ᵣ-rat 0 0)
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))


  riemannSum+ : ∀ f g →
    riemannSum f +ᵣ riemannSum g
      ≡ riemannSum (λ x ≤x x≤  → f x ≤x x≤ +ᵣ g x ≤x x≤)
  riemannSum+ f g = zip-foldFin+ᵣ' (1 ℕ.+ len)
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
    _ _ 0 0
   ∙ (cong₂ (foldlFin {n = 1 ℕ.+ len}) (funExt₂
    λ S y → cong (S +ᵣ_) (sym (·DistL+ _ _ _)))
   (+ᵣ-rat 0 0)
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))

  riemannSum'≤ : (f g : ℝ → ℝ) →
    (∀ r → a ≤ᵣ r → r ≤ᵣ b → f r ≤ᵣ g r) →
    riemannSum' f ≤ᵣ riemannSum' g

  riemannSum'≤ f g f≤g =
     foldFin+≤ (1 ℕ.+ len) _ _ _  _
       (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
       (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
       (≤ᵣ-refl 0) λ x → ≤ᵣ-o·ᵣ _ _ _ (x≤y→0≤y-x _ _ (pts'≤pts' x))
         (f≤g _ (a≤samples x) (samples≤b x))



  riemannSum'C· : ∀ C (f : ℝ → ℝ) →
    riemannSum' (λ x → C ·ᵣ f x)
     ≡ C ·ᵣ riemannSum' f
  riemannSum'C· C f =
    (cong (foldlFin {n = 1 ℕ.+ len}) (funExt₂
    λ S y → cong (S +ᵣ_)
      (·ᵣAssoc _ _ _ ∙∙ cong (_·ᵣ f (y .fst .fst)) (·ᵣComm _ _)
       ∙∙ sym (·ᵣAssoc _ _ _)))
    ≡$ 0
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))
    ∙ foldFin·DistL' (1 ℕ.+ len) _ _
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSumC· : ∀ C f →
    riemannSum (λ x ≤x x≤ → C ·ᵣ f x ≤x x≤)
     ≡ C ·ᵣ riemannSum f
  riemannSumC· C f =
    (cong (foldlFin {n = 1 ℕ.+ len}) (funExt₂
    λ S y → cong (S +ᵣ_)
      (·ᵣAssoc _ _ _ ∙∙ cong (_·ᵣ f (y .fst .fst) _ _) (·ᵣComm _ _)
       ∙∙ sym (·ᵣAssoc _ _ _)))
    ≡$ 0
    ≡$ (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k)))
    ∙ foldFin·DistL' (1 ℕ.+ len) _ _
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))


  riemannSum'- : (f g : ℝ → ℝ) →
    riemannSum' f -ᵣ riemannSum' g
      ≡ riemannSum' (λ x → f x -ᵣ g x)
  riemannSum'- f g =
      cong₂ _+ᵣ_ refl
        (-ᵣ≡[-1·ᵣ] _
         ∙ sym (riemannSum'C· -1 _)
         ∙ cong riemannSum' (funExt λ _ → sym (-ᵣ≡[-1·ᵣ] _)))
    ∙ riemannSum'+ _ _


  riemannSum- : ∀ f g →
    riemannSum f -ᵣ riemannSum g
      ≡ riemannSum (λ x ≤x x≤ → f x ≤x x≤ -ᵣ g x ≤x x≤)
  riemannSum- f g =
      cong₂ _+ᵣ_ refl
        (-ᵣ≡[-1·ᵣ] _
         ∙ sym (riemannSumC· -1 _)
         ∙ cong riemannSum (funExt₃ λ _ _ _ → sym (-ᵣ≡[-1·ᵣ] _)))
    ∙ riemannSum+ _ _



  riemannSum'-alt : (ℝ → ℝ) → ℝ
  riemannSum'-alt f = foldlFin {n = 1 ℕ.+ len}
    (λ S k →
     S +ᵣ (pts' (fsuc k) -ᵣ pts' (finj k)) ·ᵣ (f (fst (samplesΣ k))) ) 0
     (idfun _)

  riemannSum'-alt-lem : ∀ f → riemannSum' f ≡ riemannSum'-alt f
  riemannSum'-alt-lem f =
   foldFin+map (1 ℕ.+ len) 0 _
    (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))
    (idfun _)


  riemannSum-empty : (f : ∀ r → r ∈ intervalℙ a b → ℝ)
    → a ≡ b
    → 0 ≡ riemannSum (curry ∘ f)

  riemannSum-empty f a≡b =
      sym (Rℝ.0RightAnnihilates _)
    ∙ sym (foldFin+Const (1 ℕ.+ len) 0 (idfun _))
    ∙ (cong (foldlFin {n = 1 ℕ.+ len}) (funExt₂
      (λ S y → cong (S +ᵣ_) ((sym (Rℝ.0LeftAnnihilates' _ _
        (Rℝ.+InvR' _ _ (
         cong fst (isContr→isProp (pointIntervalℙ a b a≡b)
          (pts'Σ (fsuc y)) (pts'Σ (finj y))))))))))
       ≡$ 0 ≡$ idfun _)
    ∙ sym (riemannSum'-alt-lem _)
    ∙ sym (riemannSum-clamp f)


  riemannSum'-absᵣ≤ : (f : ℝ → ℝ) →
    absᵣ (riemannSum' f) ≤ᵣ riemannSum' (absᵣ ∘ f)
  riemannSum'-absᵣ≤ f =
    subst2 _≤ᵣ_
      (cong absᵣ (sym (riemannSum'-alt-lem f)))
      (sym (riemannSum'-alt-lem (absᵣ ∘ f)))
      (foldFin+≤-abs (1 ℕ.+ len) 0 0 _ _
        (idfun _) (idfun _)
        (isTrans≡≤ᵣ _ _ _ absᵣ0 (≤ᵣ-refl 0))
        λ k →
          ≡ᵣWeaken≤ᵣ _ _
            (·absᵣ _ _
           ∙ cong₂ _·ᵣ_
             (absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' k)))
             refl))



  riemannSum'Const : ∀ C → riemannSum' (const C) ≡ C ·ᵣ (b -ᵣ a)
  riemannSum'Const C = riemannSum'-alt-lem (const C)
   ∙ (λ i → foldlFin {n = 1 ℕ.+ len}
    (λ S k →
     S +ᵣ ·ᵣComm (pts' (fsuc k) -ᵣ pts' (finj k)) C i ) 0
     (idfun _))
   ∙ foldFin·DistL' (1 ℕ.+ len) _ C (idfun _)
   ∙ cong (C ·ᵣ_) (deltas-sum (1 ℕ.+ len) pts' ∙ cong₂ _-ᵣ_ pts'-last refl)


 open Sample public

 leftSample : Sample
 leftSample .samples = pts' ∘ finj
 leftSample .pts'≤samples = ≤ᵣ-refl ∘ pts' ∘ finj
 leftSample .samples≤pts' = pts'≤pts'

 rightSample : Sample
 rightSample .samples = pts' ∘ fsuc
 rightSample .pts'≤samples = pts'≤pts'
 rightSample .samples≤pts' = ≤ᵣ-refl ∘ pts' ∘ fsuc


open Partition[_,_] public hiding (a≤b)

TaggedPartition[_,_] : ℝ → ℝ → Type
TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample






0≤pos/ : ∀ {p q} → 0 ℚ.≤ [ pos p , q ]
0≤pos/ {p} {q} = ℚ.0≤pos p q

ℚ<→0< : ∀ q → 0 ℚ.< q → ℚ.0< q
ℚ<→0< q q>0 = q>0

_ℚ₊·_ : ℚ₊ → ℚ₊ → ℚ₊
_ℚ₊·_ = _·₊_

half₊ : ℚ₊ → ℚ₊
half₊ ε = ε /2₊

quarter₊ : ℚ₊ → ℚ₊
quarter₊ ε = ε /4₊

x/2<x : ∀ ε → fst (half₊ ε) ℚ.< fst ε
x/2<x = /2₊<id

/4₊≡/2₊/2₊ : ∀ ε → fst (quarter₊ ε) ≡ fst (half₊ (half₊ ε))
/4₊≡/2₊/2₊ ε = refl

x≤y·z→x·invℚ₊y≤z : ∀ x (y : ℚ₊) z →
  x ℚ.≤ z ℚ.· fst y →
  x ℚ.· fst (invℚ₊ y) ℚ.≤ z
x≤y·z→x·invℚ₊y≤z x y z x≤z·y =
  subst2 ℚ._≤_ refl ℚ!
    (ℚ.≤-·o x (z ℚ.· fst y) (fst (invℚ₊ y))
      (ℚ.<Weaken≤ _ _ (snd (invℚ₊ y))) x≤z·y)

x·invℚ₊y≤z→x≤y·z : ∀ x z (y : ℚ₊) →
  x ℚ.· fst (invℚ₊ y) ℚ.≤ z →
  x ℚ.≤ fst y ℚ.· z
x·invℚ₊y≤z→x≤y·z x z y x·1/y≤z =
  subst (x ℚ.≤_) (ℚ.·Comm z (fst y))
    (subst2 ℚ._≤_ ℚ! refl
      (ℚ.≤-·o (x ℚ.· fst (invℚ₊ y)) z (fst y)
        (ℚ.<Weaken≤ _ _ (snd y)) x·1/y≤z))

ε/2+ε/2≡ε : ∀ ε → (ε ℚ.· [ pos 1 , 2 ]) ℚ.+ (ε ℚ.· [ pos 1 , 2 ]) ≡ ε
ε/2+ε/2≡ε ε = ℚ!!

sameDenomSubSucc : ∀ m d →
  (([_/_] (pos (suc m)) d) ℚ.- ([_/_] (pos m) d)) ≡
  ([_/_] (pos (suc m) - pos m) d)
sameDenomSubSucc m d = eq/ _ _ ℤ!

invℚ₊-fromNat : ∀ m → fst (invℚ₊ (fromNat (suc m))) ≡ [ pos 1 / 1+ m ]
invℚ₊-fromNat = ℚ.invℚ₊-fromNat

u+[v-u]≡v : ∀ u v → u +ᵣ (v -ᵣ u) ≡ v
u+[v-u]≡v u v = +ᵣComm u (v -ᵣ u) ∙ Rℝ.minusPlus v u

v-[v-u]≡u : ∀ u v → v -ᵣ (v -ᵣ u) ≡ u
v-[v-u]≡u u v =
  cong (_-ᵣ (v -ᵣ u)) (sym (u+[v-u]≡v u v))
  ∙ Rℝ.plusMinus u (v -ᵣ u)

translatedDiff : ∀ x y α → (x +ᵣ α) -ᵣ (y +ᵣ α) ≡ x -ᵣ y
translatedDiff x y α = ℝ!


-- Previously this was the nested module `Integration`; it only constructs
-- equal partitions, so the new name says what it provides.
module EqualPartition a b (a≤b : a ≤ᵣ b) where

 Δ : ℝ
 Δ = b -ᵣ a

 0≤Δ : 0 ≤ᵣ Δ
 0≤Δ = x≤y→0≤y-x a _ a≤b


 module _ (n : ℕ) where

  t : ℕ → ℚ
  t k = [ pos (suc k) / 1+ n  ]

  0≤t : ∀ k → 0 ≤ᵣ rat (t k)
  0≤t k = ≤ℚ→≤ᵣ 0 (t k) (0≤pos/ {suc k} {1+ n})

  t≤1 : ∀ (k : Fin n) → rat (t (fst k)) ≤ᵣ 1
  t≤1 k = ≤ℚ→≤ᵣ (t (fst k)) 1 (ℚ.inj w)
   where
   w : pos (suc (k .fst)) ℤ.· ℤ.ℕ₊₁→ℤ 1 ℤ.≤ pos 1 ℤ.· ℤ.ℕ₊₁→ℤ (1+ n)
   w = subst2 ℤ._≤_ (sym (ℤ.·IdR _)) (sym (ℤ.·IdL _))
         (ℤ.ℕ≤→pos-≤-pos (suc (fst k))
          _ (ℕ.≤-suc (ℕᵗ.<ᵗ→< (snd k))))

  tIncr : ∀ k → t k ℚ.≤ t (suc k)
  tIncr k = ℚ.inj
    (ℤ.≤-·o {m = pos (suc k)} {n = pos (suc (suc k))} {k = suc n}
      (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-sucℕ))

  equalPartition : Partition[ a , b ]
  equalPartition .len = n
  equalPartition .pts k = a +ᵣ Δ ·ᵣ (rat (t (fst k)))
  equalPartition .endpoints≤ = a≤b
  equalPartition .a≤pts k =
    isTrans≡≤ᵣ a (a +ᵣ Δ ·ᵣ 0) _
      (sym (Rℝ.+IdR' _ _ (Rℝ.0RightAnnihilates _)))
       (≤ᵣ-o+ (Δ ·ᵣ 0) (Δ ·ᵣ (rat (t (fst k)))) a
         (≤ᵣ-o·ᵣ 0 (rat (t (fst k))) Δ  0≤Δ (0≤t (fst k))))
  equalPartition .pts≤b k =
    isTrans≤≡ᵣ (a +ᵣ Δ ·ᵣ rat (t (fst k))) (a +ᵣ Δ) b
    (≤ᵣ-o+ _ _ a
     (isTrans≤≡ᵣ (Δ ·ᵣ rat (t (fst k))) (Δ ·ᵣ 1) Δ
      (≤ᵣ-o·ᵣ (rat (t (fst k))) 1 Δ  0≤Δ (t≤1 k)) (·IdR Δ)))
      (ℝ!)
  equalPartition .pts≤pts k =
     subst2 _≤ᵣ_
       (sym (cong (λ j → a +ᵣ Δ ·ᵣ rat (t j))
         (toℕ-finj-pred {n = n} k)))
       (sym (cong (λ j → a +ᵣ Δ ·ᵣ rat (t j))
         (toℕ-fsuc-pred {n = n} k)))
       (≤ᵣ-o+ _ _ a
         (≤ᵣ-o·ᵣ (rat (t (fst k))) (rat (t (suc (fst k)))) Δ 0≤Δ
           (≤ℚ→≤ᵣ (t (fst k)) _ (tIncr (fst k)))))


  equalPartitionPts' : ∀ k → pts' equalPartition k ≡
        a +ᵣ Δ ·ᵣ rat [ pos (fst k) / 1+ n  ]
  equalPartitionPts' (zero , p) =
   sym (Rℝ.+IdR' _ _ (Rℝ.0RightAnnihilates' _ _ (cong rat (ℚ.[0/n]≡[0/m] _ _))))
  equalPartitionPts' k'@(suc k , p) =
    ℕᵗ.split<ᵗ-suc-elim {k = k} {len = n}
      {C = pts' equalPartition k' ≡
           a +ᵣ Δ ·ᵣ rat [ pos (fst k') / 1+ n ]}
      p
      (λ k<n →
        let j : Fin n
            j = k , k<n
            k'≡mid : k' ≡ fsuc (finj j)
            k'≡mid = toℕ-injective {k = 2 ℕ.+ n} refl
        in cong (pts' equalPartition) k'≡mid
           ∙ pts'-mid equalPartition j)
      (λ k≡n →
        let k'≡last : k' ≡ flast {k = 1 ℕ.+ n}
            k'≡last = toℕ-injective {k = 2 ℕ.+ n} (cong suc k≡n)
            frac≡1 : rat [ pos (suc k) / 1+ n ] ≡ 1
            frac≡1 =
              cong (rat ∘ [_/ 1+ n ]) (cong (pos ∘ suc) k≡n)
              ∙ cong rat (ℚ.[n/n]≡[m/m] n 0)
            lastEq : b ≡ a +ᵣ Δ ·ᵣ rat [ pos (suc k) / 1+ n ]
            lastEq =
              sym (cong (a +ᵣ_) (cong (Δ ·ᵣ_) frac≡1 ∙ ·IdR Δ)
                   ∙ u+[v-u]≡v a b)
        in cong (pts' equalPartition) k'≡last
           ∙ pts'-last equalPartition
           ∙ lastEq)

  equalPartitionΔ : ∀ k →
    pts' equalPartition (fsuc k) -ᵣ pts' equalPartition (finj k)
    ≡ Δ ·ᵣ rat [ 1 / 1+ n ]
  equalPartitionΔ k =
    cong₂ _-ᵣ_ (equalPartitionPts' (fsuc k)) (equalPartitionPts' (finj k))
    ∙ ℝ!
    ∙ sym (Rℝ.·DistR- _ _ _)
    ∙ cong (Δ ·ᵣ_) zz
    where
    zz : rat [ pos (suc (fst k)) / 1+ n ] -ᵣ rat [ pos (fst k) / 1+ n ]
       ≡ rat [ 1 / 1+ n ]
    zz =
      -ᵣ-rat₂ ([ pos (suc (fst k)) / 1+ n ]) ([ pos (fst k) / 1+ n ])
      ∙ cong rat
          (sameDenomSubSucc (fst k) (1+ n) ∙
            cong [_/ 1+ n ]
              (cong (ℤ._- pos (fst k)) (ℤ.pos+ 1 (fst k))
               ∙ ℤ.plusMinus (pos (fst k)) 1))

 isStrictEqualPartition : a <ᵣ b → ∀ n → isStrictPartition (equalPartition n)
 isStrictEqualPartition a<b n k =
   subst2 _<ᵣ_
     (sym (equalPartitionPts' n (finj k)))
     (sym (equalPartitionPts' n (fsuc k)))
     (<ᵣ-o+ _ _ a
       (<ᵣ-o·ᵣ _ _
         (Δ , x<y→0<y-x _ _ a<b)
         (<ℚ→<ᵣ _ _ (([k/n]<[k'/n]
          (pos (fst k)) (pos (suc (fst k))) (1+ n)
            (ℤ.ℕ<→pos-<-pos (fst k) (suc (fst k)) ℕ.<-suc))))))

 equalPartition-2ⁿ : ℕ → Partition[ a , b ]
 equalPartition-2ⁿ n = equalPartition (predℕ (2^ (suc n)))

 equalPartition-mesh : ∀ n →
  mesh≤ᵣ (equalPartition n)
   ((b -ᵣ a) ·ᵣ (rat [ 1 / 1+ n  ]) )
 equalPartition-mesh n k = ≡ᵣWeaken≤ᵣ _ _
  (equalPartitionΔ n k)

∃Partition< : ∀ a b → a ≤ᵣ b → ∀ (ε : ℚ₊) →
  ∃[ (p , tg) ∈ TaggedPartition[ a , b ] ] mesh≤ᵣ p (rat (fst ε))
∃Partition< a b a≤b ε =
  PT.map
    (λ (x' , b-a<x' , _) →
      let x'₊ = (x' , ℚ<→0< x'
                (<ᵣ→<ℚ 0 x' (isTrans≤<ᵣ 0 (b -ᵣ a) (rat x')
                  (x≤y→0≤y-x a b a≤b) b-a<x')))
          (1+ N , p) = ℚ.ceilℚ₊ (invℚ₊ ε ℚ₊· x'₊)
          ww : fst (x'₊ ℚ₊· invℚ₊ ε) ℚ.≤ fromNat (suc N)
          ww = ℚ.<Weaken≤ _ _
            (subst (ℚ._< fromNat (suc N))
              (ℚ.·Comm (fst (invℚ₊ ε)) x') p)

      in (_ , leftSample (∫ab.equalPartition N)) ,
          λ k → isTrans≤ᵣ _ _ _ (∫ab.equalPartition-mesh N k)
            (isTrans≤ᵣ _ _ _
              (isTrans≤≡ᵣ _ _ _ (≤ᵣ-·ᵣo _ _ _ (≤ℚ→≤ᵣ _ _ (ℚ.0≤pos 1 (1+ N)))
                (<ᵣWeaken≤ᵣ _ _ b-a<x'))
                (sym (rat·ᵣrat x' _)))
              (let N₂ : ℚ₊
                   N₂ = fromNat (suc N)
                   x'≤ε·N₂ : x' ℚ.≤ fst ε ℚ.· fst N₂
                   x'≤ε·N₂ = x·invℚ₊y≤z→x≤y·z x' (fst N₂) ε ww
                   x'·invN₂≤ε : x' ℚ.· fst (invℚ₊ N₂) ℚ.≤ fst ε
                   x'·invN₂≤ε = x≤y·z→x·invℚ₊y≤z x' N₂ (fst ε) x'≤ε·N₂
               in ≤ℚ→≤ᵣ _ _
                 (subst (λ q → x' ℚ.· q ℚ.≤ fst ε)
                   (invℚ₊-fromNat N)
                   x'·invN₂≤ε)))
      )
    (denseℚinℝ (b -ᵣ a) ((b -ᵣ a) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 (b -ᵣ a) decℚ<ᵣ?)))
 where
 module ∫ab = EqualPartition a b a≤b

module Partition-pre+ (a b : ℝ) (α : ℝ) where
 partition-pre+P : Partition[ a , b ] → Partition[ a +ᵣ α , b +ᵣ α ]
 partition-pre+P x .len = x .len
 partition-pre+P x .pts = (_+ᵣ α) ∘ x .pts
 partition-pre+P x .endpoints≤ =
   ≤ᵣ-+o _ _ _ (Partition[_,_].endpoints≤ x)
 partition-pre+P x .a≤pts =
   ≤ᵣ-+o _ _ _ ∘ x .a≤pts
 partition-pre+P x .pts≤b =
    ≤ᵣ-+o _ _ _ ∘ x .pts≤b
 partition-pre+P x .pts≤pts k =
     ≤ᵣ-+o _ _ _ (x .pts≤pts k)

 partition-pre+-pts' : ∀ p k → pts' (partition-pre+P p) k ≡ pts' p k +ᵣ α
 partition-pre+-pts' p (zero , _) = refl
 partition-pre+-pts' p k'@(suc k , q) =
   ℕᵗ.split<ᵗ-suc-elim {k = k} {len = p .len}
     {C = pts' (partition-pre+P p) k' ≡ pts' p k' +ᵣ α}
     q
     (λ k<slen →
       let j : Fin (p .len)
           j = k , k<slen
           k'≡mid : k' ≡ fsuc (finj j)
           k'≡mid = toℕ-injective {k = 2 ℕ.+ p .len} refl
           preMid : pts' (partition-pre+P p) k' ≡ pts (partition-pre+P p) j
           preMid = cong (pts' (partition-pre+P p)) k'≡mid
                    ∙ pts'-mid (partition-pre+P p) j
           pMid : pts' p k' ≡ pts p j
           pMid = cong (pts' p) k'≡mid ∙ pts'-mid p j
       in preMid ∙ cong (_+ᵣ α) (sym pMid))
     (λ k≡slen →
       let k'≡last : k' ≡ flast {k = 1 ℕ.+ p .len}
           k'≡last = toℕ-injective {k = 2 ℕ.+ p .len} (cong suc k≡slen)
           preLast : pts' (partition-pre+P p) k' ≡ b +ᵣ α
           preLast = cong (pts' (partition-pre+P p)) k'≡last
                     ∙ pts'-last (partition-pre+P p)
           pLast : pts' p k' ≡ b
           pLast = cong (pts' p) k'≡last ∙ pts'-last p
       in preLast ∙ cong (_+ᵣ α) (sym pLast))

 partition-pre+ :
    ( (TaggedPartition[ a , b ]))
    → ((TaggedPartition[ a +ᵣ α , b +ᵣ α ]))
 partition-pre+  x .fst = partition-pre+P (x .fst)
 partition-pre+  x  .snd .samples =
  (_+ᵣ α) ∘  x  .snd .samples
 partition-pre+  x .snd .pts'≤samples =
   λ k → subst2 _≤ᵣ_
     (sym (partition-pre+-pts' (x .fst) (finj k)))
     refl
     (≤ᵣ-+o _ _ α (x .snd .pts'≤samples k))


 partition-pre+  x .snd .samples≤pts' =
   λ k → subst2 _≤ᵣ_
     refl
     (sym (partition-pre+-pts' (x .fst) (fsuc k)))
     (≤ᵣ-+o _ _ α (x .snd .samples≤pts' k))

 partition-pre+-lem : ∀ tp k →
      pts' (fst (partition-pre+ tp)) (fsuc k) -ᵣ
      pts' (fst (partition-pre+ tp)) (finj k)
      ≡
      (pts' (fst tp) (fsuc k)) -ᵣ (pts' (fst tp) (finj k))
 partition-pre+-lem tp k =
   cong₂ _-ᵣ_
     (partition-pre+-pts' (fst tp) (fsuc k))
     (partition-pre+-pts' (fst tp) (finj k))
   ∙ translatedDiff (pts' (fst tp) (fsuc k)) (pts' (fst tp) (finj k)) α

 mesh-pre+ : ∀ δ → (tp : TaggedPartition[ a , b ]) →
             mesh≤ᵣ (fst tp) δ
            → mesh≤ᵣ (fst (partition-pre+ tp)) δ
 mesh-pre+ δ tp x k =
   isTrans≡≤ᵣ _ _ _ (partition-pre+-lem tp k) (x k)


pts'-tranp : ∀ {a a' b b'} → (p : a ≡ a') (p' : b ≡ b') →
 ((pa , tg) : TaggedPartition[ a , b ]) →
 ∀ k k' → fst k ≡ fst k' →
 pts' pa k ≡ pts' (fst (subst2 TaggedPartition[_,_] p p' (pa , tg))) k'
pts'-tranp {a} {a'} {b} {b'} p p' =
 J2 (λ a' p b' p' →
              ((pa , tg) : TaggedPartition[ a , b ]) →
            ∀ k k' → fst k ≡ fst k' →
            pts' pa k ≡
            pts' (fst (subst2 TaggedPartition[_,_] p p' (pa , tg))) k' )
         (λ (pa , tg) k k' pp i →
           fst (pts'Σ (transportRefl pa (~ i))
             (toℕ-injective {suc (suc (len pa))}
               {k} {k'} pp i)))
           {a'} p {b'} p'

module Partition-pre· (a b : ℝ) (α : ℝ) (0≤α : 0 ≤ᵣ α) where
 partition-pre·P : Partition[ a , b ] → Partition[ a ·ᵣ α , b ·ᵣ α ]
 partition-pre·P x .len = x .len
 partition-pre·P x .pts = (_·ᵣ α) ∘ x .pts
 partition-pre·P x .endpoints≤ =
   ≤ᵣ-·ᵣo _ _ _ 0≤α (Partition[_,_].endpoints≤ x)
 partition-pre·P x .a≤pts =
   ≤ᵣ-·ᵣo _ _ _ 0≤α ∘ x .a≤pts
 partition-pre·P x .pts≤b =
    ≤ᵣ-·ᵣo _ _ _ 0≤α ∘ x .pts≤b
 partition-pre·P x .pts≤pts k =
     ≤ᵣ-·ᵣo _ _ _ 0≤α (x .pts≤pts k)

 partition-pre·P-pts' : ∀ p k → pts' (partition-pre·P p) k ≡ pts' p k ·ᵣ α
 partition-pre·P-pts' p (zero , _) = refl
 partition-pre·P-pts' p k'@(suc k , q) =
   ℕᵗ.split<ᵗ-suc-elim {k = k} {len = p .len}
     {C = pts' (partition-pre·P p) k' ≡ pts' p k' ·ᵣ α}
     q
     (λ k<slen →
       let j : Fin (p .len)
           j = k , k<slen
           k'≡mid : k' ≡ fsuc (finj j)
           k'≡mid = toℕ-injective {k = 2 ℕ.+ p .len} refl
           preMid : pts' (partition-pre·P p) k' ≡ pts (partition-pre·P p) j
           preMid = cong (pts' (partition-pre·P p)) k'≡mid
                    ∙ pts'-mid (partition-pre·P p) j
           pMid : pts' p k' ≡ pts p j
           pMid = cong (pts' p) k'≡mid ∙ pts'-mid p j
       in preMid ∙ cong (_·ᵣ α) (sym pMid))
     (λ k≡slen →
       let k'≡last : k' ≡ flast {k = 1 ℕ.+ p .len}
           k'≡last = toℕ-injective {k = 2 ℕ.+ p .len} (cong suc k≡slen)
           preLast : pts' (partition-pre·P p) k' ≡ b ·ᵣ α
           preLast = cong (pts' (partition-pre·P p)) k'≡last
                     ∙ pts'-last (partition-pre·P p)
           pLast : pts' p k' ≡ b
           pLast = cong (pts' p) k'≡last ∙ pts'-last p
       in preLast ∙ cong (_·ᵣ α) (sym pLast))

 partition-pre· :
    ( (TaggedPartition[ a , b ]))
    → ((TaggedPartition[ a ·ᵣ α , b ·ᵣ α ]))
 partition-pre·  x .fst = partition-pre·P (x .fst)
 partition-pre·  x  .snd .samples =
  (_·ᵣ α) ∘  x  .snd .samples
 partition-pre·  x .snd .pts'≤samples =
  λ k → subst2 _≤ᵣ_
    (sym (partition-pre·P-pts' (x .fst) (finj k)))
    refl
    (≤ᵣ-·ᵣo _ _ α 0≤α (x .snd .pts'≤samples k))

 partition-pre·  x .snd .samples≤pts' =
  λ k → subst2 _≤ᵣ_
    refl
    (sym (partition-pre·P-pts' (x .fst) (fsuc k)))
    (≤ᵣ-·ᵣo _ _ α 0≤α (x .snd .samples≤pts' k))

 partition-pre·-pts' : ∀ tp k →
      pts' (fst (partition-pre· tp)) k ≡ pts' (fst tp) k ·ᵣ α
 partition-pre·-pts' tp k = partition-pre·P-pts' (fst tp) k

 partition-pre·-lem : ∀ tp k →
      pts' (fst (partition-pre· tp)) (fsuc k) -ᵣ
      pts' (fst (partition-pre· tp)) (finj k)
      ≡
      pts' (fst tp) (fsuc k) ·ᵣ α -ᵣ pts' (fst tp) (finj k) ·ᵣ α
 partition-pre·-lem tp k =
   cong₂ _-ᵣ_ (partition-pre·-pts' tp (fsuc k)) (partition-pre·-pts' tp (finj k))

 mesh-pre· : ∀ δ → (tp : TaggedPartition[ a , b ]) →
             mesh≤ᵣ (fst tp) δ
            → mesh≤ᵣ (fst (partition-pre· tp)) (δ ·ᵣ α)
 mesh-pre· δ tp x k =
   isTrans≡≤ᵣ _ _ _
     (partition-pre·-lem tp k ∙ sym (Rℝ.·DistL- _ _ _))
     (≤ᵣ-·ᵣo _ _ _ 0≤α
      (x k))

opaque
 unfolding _+ᵣ_ maxᵣ

 clamp-Δ-·f : ∀ a b → a ≤ᵣ b → ∀ f
       → IsContinuous f
       → ∀ (δ : ℚ₊)
       → ∀ u v → u ≤ᵣ v
       → v -ᵣ u ≤ᵣ rat (fst δ)
       → ∀ x → x ∈ intervalℙ u v
       → (clampᵣ a b v -ᵣ clampᵣ a b u) ·ᵣ f x
         ≡ (clampᵣ a b v -ᵣ clampᵣ a b u)
           ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) (b +ᵣ rat (fst δ)) x)
 clamp-Δ-·f a b a≤b f cf δ u v u≤v v∼u x x∈ =
   sym (λ i → (clampᵣ a (b* i) (v* i) -ᵣ clampᵣ a (b* i) u) ·ᵣ f (x* i))
   ∙∙
   hhh'' a b u v x
   ∙∙
   λ i → (clampᵣ a (b* i) (v* i) -ᵣ clampᵣ a (b* i) u) ·ᵣ
      f (clampᵣ (a -ᵣ δ* i) ((b* i) +ᵣ δ* i) (x* i))


   where
   b* v* x* δ* : I → ℝ
   b* i = ≤→maxᵣ a b a≤b i
   v* i = ≤→maxᵣ u v u≤v i
   x* i = ((cong (clampᵣ u) (λ i → v* i) ≡$ x) ∙ sym (∈ℚintervalℙ→clampᵣ≡ u v x x∈)
               ) i
   δ* i = ((λ i → maxᵣ (v* i -ᵣ u) (rat (fst δ)))
        ∙ ≤→maxᵣ  (v -ᵣ u) (rat (fst δ)) v∼u) i

   fL : ℝ → ℝ → ℝ → ℝ → ℝ
   fL a b u v = clampᵣ a (maxᵣ a b) (maxᵣ u v) -ᵣ clampᵣ a (maxᵣ a b) u

   fLC : ∀ a b → IsContinuous₂ (fL a b)
   fLC a b = IsContinuous-₂∘
     (cont∘₂ (IsContinuousClamp a (maxᵣ a b)) (contNE₂ maxR))
    (cont∘₂ (IsContinuousClamp a (maxᵣ a b)) cont₂-fst)

   fLC' : ∀ u v → IsContinuous₂ (λ a b → fL a b u v)
   fLC' u v = IsContinuous-₂∘
     (IsContinuousClamp₂∘ (maxᵣ u v) cont₂-fst (contNE₂ maxR))
    (IsContinuousClamp₂∘ u cont₂-fst (contNE₂ maxR))

   f₀ f₁ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
   f₀ a b u v x = fL a b u v ·ᵣ f (clampᵣ u (maxᵣ u v) x)
   f₁ a b u v x = fL a b u v ·ᵣ
      f (clampᵣ (a -ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
       ((maxᵣ a b) +ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
       ((clampᵣ u (maxᵣ u v) x)))

   f₀C : ∀ a b x → IsContinuous₂ (λ u v → f₀ a b u v x)
   f₀C a b x = cont₂·₂ᵣ (fLC a b)
     (cont∘₂ cf (IsContinuousClamp₂∘ x
       cont₂-fst (contNE₂ maxR)))
   f₁C : ∀ a b x → IsContinuous₂ (λ u v → f₁ a b u v x)
   f₁C a b x = cont₂·₂ᵣ (fLC a b) (cont∘₂ cf
      (IsContinuousClamp₂∘'
        (IsContinuous-₂∘ (cont₂-id a)
          (contNE₂∘ maxR
            (IsContinuous-₂∘ (contNE₂ maxR) cont₂-fst) (cont₂-id _)))
        ((contNE₂∘ sumR (cont₂-id (maxᵣ a b))
          (contNE₂∘ maxR
            (IsContinuous-₂∘ (contNE₂ maxR) cont₂-fst) (cont₂-id _))))
        (IsContinuousClamp₂∘ x cont₂-fst (contNE₂ maxR))))

   f₀C' : ∀ u v x → IsContinuous₂ (λ a b → f₀ a b u v x)
   f₀C' u v x = cont∘₂ (IsContinuous·ᵣR _) (fLC' u v)
   f₁C' : ∀ u v x → IsContinuous₂ (λ a b → f₁ a b u v x)
   f₁C' u v x = cont₂·₂ᵣ (fLC' u v)
      (cont∘₂ cf (IsContinuousClamp₂∘ (clampᵣ u (maxᵣ u v) x)
        (cont∘₂ (IsContinuous+ᵣR (-ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ)))))
          cont₂-fst)
        ((cont∘₂ (IsContinuous+ᵣR (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
          (contNE₂ maxR)))))

   f₀C'' : ∀ a b u v → IsContinuous (f₀ a b u v)
   f₀C'' a b u v = IsContinuous∘ _ _ (IsContinuous·ᵣL _)
     (IsContinuous∘ _ _ cf (IsContinuousClamp u (maxᵣ u v)))
   f₁C'' : ∀ a b u v → IsContinuous (f₁ a b u v)
   f₁C'' a b u v = IsContinuous∘ _ _ (IsContinuous·ᵣL _)
     (IsContinuous∘ _ _ cf
       (IsContinuous∘ _ _
        (IsContinuousClamp
          (a -ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ))))
          ((maxᵣ a b) +ᵣ (maxᵣ (maxᵣ u v -ᵣ u) (rat (fst δ)))))
        (IsContinuousClamp u (maxᵣ u v))))


   hhh : ∀ a b → a ℚ.≤ b
       → ∀ u v → u ℚ.≤ v
       → ∀ δ
       → rat v -ᵣ rat u ≤ᵣ rat δ
       → ∀ x → x ∈ ℚ.ℚintervalℙ u v

       → (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u)) ·ᵣ f (rat x)
         ≡ (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u))
           ·ᵣ f (clampᵣ (rat a -ᵣ rat δ) (rat b +ᵣ rat δ) (rat x))
   hhh a b a≤b u v u≤v δ v-u≤δ x (≤x , x≤) = ⊎.rec
        (λ p →
         let q : clampᵣ (rat a) (rat b) (rat v)
                 -ᵣ clampᵣ (rat a) (rat b) (rat u) ≡ 0
             q = cong₂ _-ᵣ_ (clampᵣ-rat a b v) (clampᵣ-rat a b u)
                   ∙ -ᵣ-rat₂ (ℚ.clamp a b v) (ℚ.clamp a b u)  ∙ cong rat p
         in (Rℝ.0LeftAnnihilates'
               (clampᵣ (rat a) (rat b) (rat v)
                 -ᵣ clampᵣ (rat a) (rat b) (rat u)) (f (rat x)) q)
          ∙ sym (Rℝ.0LeftAnnihilates'
              (clampᵣ (rat a) (rat b) (rat v)
                 -ᵣ clampᵣ (rat a) (rat b) (rat u))
                  (f (clampᵣ (rat a -ᵣ rat (δ)) (rat b +ᵣ rat δ) (rat x))) q))
                  (λ (a≤v , u≤b) →
                     cong ( (clampᵣ (rat a) (rat b) (rat v) -ᵣ clampᵣ (rat a) (rat b) (rat u)) ·ᵣ_)
                        (cong f
                          (∈ℚintervalℙ→clampᵣ≡ (rat a -ᵣ rat δ) (rat b +ᵣ rat δ) (rat x)
                           (isTrans≤ᵣ _ _ _
                              (isTrans≤≡ᵣ _ _ _
                                (≤ᵣMonotone+ᵣ _ _ _ _
                                  (≤ℚ→≤ᵣ a _ a≤v) (-ᵣ≤ᵣ _ _ v-u≤δ) )
                                (v-[v-u]≡u (rat u) (rat v)))
                              (≤ℚ→≤ᵣ u _ ≤x)
                           , isTrans≤ᵣ _ _ _
                                (≤ℚ→≤ᵣ _ v x≤)
                                (isTrans≡≤ᵣ _ _ _
                                  (sym (u+[v-u]≡v (rat u) (rat v)))
                                  (≤ᵣMonotone+ᵣ _ _ _ _
                                   (≤ℚ→≤ᵣ u _ u≤b) v-u≤δ))))))
                  (clampCases a b a≤b u v u≤v)

   hhh' : ∀ (a b u v x : ℚ) → f₀ (rat a) (rat b) (rat u) (rat v) (rat x)
                 ≡
               f₁ (rat a) (rat b) (rat u) (rat v) (rat x)
   hhh' a b u v x =
     leftEq ∙ core ∙ sym rightEq
    where
    maxab maxuv δq clampuv : ℚ
    maxab = ℚ.max a b
    maxuv = ℚ.max u v
    δq = ℚ.max (maxuv ℚ.- u) (fst δ)
    clampuv = ℚ.clamp u maxuv x

    maxabᵣ : maxᵣ (rat a) (rat b) ≡ rat maxab
    maxabᵣ = maxᵣ-rat a b

    maxuvᵣ : maxᵣ (rat u) (rat v) ≡ rat maxuv
    maxuvᵣ = maxᵣ-rat u v

    δqᵣ : maxᵣ (maxᵣ (rat u) (rat v) -ᵣ rat u) (rat (fst δ)) ≡ rat δq
    δqᵣ =
      cong₂ maxᵣ
        (cong (_-ᵣ rat u) maxuvᵣ ∙ -ᵣ-rat₂ maxuv u)
        refl
      ∙ maxᵣ-rat (maxuv ℚ.- u) (fst δ)

    clampuvᵣ : clampᵣ (rat u) (maxᵣ (rat u) (rat v)) (rat x) ≡ rat clampuv
    clampuvᵣ =
      cong (λ z → clampᵣ (rat u) z (rat x)) maxuvᵣ
      ∙ clampᵣ-rat u maxuv x

    coeffEq : fL (rat a) (rat b) (rat u) (rat v) ≡
      clampᵣ (rat a) (rat maxab) (rat maxuv) -ᵣ clampᵣ (rat a) (rat maxab) (rat u)
    coeffEq =
      cong₂ _-ᵣ_
        (cong₂ (clampᵣ (rat a)) maxabᵣ maxuvᵣ)
        (cong (λ z → clampᵣ (rat a) z (rat u)) maxabᵣ)

    lowerEq : rat a -ᵣ maxᵣ (maxᵣ (rat u) (rat v) -ᵣ rat u) (rat (fst δ))
            ≡ rat a -ᵣ rat δq
    lowerEq = cong (λ z → rat a -ᵣ z) δqᵣ

    upperEq : maxᵣ (rat a) (rat b) +ᵣ
              maxᵣ (maxᵣ (rat u) (rat v) -ᵣ rat u) (rat (fst δ))
            ≡ rat maxab +ᵣ rat δq
    upperEq = cong₂ _+ᵣ_ maxabᵣ δqᵣ

    argEq : clampᵣ (rat a -ᵣ maxᵣ (maxᵣ (rat u) (rat v) -ᵣ rat u) (rat (fst δ)))
                    (maxᵣ (rat a) (rat b) +ᵣ
                     maxᵣ (maxᵣ (rat u) (rat v) -ᵣ rat u) (rat (fst δ)))
                    (clampᵣ (rat u) (maxᵣ (rat u) (rat v)) (rat x))
          ≡ clampᵣ (rat a -ᵣ rat δq) (rat maxab +ᵣ rat δq) (rat clampuv)
    argEq i = clampᵣ (lowerEq i) (upperEq i) (clampuvᵣ i)

    leftEq : f₀ (rat a) (rat b) (rat u) (rat v) (rat x) ≡
      (clampᵣ (rat a) (rat maxab) (rat maxuv) -ᵣ clampᵣ (rat a) (rat maxab) (rat u))
      ·ᵣ f (rat clampuv)
    leftEq = cong₂ _·ᵣ_ coeffEq (cong f clampuvᵣ)

    rightEq : f₁ (rat a) (rat b) (rat u) (rat v) (rat x) ≡
      (clampᵣ (rat a) (rat maxab) (rat maxuv) -ᵣ clampᵣ (rat a) (rat maxab) (rat u))
      ·ᵣ f (clampᵣ (rat a -ᵣ rat δq) (rat maxab +ᵣ rat δq) (rat clampuv))
    rightEq = cong₂ _·ᵣ_ coeffEq (cong f argEq)

    core :
      (clampᵣ (rat a) (rat maxab) (rat maxuv) -ᵣ clampᵣ (rat a) (rat maxab) (rat u))
      ·ᵣ f (rat clampuv)
      ≡
      (clampᵣ (rat a) (rat maxab) (rat maxuv) -ᵣ clampᵣ (rat a) (rat maxab) (rat u))
      ·ᵣ f (clampᵣ (rat a -ᵣ rat δq) (rat maxab +ᵣ rat δq) (rat clampuv))
    core =
      hhh a maxab (ℚ.≤max a b) u maxuv (ℚ.≤max u v) δq
        (isTrans≡≤ᵣ _ _ _
          (-ᵣ-rat₂ maxuv u)
          (≤ℚ→≤ᵣ (maxuv ℚ.- u) δq (ℚ.≤max (maxuv ℚ.- u) (fst δ))))
        clampuv
        (ℚ.clam∈ℚintervalℙ u maxuv (ℚ.≤max u v) x)

   hhh'' : ∀ (a b u v x : ℝ) → f₀ a b u v x ≡ f₁ a b u v x
   hhh'' a b u v x =
     ≡Cont₂ (f₀C a b x) (f₁C a b x)
       (λ uℚ vℚ → let u = rat uℚ ; v = rat vℚ in
         ≡Cont₂ (f₀C' u v x) (f₁C' u v x)
          (λ aℚ bℚ → let a = rat aℚ ; b = rat bℚ in
           ≡Continuous (f₀ a b u v) (f₁ a b u v)
            (f₀C'' a b u v) (f₁C'' a b u v)
             (hhh' aℚ bℚ uℚ vℚ) x)
          a b)
       u v



opaque
 unfolding maxᵣ
 clamp-interval-Δ-swap : ∀ a b a' b'
            → a  ≤ᵣ b
            → a' ≤ᵣ b'
                  → clampᵣ a  b  b' -ᵣ clampᵣ a  b  a'
                  ≡ clampᵣ a' b' b  -ᵣ clampᵣ a' b' a
 clamp-interval-Δ-swap a b a' b' a≤b a'≤b' =
   lhsEq ∙ f-sym a b a' b' ∙ rhsEq



  where

  f : ℝ → ℝ → ℝ → ℝ → ℝ
  f a b a' b' = clampᵣ a (maxᵣ a b) (maxᵣ a' b') -ᵣ clampᵣ a (maxᵣ a b) a'

  lhsEq : clampᵣ a b b' -ᵣ clampᵣ a b a' ≡ f a b a' b'
  lhsEq =
    cong₂ _-ᵣ_
      (cong₂ (clampᵣ a) (sym (≤→maxᵣ a b a≤b)) (sym (≤→maxᵣ a' b' a'≤b')))
      (cong (λ z → clampᵣ a z a') (sym (≤→maxᵣ a b a≤b)))

  rhsEq : f a' b' a b ≡ clampᵣ a' b' b -ᵣ clampᵣ a' b' a
  rhsEq =
    cong₂ _-ᵣ_
      (cong₂ (clampᵣ a') (≤→maxᵣ a' b' a'≤b') (≤→maxᵣ a b a≤b))
      (cong (λ z → clampᵣ a' z a) (≤→maxᵣ a' b' a'≤b'))

  fC : ∀ a b → IsContinuous₂ (f a b)
  fC a b = IsContinuous-₂∘
     (cont∘₂ (IsContinuousClamp a (maxᵣ a b)) (contNE₂ maxR))
     (cont∘₂ (IsContinuousClamp a (maxᵣ a b))
      ((λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)))

  fC' : ∀ a b → IsContinuous₂ (λ a' b' → f a' b' a b)
  fC' a' b' = IsContinuous-₂∘
     (IsContinuousClamp₂∘ (maxᵣ a' b')
      (((λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)))
      (contNE₂ maxR))
     (IsContinuousClamp₂∘ a'
      ((λ _ → IsContinuousConst _) ,  (λ _ → IsContinuousId)) (contNE₂ maxR))

  fℚ-sym : ∀ a b a' b' → f (rat a) (rat b) (rat a') (rat b') ≡
                              f (rat a') (rat b') (rat a) (rat b)
  fℚ-sym a b a' b' = lhsℚ ∙ midℚ ∙ sym rhsℚ
   where
   lhsℚ : f (rat a) (rat b) (rat a') (rat b') ≡
     rat (ℚ.clamp a (ℚ.max a b) (ℚ.max a' b') ℚ.-
          ℚ.clamp a (ℚ.max a b) a')
   lhsℚ =
     cong₂ _-ᵣ_
       (cong₂ (clampᵣ (rat a)) (maxᵣ-rat a b) (maxᵣ-rat a' b')
        ∙ clampᵣ-rat a (ℚ.max a b) (ℚ.max a' b'))
       (cong (λ z → clampᵣ (rat a) z (rat a')) (maxᵣ-rat a b)
        ∙ clampᵣ-rat a (ℚ.max a b) a')
     ∙ -ᵣ-rat₂ (ℚ.clamp a (ℚ.max a b) (ℚ.max a' b'))
               (ℚ.clamp a (ℚ.max a b) a')

   midℚ : rat (ℚ.clamp a (ℚ.max a b) (ℚ.max a' b') ℚ.-
               ℚ.clamp a (ℚ.max a b) a') ≡
          rat (ℚ.clamp a' (ℚ.max a' b') (ℚ.max a b) ℚ.-
               ℚ.clamp a' (ℚ.max a' b') a)
   midℚ =
     cong rat
       (ℚclampInterval-delta a (ℚ.max a b) a' (ℚ.max a' b')
         (ℚ.≤max a b) (ℚ.≤max a' b'))

   rhsℚ : f (rat a') (rat b') (rat a) (rat b) ≡
     rat (ℚ.clamp a' (ℚ.max a' b') (ℚ.max a b) ℚ.-
          ℚ.clamp a' (ℚ.max a' b') a)
   rhsℚ =
     cong₂ _-ᵣ_
       (cong₂ (clampᵣ (rat a')) (maxᵣ-rat a' b') (maxᵣ-rat a b)
        ∙ clampᵣ-rat a' (ℚ.max a' b') (ℚ.max a b))
       (cong (λ z → clampᵣ (rat a') z (rat a)) (maxᵣ-rat a' b')
        ∙ clampᵣ-rat a' (ℚ.max a' b') a)
     ∙ -ᵣ-rat₂ (ℚ.clamp a' (ℚ.max a' b') (ℚ.max a b))
               (ℚ.clamp a' (ℚ.max a' b') a)

  f-sym : ∀ a b a' b' → f a b a' b' ≡ f a' b' a b
  f-sym a b a' b' =
    ≡Cont₂ (fC a b) (fC' a b)
      (λ aℚ' bℚ' →
        ≡Cont₂ (fC' (rat aℚ') (rat bℚ')) (fC (rat aℚ') (rat bℚ'))
          (λ aℚ bℚ → fℚ-sym aℚ bℚ aℚ' bℚ')
          a b)
      a' b'


llll : absᵣ (rat [ pos 0 / 1+ 0 ] -ᵣ rat [ pos 0 / 1+ 0 ]) ≤ᵣ
      rat [ pos 0 / 1+ 0 ]
llll = ≡ᵣWeaken≤ᵣ _ _
   (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ0
     ∙ cong {x = zero} (λ z → rat [ pos z / 1+ z ]) refl )

0<2^-ℚ : ∀ n → ℚ.0< [ pos (2^ n) / 1+ 0 ]
0<2^-ℚ n = ℚ<→0< [ pos (2^ n) / 1+ 0 ] (<ℤ→<ℚ 0 (pos (2^ n))
 (ℤ.ℕ<→pos-<-pos 0 _ (0<2^ n) ))

2^-mon : ∀ n → 2^ n ℕ.< 2^ (suc n)
2^-mon zero = ℕ.≤-solver 2 2
2^-mon (suc n) = ℕ.<-+-< (2^-mon n) (2^-mon n)

lemXX : ∀ n → 1 ℕ.+ predℕ (2^ (suc n)) ≡ 2^ (suc n)
lemXX n = ℕ.k+predℕₖ {1} {2^ (suc n)} (0<2^ (suc n))

invℚ₊-inj : ∀ a b → fst (invℚ₊ a) ≡ fst (invℚ₊ b) → fst a ≡ fst b
invℚ₊-inj a b x =
  sym (ℚ.invℚ₊-invol _)
  ∙∙ cong (fst ∘ invℚ₊) (ℚ₊≡ x) ∙∙
  ℚ.invℚ₊-invol _

module Resample where



 resampledRiemannSum' : ∀ a b →  (ℝ → ℝ)
   → (pa pa' : Partition[ a , b ])
    (s : Sample pa) → ℝ
 resampledRiemannSum' a b f pa pa' sa =
   foldlFin {n = 1 ℕ.+ P'.len}
      (λ s  k →
        let  a' = P'.pts' (finj k)
             b' = P'.pts' (fsuc k)
        in s +ᵣ
            foldlFin {n = 1 ℕ.+ P.len}
            (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
              b-a ·ᵣ (f t) ) 0
                (λ k →  S.samplesΣ k ,
                 clampᵣ a' b' (P.pts' (fsuc k))
                  -ᵣ clampᵣ a' b' (P.pts' (finj k)))
        ) 0 (idfun _)

  where
  module P = Partition[_,_] pa
  module P' = Partition[_,_] pa'
  module S = Sample sa


 partitionClamp : ∀ a b  → ∀ a' b' → a' ≤ᵣ b'
   → a ≤ᵣ a' →  b' ≤ᵣ b →
   (pa : Partition[ a , b ]) →
    b' -ᵣ a' ≡
         foldlFin {n = 1 ℕ.+ len pa}
      (λ s  k →
        let  a* = pts' pa (finj k)
             b* = pts' pa (fsuc k)
        in s +ᵣ
            ((clampᵣ a' b' b* -ᵣ clampᵣ a' b' a*))
        )
      0
      (idfun _)
 partitionClamp a b a' b' a'≤b' a≤a' b'≤b pa =
   cong₂ _-ᵣ_
     (sym (≤x→clampᵣ≡ a' b' (pts' pa flast) a'≤b'
       (subst (b' ≤ᵣ_) (sym (pts'-last pa)) b'≤b)))
     (sym (x≤→clampᵣ≡ a' b' (pts' pa fzero)
       a'≤b' a≤a'))
    ∙ sym (deltas-sum (1 ℕ.+ len pa)
      (clampᵣ a' b' ∘ pts' pa ))



 resample : ∀ a b → a ≤ᵣ b → (pa pa' : Partition[ a , b ])
    (sa : Sample pa)  → ∀ f
    → resampledRiemannSum' a b f pa pa' sa
       ≡ riemannSum' sa f
 resample a b a≤b pa pa' sa f =
    ((cong (foldlFin {n = 1 ℕ.+ P'.len})
     (funExt₂ (λ s k' →
       cong (s +ᵣ_)
        (foldFin+map (1 ℕ.+ P.len) 0 _
         (λ k →  S.samplesΣ k ,
                 clampᵣ (P'.pts' (finj k')) (P'.pts' (fsuc k'))
                  (P.pts' (fsuc k))
                  -ᵣ clampᵣ (P'.pts' (finj k')) (P'.pts' (fsuc k'))
                   (P.pts' (finj k))) (idfun _) )))
     ≡$ 0) ≡$ (idfun _))
     ∙ foldFin+transpose (1 ℕ.+ P'.len) (1 ℕ.+ P.len) _ 0
     ∙ ((cong (foldlFin {n = 1 ℕ.+ P.len})
          (funExt₂ (λ s k →
            cong (s +ᵣ_)
             (  (cong (foldlFin {n = 1 ℕ.+ P'.len})
               (funExt₂ (λ s k' → cong (s +ᵣ_)
                 (·ᵣComm _ _)))
               ≡$ 0 ≡$ (idfun _))
              ∙ foldFin·DistL' (1 ℕ.+ P'.len) _ (f (fst (S.samplesΣ k))) (idfun _)
              ∙ cong (f (fst (S.samplesΣ k)) ·ᵣ_)
                  (((cong (foldlFin {n = 1 ℕ.+ P'.len})
                     (funExt₂ (λ s k' → cong (s +ᵣ_)
                         ((clamp-interval-Δ-swap
                          (P'.pts' (finj k')) (P'.pts' (fsuc k'))
                          (P.pts' (finj k)) (P.pts' (fsuc k))
                          (P'.pts'≤pts' k') (P.pts'≤pts' k)))
                         )) ≡$ 0)
                      ≡$ (idfun _))
                   ∙ sym
                     (partitionClamp a b (P.pts' (finj k)) (P.pts' (fsuc k))
                      (P.pts'≤pts' k) (P.a≤pts' (finj k)) (P.pts'≤b (fsuc k)) pa'))
              ∙ ·ᵣComm _ _
             )
                        ))
          ≡$ 0) ≡$ (idfun _))
     ∙ sym (foldFin+map (1 ℕ.+ P.len) 0 _
       (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k)) (idfun _))


  where
  module P = Partition[_,_] pa
  module P' = Partition[_,_] pa'
  module S = Sample sa

--
 resampleΔ-UC : ∀ a b → (a<b : a ≤ᵣ b)   → ∀ f → IsUContinuous f → (ε : ℚ₊)
    → (δ : ℚ₊ ) →  (∀ (u v : ℝ) →
                   u ∼[ δ ] v →
                   absᵣ (f u -ᵣ f v) <ᵣ
                   fst (ℚ₊→ℝ₊ ε ₊·ᵣ
                       invℝ₊ (maxᵣ 1 (b -ᵣ a) ,
                         isTrans<≤ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) (≤maxᵣ 1 (b -ᵣ a)))))
    → (tpa tpa' : TaggedPartition[ a , b ])
       → mesh≤ᵣ (fst tpa) (rat (fst (quarter₊ δ)))
       → mesh≤ᵣ (fst tpa') (rat (fst (quarter₊ δ))) →
      absᵣ (riemannSum' (snd tpa) f -ᵣ riemannSum' (snd tpa') f) ≤ᵣ
     rat (fst ε)
 resampleΔ-UC a b a≤b f fcu ε δ X (pa , sa) (pa' , sa') = zzzz
  where
    σ : ℝ₊
    σ = maxᵣ 1 (b -ᵣ a) ,
        isTrans<≤ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) (≤maxᵣ 1 (b -ᵣ a))
    η : ℝ₊
    η = ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ σ

    cf : IsContinuous f
    cf = IsUContinuous→IsContinuous f fcu


    module P = Partition[_,_] pa
    module P' = Partition[_,_] pa'
    module S = Sample sa
    module S' = Sample sa'

    ruc'Δ : Fin (suc P.len) → Fin (suc P'.len) → ℝ
    ruc'Δ k k' = (clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k'))
         -ᵣ
        clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k')))

    WeightedSample : Type₀
    WeightedSample = (Σ[ t ∈ ℝ ] (a ≤ᵣ t) × (t ≤ᵣ b)) × ℝ

    weightedValue : WeightedSample → ℝ
    weightedValue ((t , _ , _) , Δ) = Δ ·ᵣ f t

    PΔ : Fin (1 ℕ.+ len pa) → ℝ
    PΔ k = P.pts' (fsuc k) -ᵣ P.pts' (finj k)

    sampleFiber : Fin (1 ℕ.+ len pa) → Fin (1 ℕ.+ len pa') → WeightedSample
    sampleFiber k k' = S'.samplesΣ k' , ruc'Δ k k'

    resampledFiber : Fin (1 ℕ.+ len pa) → ℝ
    resampledFiber k =
      foldlFin {n = 1 ℕ.+ len pa'}
        (λ s y → s +ᵣ weightedValue y) 0
        (sampleFiber k)

    outerDiffTerm : WeightedSample × Fin (1 ℕ.+ len pa) → ℝ
    outerDiffTerm (y , k) = weightedValue y -ᵣ resampledFiber k

    outerBound : Fin (1 ℕ.+ len pa) → ℝ
    outerBound k = fst η ·ᵣ P.pts' (fsuc k) -ᵣ fst η ·ᵣ P.pts' (finj k)

    scaledTerm : (k : Fin (1 ℕ.+ len pa)) → Fin (1 ℕ.+ len pa') → ℝ
    scaledTerm k k' = f (S.samplesΣ k .fst) ·ᵣ ruc'Δ k k'

    innerDiffTerm : (k : Fin (1 ℕ.+ len pa)) → Fin (1 ℕ.+ len pa') × WeightedSample → ℝ
    innerDiffTerm k (k' , y) = scaledTerm k k' -ᵣ weightedValue y

    innerBound : (k : Fin (1 ℕ.+ len pa)) → Fin (1 ℕ.+ len pa') → ℝ
    innerBound k k' = fst η ·ᵣ ruc'Δ k k'


    opaque
     unfolding maxᵣ minᵣ
     zzzz :
       P.mesh≤ᵣ (rat (fst (quarter₊ δ))) →
       P'.mesh≤ᵣ (rat (fst (quarter₊ δ))) →
       absᵣ (S.riemannSum' f -ᵣ S'.riemannSum' f) ≤ᵣ
       rat (fst ε)
     zzzz m-pa< m-pa'< =
        isTrans≡≤ᵣ _ _ _
         (cong absᵣ
          (cong (_-ᵣ_ (S.riemannSum' f))
            (sym (resample a b a≤b pa' pa sa' f))
            ∙ zip-foldFin-ᵣ (1 ℕ.+ len pa)

              (λ k → S.samplesΣ k , PΔ k)
              (idfun (Fin (1 ℕ.+ len pa)))
              weightedValue resampledFiber 0 0))
         (isTrans≤ᵣ _ _ _ (isTrans≤≡ᵣ _ _ _

           (foldFin+≤-abs (1 ℕ.+ len pa) (0 -ᵣ 0) 0
             outerDiffTerm outerBound
                           (λ k →
                             (S.samplesΣ k , PΔ k) , k)
                           (idfun (Fin (1 ℕ.+ len pa)))
            llll
            ruc
            )
           (deltas-sum (1 ℕ.+ len pa) ((fst η ·ᵣ_) ∘ pts' pa)
            ∙ cong₂ _-ᵣ_ (cong (fst η ·ᵣ_) P.pts'-last) refl
            ∙ sym (Rℝ.·DistR- _ _ _)))
             (isTrans≤≡ᵣ _ _ _
               (≤ᵣ-o·ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (snd η))
                (isTrans≤≡ᵣ _ _ _ (≤maxᵣ (b -ᵣ a) 1) (maxᵣComm (b -ᵣ a) 1)) )
               ([x/₊y]·yᵣ _ σ)))

      where

 -- ruc

       ruc' : ∀ k k' →
              absᵣ
          (f (S.samplesΣ k .fst) ·ᵣ ruc'Δ k k' -ᵣ
            ruc'Δ k k' ·ᵣ f (S'.samplesΣ k' .fst))
          ≤ᵣ fst η ·ᵣ ruc'Δ k k'
       ruc' k k' =
        isTrans≡≤ᵣ _ _ _

         (cong absᵣ (cong₂ _-ᵣ_
          (·ᵣComm _ _)
          ((clamp-Δ-·f _ _ (P.pts'≤pts' k)
            f cf (half₊ (half₊ δ)) _ _ (P'.pts'≤pts' k')
              (isTrans≤≡ᵣ _ _ _ (m-pa'< k')
                (cong rat (/4₊≡/2₊/2₊ δ))) _
                 (S'.pts'≤samples k' ,
                  S'.samples≤pts' k' )))

                  ∙
               sym (Rℝ.·DistR- (ruc'Δ k k') _ f') ) ∙
                ·absᵣ _ _ ∙
                 cong (_·ᵣ (absᵣ (f (S.samplesΣ k .fst) -ᵣ
                      f'))) (absᵣNonNeg _ hh
                        ) ∙ ·ᵣComm _ _)
         (≤ᵣ-·ᵣo _ _ _ hh (<ᵣWeaken≤ᵣ _ _ (X _ _ smpl-δ)))
         where
          δ/4<δ/2 : rat (fst δ ℚ.· ([ pos 1 , 2 ] ℚ.· [ pos 1 , 2 ])) <ᵣ
             rat (fst (half₊ δ))
          δ/4<δ/2 = (isTrans≡<ᵣ _ _ _
                            (cong rat (ℚ.·Assoc (fst δ) _ _))
                            (<ℚ→<ᵣ (fst (half₊ (half₊ δ))) (fst (half₊ δ)) (x/2<x (half₊ δ))))

          f' : ℝ
          f' =
            f (clampᵣ
                (P.pts' (finj k) -ᵣ rat (fst (half₊ (half₊ δ))))
                (P.pts' (fsuc k) +ᵣ rat (fst (half₊ (half₊ δ))))
                (S'.samplesΣ k' .fst))
          hh : 0 ≤ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k'))
                -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k'))
          hh = (x≤y→0≤y-x _ _
                         (clamp-monotone-≤ᵣ
                          (P.pts' (finj k))
                          (P.pts' (fsuc k))
                          _ _ (P'.pts'≤pts' k')))

          xzxd : absᵣ
               (P.pts' (fsuc k) +ᵣ rat (fst (half₊ (half₊ δ))) +ᵣ -ᵣ P.pts' (finj k))
               +ᵣ absᵣ (-ᵣ (-ᵣ rat (fst (half₊ (half₊ δ)))))
               <ᵣ rat (fst δ)
          xzxd =
            isTrans<≡ᵣ _ _ _
              (≤<ᵣMonotone+ᵣ _ _ _ _ first≤ second<)
              (+ᵣ-rat (fst (half₊ δ)) (fst (half₊ δ))
               ∙ cong rat (ε/2+ε/2≡ε (fst δ)))
           where
           q : ℚ
           q = fst (half₊ (half₊ δ))

           exprEq : P.pts' (fsuc k) +ᵣ rat q +ᵣ -ᵣ P.pts' (finj k) ≡
                    (P.pts' (fsuc k) -ᵣ P.pts' (finj k)) +ᵣ rat q
           exprEq =
             sym (+ᵣAssoc (P.pts' (fsuc k)) (rat q) (-ᵣ P.pts' (finj k)))
             ∙ cong (P.pts' (fsuc k) +ᵣ_)
                 (+ᵣComm (rat q) (-ᵣ P.pts' (finj k)))
             ∙ +ᵣAssoc (P.pts' (fsuc k)) (-ᵣ P.pts' (finj k)) (rat q)

           diffNonNeg : 0 ≤ᵣ P.pts' (fsuc k) -ᵣ P.pts' (finj k)
           diffNonNeg = x≤y→0≤y-x _ _ (P.pts'≤pts' k)

           qNonNeg : 0 ≤ᵣ rat q
           qNonNeg = ≤ℚ→≤ᵣ 0 q (ℚ.0≤ℚ₊ (half₊ (half₊ δ)))

           exprNonNeg : 0 ≤ᵣ P.pts' (fsuc k) +ᵣ rat q +ᵣ -ᵣ P.pts' (finj k)
           exprNonNeg =
             subst (0 ≤ᵣ_) (sym exprEq)
               (isTrans≡≤ᵣ _ _ _
                 (sym (+ᵣ-rat 0 0))
                 (≤ᵣMonotone+ᵣ _ _ _ _ diffNonNeg qNonNeg))

           diff≤q : P.pts' (fsuc k) -ᵣ P.pts' (finj k) ≤ᵣ rat q
           diff≤q =
             isTrans≤≡ᵣ _ _ _
               (m-pa< k)
               (cong rat (/4₊≡/2₊/2₊ δ))

           first≤ : absᵣ
                    (P.pts' (fsuc k) +ᵣ rat q +ᵣ -ᵣ P.pts' (finj k))
                    ≤ᵣ rat (fst (half₊ δ))
           first≤ =
             isTrans≡≤ᵣ _ _ _
               (absᵣNonNeg _ exprNonNeg ∙ exprEq)
               (isTrans≤≡ᵣ _ _ _
                 (≤ᵣMonotone+ᵣ _ _ _ _ diff≤q (≤ᵣ-refl (rat q)))
                 (+ᵣ-rat q q ∙ cong rat (ε/2+ε/2≡ε (fst (half₊ δ)))))

           second< : absᵣ (-ᵣ (-ᵣ rat q)) <ᵣ rat (fst (half₊ δ))
           second< =
             isTrans≡<ᵣ _ _ _
               (cong absᵣ (-ᵣInvol (rat q))
                ∙ absᵣNonNeg (rat q) qNonNeg)
               (<ℚ→<ᵣ q (fst (half₊ δ)) (x/2<x (half₊ δ)))

          smpl-δ : S.samplesΣ k .fst ∼[ δ ]
               clampᵣ (P.pts' (finj k) -ᵣ rat (fst (half₊ (half₊ δ))))
                      (P.pts' (fsuc k) +ᵣ rat (fst (half₊ (half₊ δ))))
               (fst (S'.samplesΣ k'))
          smpl-δ =
            invEq (∼≃abs<ε _ _ _)
            ((isTrans≤<ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (cong absᵣ
                 ((cong₂ _-ᵣ_
                   (∈ℚintervalℙ→clampᵣ≡ (P.pts' (finj k) -ᵣ rat (fst (half₊ (half₊ δ))))
                    (P.pts' (fsuc k) +ᵣ rat (fst (half₊ (half₊ δ))))
                     (fst (S.samplesΣ k))

                      ((isTrans≤ᵣ _ _ _
                        (isTrans≤≡ᵣ _ _ _
                          (≤ᵣ-o+ _ _ (P.pts' (finj k))
                           (-ᵣ≤ᵣ _ _ (≤ℚ→≤ᵣ 0 _ (ℚ.0≤ℚ₊ (half₊ (half₊ δ))))))
                          (Rℝ.+IdR' _ _ (-ᵣ-rat 0)))
                        (S.pts'≤samples k)) ,
                         isTrans≤ᵣ _ _ _
                         (S.samples≤pts' k)
                         (isTrans≡≤ᵣ _ _ _ (sym (Rℝ.+IdR' _ _ refl))
                           (≤ᵣ-o+ _ _ (P.pts' (fsuc k))
                           (≤ℚ→≤ᵣ 0 _ (ℚ.0≤ℚ₊ (half₊ (half₊ δ))))))
                        )
                        )
                   refl)))
                  (clampᵣ-dist (P.pts' (finj k) -ᵣ rat (fst (half₊ (half₊ δ))))
                   (P.pts' (fsuc k) +ᵣ rat (fst (half₊ (half₊ δ))))
                     _ _))
                  (isTrans≤<ᵣ _ _ _
                   (isTrans≡≤ᵣ _ _ _ (cong absᵣ
                    (cong ((P.pts' (fsuc k) +ᵣ rat (fst (half₊ (half₊ δ)))) +ᵣ_) ( -ᵣDistr _ _) ∙ +ᵣAssoc _ _ _))
                     (absᵣ-triangle _ _))
                      xzxd)))
       ruc : ∀ k →
           absᵣ
         ((P.pts' (fsuc k) -ᵣ P.pts' (finj k)) ·ᵣ f (S.samplesΣ k .fst) -ᵣ
          foldlFin {n = 1 ℕ.+ len pa'}
          (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ b-a ·ᵣ f t) 0
          (λ k₁ →
             P'.samplesΣ sa' k₁ ,
             clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
             -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k₁))))
         ≤ᵣ
         (fst η ·ᵣ P.pts' (fsuc k) -ᵣ fst η ·ᵣ P.pts' (finj k))

       ruc k =
         isTrans≡≤ᵣ _ _ _
           (cong (absᵣ ∘ (_-ᵣ (foldlFin {n = 1 ℕ.+ len pa'}
          (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ b-a ·ᵣ f t) 0
          (λ k₁ →
             P'.samplesΣ sa' k₁ ,
             clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
             -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k₁))
             ))))
              (cong (_·ᵣ f (S.samplesΣ k .fst))
                (partitionClamp a b
                  (P.pts' (finj k))
                  (P.pts' (fsuc k))
                   (P.pts'≤pts' k)
                  (P.a≤pts' (finj k)) (P.pts'≤b (fsuc k)) pa'
                  ) ∙ ·ᵣComm _ _ ∙
                   sym (foldFin·DistL (1 ℕ.+ len pa') _ _ _
                    (idfun (Fin (1 ℕ.+ len pa'))))) ∙
                   cong absᵣ
                    (zip-foldFin-ᵣ (1 ℕ.+ len pa')
                    (idfun (Fin (1 ℕ.+ len pa')))
                     (sampleFiber k)
                       (scaledTerm k) weightedValue
                       (f (S.samplesΣ k .fst) ·ᵣ 0)
                     0))
              (isTrans≤≡ᵣ _ _ _
               (foldFin+≤-abs (1 ℕ.+ len pa')
                  ((f (S.samplesΣ k .fst) ·ᵣ 0) -ᵣ 0) 0
                   (innerDiffTerm k) (innerBound k)
                   (λ k₁ → k₁ , sampleFiber k k₁)
                   (idfun (Fin (1 ℕ.+ len pa')))
                   (isTrans≡≤ᵣ _ _ _
                      (cong absᵣ (cong (_-ᵣ 0) (Rℝ.0RightAnnihilates _)))
                      llll)
                 (ruc' k))
               ((foldFin·DistL' (1 ℕ.+ len pa') _ _ (idfun (Fin (1 ℕ.+ len pa'))) ∙
                cong (fst η ·ᵣ_) (deltas-sum (1 ℕ.+ P'.len )
                  (clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) ∘ (P'.pts'))
                  ∙ cong₂ _-ᵣ_
                    (≤x→clampᵣ≡ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' flast)
                      (P.pts'≤pts' k)
                      (subst (P.pts' (fsuc k) ≤ᵣ_) (sym P'.pts'-last)
                        (P.pts'≤b (fsuc k))) )
                    (x≤→clampᵣ≡ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' fzero)
                      (P.pts'≤pts' k) (P.a≤pts' (finj k))))
                ) ∙ Rℝ.·DistR- _ _ _) )

∃enclosingℚInterval : ∀ a b →
                      ∃[ (A , B) ∈ (ℚ × ℚ) ]
                        (rat A ≤ᵣ a) × (b ≤ᵣ rat B)
∃enclosingℚInterval a b =
  PT.map2 (λ (A , _ , A<a) (B , b<B , _)
       → (A , B) , <ᵣWeaken≤ᵣ _ _ A<a , <ᵣWeaken≤ᵣ _ _ b<B)
   (denseℚinℝ (a -ᵣ 1) a (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ _ _ a (-ᵣ<ᵣ _ _ (decℚ<ᵣ? {0} {1})))
       (Rℝ.+IdR' _ _ (-ᵣ-rat 0)) ))
   (denseℚinℝ b (b +ᵣ 1)
    (isTrans≡<ᵣ _ _ _ (sym (+IdR b)) (<ᵣ-o+ _ _ b (decℚ<ᵣ? {0} {1}))))


record RefinableTaggedPartition[_,_] (a b : ℝ) : Type where
 field
  tpSeq : ℕ → TaggedPartition[ a , b ]
  tpRef : ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n →
   mesh≤ᵣ (fst (tpSeq n)) (rat (fst ε)))

 tpTP : ∀ (ε : ℚ₊) →
   Σ[ tp ∈ TaggedPartition[ a , b ] ]
    (mesh≤ᵣ (fst tp) (rat (fst ε)))
 tpTP ε = tpSeq (suc (fst (tpRef ε))) , (snd (tpRef ε) _ ℕ.≤-refl)


clamp-TaggedPartition : ∀ A B → A ≤ᵣ B → ∀ a b → a ≤ᵣ b →
   TaggedPartition[ A , B ] →
   TaggedPartition[ a , b ]
clamp-TaggedPartition A B A≤B a b a≤b tp = w

 where
 w : TaggedPartition[ a , b ]
 w .fst .len = fst (tp) .len
 w .fst .pts = clampᵣ a b ∘ (fst (tp) .pts)
 w .fst .endpoints≤ = a≤b
 w .fst .a≤pts k = ≤clampᵣ a b _ a≤b
 w .fst .pts≤b k = clamp≤ᵣ a b _
 w .fst .pts≤pts k = clamp-monotone-≤ᵣ a b _ _
   (tp  .fst .pts≤pts k)
 w .snd .samples = clampᵣ a b ∘ (tp .snd .samples)
 w .snd .pts'≤samples j@(zero , _) =
   ≤clampᵣ a b  _ a≤b
 w .snd .pts'≤samples j@(suc k , p) =
   let jm : Fin (tp .fst .len)
       jm = k , p
       finj≡mid : finj j ≡ fsuc (finj jm)
       finj≡mid = toℕ-injective {k = 2 ℕ.+ tp .fst .len} refl
       lhsMid : pts' (w .fst) (finj j) ≡ pts (w .fst) jm
       lhsMid = cong (pts' (w .fst)) finj≡mid ∙ pts'-mid (w .fst) jm
       rhsMid : clampᵣ a b (pts' (tp .fst) (finj j))
              ≡ clampᵣ a b (pts (tp .fst) jm)
       rhsMid = cong (clampᵣ a b)
         (cong (pts' (tp .fst)) finj≡mid ∙ pts'-mid (tp .fst) jm)
       lhsEq : pts' (w .fst) (finj j) ≡ clampᵣ a b (pts' (tp .fst) (finj j))
       lhsEq = lhsMid ∙ sym rhsMid
   in subst2 _≤ᵣ_ (sym lhsEq) refl
       (clamp-monotone-≤ᵣ a b _ _ (tp .snd .pts'≤samples j))
 w .snd .samples≤pts' j@(k , p) =
   ℕᵗ.split<ᵗ-suc-elim {k = k} {len = tp .fst .len}
     p
     (λ k<slen →
       let jm : Fin (tp .fst .len)
           jm = k , k<slen
           fsucj≡mid : fsuc j ≡ fsuc (finj jm)
           fsucj≡mid = toℕ-injective {k = 2 ℕ.+ tp .fst .len} refl
           lhsMid : pts' (w .fst) (fsuc j) ≡ pts (w .fst) jm
           lhsMid = cong (pts' (w .fst)) fsucj≡mid ∙ pts'-mid (w .fst) jm
           rhsMid : clampᵣ a b (pts' (tp .fst) (fsuc j))
                  ≡ clampᵣ a b (pts (tp .fst) jm)
           rhsMid = cong (clampᵣ a b)
             (cong (pts' (tp .fst)) fsucj≡mid ∙ pts'-mid (tp .fst) jm)
           rhsEq : pts' (w .fst) (fsuc j) ≡ clampᵣ a b (pts' (tp .fst) (fsuc j))
           rhsEq = lhsMid ∙ sym rhsMid
       in subst2 _≤ᵣ_ refl (sym rhsEq)
           (clamp-monotone-≤ᵣ a b _ _ (tp .snd .samples≤pts' j)))
     (λ k≡last →
       let fsucj≡last : fsuc j ≡ flast {k = 1 ℕ.+ w .fst .len}
           fsucj≡last =
             toℕ-injective {k = 2 ℕ.+ w .fst .len} (cong suc k≡last)
           rhsEq : pts' (w .fst) (fsuc j) ≡ b
           rhsEq = cong (pts' (w .fst)) fsucj≡last ∙ pts'-last (w .fst)
       in subst ((w .snd .samples j) ≤ᵣ_) (sym rhsEq) (clamp≤ᵣ a b _))

clamp-TaggedPartition-mesh : ∀ A B A≤B a b a≤b
  → a ∈ intervalℙ A B
  → b ∈ intervalℙ A B
  → ∀ tp δ
  → mesh≤ᵣ (fst tp) δ
  → mesh≤ᵣ (fst (clamp-TaggedPartition A B A≤B a b a≤b tp)) δ

clamp-TaggedPartition-mesh A B A≤B a b a≤b (≤a , a≤) (≤b , b≤) tp δ mesh-tp k =
   isTrans≤ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
     (cong₂ _-ᵣ_  (w-pts (fsuc k)) (w-pts (finj k)))
     ((subst2 _≤ᵣ_
        (absᵣNonNeg _ ((x≤y→0≤y-x _ _
          (clamp-monotone-≤ᵣ (pts' (fst tp) (finj k)) (pts' (fst tp) (fsuc k))
            a b a≤b)))
         ∙ sym (clamp-interval-Δ-swap
              a b
              (pts' (fst (tp)) (finj k))
              (pts' (fst (tp)) (fsuc k))

               a≤b ((pts'≤pts' (fst (tp)) k))))
        (absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' (fst (tp)) k)))
        (clampᵣ-dist _ _ _ _))))
    (mesh-tp k)
 where

 P : Partition[ A , B ]
 P = fst tp

 Q : Partition[ a , b ]
 Q = fst (clamp-TaggedPartition A B A≤B a b a≤b tp)

 w-pts : ∀ k → pts' (fst (clamp-TaggedPartition A B A≤B a b a≤b tp)) k ≡
  clampᵣ a b (pts' (fst tp) k)
 w-pts (zero , _) = sym (x≤→clampᵣ≡ a b A a≤b ≤a)
 w-pts j'@(suc k , p) =
   ℕᵗ.split<ᵗ-suc-elim {len = len P} p
     (λ k<slen →
       let j : Fin (len P)
           j = k , k<slen
           j'≡mid : j' ≡ fsuc (finj j)
           j'≡mid = toℕ-injective {k = 2 ℕ.+ len P} refl
           lhsMid : pts' Q j' ≡ pts Q j
           lhsMid = cong (pts' Q) j'≡mid ∙ pts'-mid Q j
           rhsMid : clampᵣ a b (pts' P j') ≡ clampᵣ a b (pts P j)
           rhsMid = cong (clampᵣ a b) (cong (pts' P) j'≡mid ∙ pts'-mid P j)
       in lhsMid ∙ sym rhsMid)
     (λ k≡slen →
       let j'≡last : j' ≡ flast {k = 1 ℕ.+ len P}
           j'≡last = toℕ-injective {k = 2 ℕ.+ len P} (cong suc k≡slen)
           lhsLast : pts' Q j' ≡ b
           lhsLast = cong (pts' Q) j'≡last ∙ pts'-last Q
           rhsLast : clampᵣ a b (pts' P j') ≡ clampᵣ a b B
           rhsLast = cong (clampᵣ a b) (cong (pts' P) j'≡last ∙ pts'-last P)
       in lhsLast ∙ sym (≤x→clampᵣ≡ a b B a≤b b≤) ∙ sym rhsLast)

clamp-RefinableTaggedPartition : ∀ A B → ∀ a b → a ≤ᵣ b
   → a ∈ intervalℙ A B
   → b ∈ intervalℙ A B →
   RefinableTaggedPartition[ A , B ] →
   RefinableTaggedPartition[ a , b ]
clamp-RefinableTaggedPartition A B a b a≤b (≤a , a≤) (≤b , b≤) rfp = ww
 where
 open RefinableTaggedPartition[_,_]



 w : ℕ → TaggedPartition[ a , b ]
 w = clamp-TaggedPartition A B
   (isTrans≤ᵣ _ _ _ (isTrans≤ᵣ _ _ _ ≤a a≤b) b≤)
    a b a≤b ∘ rfp .tpSeq

 P : ℕ → Partition[ A , B ]
 P n = fst (rfp .tpSeq n)

 Q : ℕ → Partition[ a , b ]
 Q n = fst (w n)

 w-pts : ∀ n k → pts' (fst (w n)) k ≡
  clampᵣ a b (pts' (fst (rfp .tpSeq n)) k)
 w-pts n (zero , _) = sym (x≤→clampᵣ≡ a b A a≤b ≤a)
 w-pts n j'@(suc k , p) =
   ℕᵗ.split<ᵗ-suc-elim {len = len (P n)} p
     (λ k<slen →
       let j : Fin (len (P n))
           j = k , k<slen
           j'≡mid : j' ≡ fsuc (finj j)
           j'≡mid = toℕ-injective {k = 2 ℕ.+ len (P n)} refl
           lhsMid : pts' (Q n) j' ≡ pts (Q n) j
           lhsMid = cong (pts' (Q n)) j'≡mid ∙ pts'-mid (Q n) j
           rhsMid : clampᵣ a b (pts' (P n) j') ≡ clampᵣ a b (pts (P n) j)
           rhsMid = cong (clampᵣ a b) (cong (pts' (P n)) j'≡mid ∙ pts'-mid (P n) j)
       in lhsMid ∙ sym rhsMid)
     (λ k≡slen →
       let j'≡last : j' ≡ flast {k = 1 ℕ.+ len (P n)}
           j'≡last = toℕ-injective {k = 2 ℕ.+ len (P n)} (cong suc k≡slen)
           lhsLast : pts' (Q n) j' ≡ b
           lhsLast = cong (pts' (Q n)) j'≡last ∙ pts'-last (Q n)
           rhsLast : clampᵣ a b (pts' (P n) j') ≡ clampᵣ a b B
           rhsLast = cong (clampᵣ a b) (cong (pts' (P n)) j'≡last ∙ pts'-last (P n))
       in lhsLast ∙ sym (≤x→clampᵣ≡ a b B a≤b b≤) ∙ sym rhsLast)

 ww : RefinableTaggedPartition[ a , b ]
 ww .tpSeq = w
 ww .tpRef = map-snd (λ X n n< k →
   isTrans≤ᵣ _ _ _
     ((subst2 _≤ᵣ_
        (cong absᵣ
           (sym (cong₂ _-ᵣ_ (w-pts n (fsuc k)) (w-pts n (finj k))
             ∙ (clamp-interval-Δ-swap
              a b
              (pts' (fst (rfp .tpSeq n)) (finj k))
              (pts' (fst (rfp .tpSeq n)) (fsuc k))

               a≤b ((pts'≤pts' (fst (rfp .tpSeq n)) k))))) ∙
          absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' (fst (w n)) k)))
        (absᵣNonNeg _ (x≤y→0≤y-x _ _ (pts'≤pts' (fst (rfp .tpSeq n)) k)))
        (clampᵣ-dist _ _ _ _))
      ) (X n n< k) ) ∘ (tpRef rfp)




rtp-1/n : ∀ (A B : ℚ) → A ℚ.≤ B → RefinableTaggedPartition[ rat A , rat B ]
rtp-1/n A B A≤B .RefinableTaggedPartition[_,_].tpSeq n =
  EqualPartition.equalPartition (rat A) (rat B) (≤ℚ→≤ᵣ _ _ A≤B) n
   , leftSample _
rtp-1/n A B A≤B .RefinableTaggedPartition[_,_].tpRef ε =
  let Δ₊ = ℚ.max (B ℚ.- A) 1 , ℚ<→0< (ℚ.max (B ℚ.- A) 1)
              (ℚ.isTrans<≤ 0 1 (ℚ.max (B ℚ.- A) 1)
              (ℚ.decℚ<? {0} {1})
              ((ℚ.≤max' (B ℚ.- A) 1)))
      (1+ N , p)  = ℚ.ceilℚ₊ (Δ₊ ℚ₊· invℚ₊ ε)
      in N , λ n N<n k →
       let z = subst (ℚ.max (B ℚ.- A) [ pos 1 / 1+ 0 ] ℚ.≤_)
             (ℚ.·Comm (fst ε) [ pos (suc n) / 1+ 0 ])
              ((x·invℚ₊y≤z→x≤y·z (ℚ.max (B ℚ.- A) [ pos 1 / 1+ 0 ])
                   _ ε
                (ℚ.<Weaken≤ (fst (Δ₊ ℚ₊· invℚ₊ ε)) (fromNat (suc n))
                 (ℚ.isTrans< (fst (Δ₊ ℚ₊· invℚ₊ ε)) _ (fromNat (suc n)) p
                 (<ℤ→<ℚ
                   (ℤ.pos (suc N)) (ℤ.pos (suc n))
                     (ℤ.ℕ<→pos-<-pos (suc N) (suc n)
                       (ℕ.suc-≤-suc N<n)))))))
       in isTrans≡≤ᵣ _ _ _
          (EqualPartition.equalPartitionΔ (rat A) (rat B) (≤ℚ→≤ᵣ A B A≤B) n k ∙
            cong (_·ᵣ rat [ pos 1 / 1+ n ]) (-ᵣ-rat₂ _ _) ∙
             sym (rat·ᵣrat _ _))
              (≤ℚ→≤ᵣ _ _
                (ℚ.isTrans≤ ((B ℚ.- A) ℚ.· [ pos 1 / 1+ n ])
                   _ (fst ε)
                  ((ℚ.≤-·o (B ℚ.- A) (ℚ.max (B ℚ.- A) 1) ([ pos 1 / 1+ n ])
                  (ℚ.0≤pos 1 (1+ n))
                  (ℚ.≤max (B ℚ.- A) 1)))
                  (let N₂ : ℚ₊
                       N₂ = fromNat (suc n)
                       Δ≤N₂·ε : ℚ.max (B ℚ.- A) 1 ℚ.≤ fst N₂ ℚ.· fst ε
                       Δ≤N₂·ε = z
                       Δ≤ε·N₂ : ℚ.max (B ℚ.- A) 1 ℚ.≤ fst ε ℚ.· fst N₂
                       Δ≤ε·N₂ =
                         subst (ℚ.max (B ℚ.- A) 1 ℚ.≤_)
                           (ℚ.·Comm (fst N₂) (fst ε))
                           Δ≤N₂·ε
                       Δ·invN₂≤ε : ℚ.max (B ℚ.- A) 1 ℚ.· fst (invℚ₊ N₂) ℚ.≤ fst ε
                       Δ·invN₂≤ε =
                         x≤y·z→x·invℚ₊y≤z (ℚ.max (B ℚ.- A) 1) N₂ (fst ε) Δ≤ε·N₂
                   in subst (λ q → ℚ.max (B ℚ.- A) 1 ℚ.· q ℚ.≤ fst ε)
                        (invℚ₊-fromNat n)
                        Δ·invN₂≤ε)))

∃RefinableTaggedPartition : (∀ (A B : ℚ) → A ℚ.≤ B → RefinableTaggedPartition[ rat A , rat B ])
  → ∀ a b → a ≤ᵣ b → ∥ RefinableTaggedPartition[ a , b ] ∥₁
∃RefinableTaggedPartition rtpℚ a b a≤b =
  PT.map (λ ((A , B) , A≤a , b≤B) →
    (clamp-RefinableTaggedPartition
            _ _ a b a≤b
             (A≤a , (isTrans≤ᵣ _ _ _ a≤b b≤B))
             (isTrans≤ᵣ _ _ _ A≤a a≤b , b≤B)
            (rtpℚ A B
              (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                (isTrans≤ᵣ _ _ _ A≤a a≤b)
                  b≤B)))))
   (∃enclosingℚInterval a b)
