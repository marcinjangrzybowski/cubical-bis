module Cubical.Data.Rationals.Inverse where

open import Cubical.Data.Rationals.Inverse.Base public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast.Base as ℤ using (ℤ; pos; negsuc; ℕ₊₁→ℤ)
open import Cubical.Data.Int.Fast.Properties as ℤ using ()
open import Cubical.Data.Int.Fast.Order as ℤ using ()
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Rationals.Order
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)
open PositiveRationals
open NonNegativeRationals
open PositiveHalvesℚ
open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Floor
open import Cubical.Data.Rationals.Order.Algebra
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
import Cubical.Data.Bool as 𝟚
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

invℚ₊-invol : ∀ x → fst ((x ⁻¹₊) ⁻¹₊) ≡ fst  x
invℚ₊-invol x = ℚ!



x·invℚ₊[x] : ∀ x → fst x · fst (x ⁻¹₊) ≡ 1
x·invℚ₊[x] x = ℚ!

invℚ₊[x]·x : ∀ x →  fst (x ⁻¹₊) · fst x ≡ 1
invℚ₊[x]·x x = ℚ!

[y·x]/y : ∀ y x → fst (y ⁻¹₊) · (fst y · x) ≡ x
[y·x]/y y x = ℚ!

y·[x/y] : ∀ y x →  fst y · (fst (y ⁻¹₊) · x) ≡ x
y·[x/y] y x = ℚ!


invℚ₊Dist· : ∀ x y →  (( x ⁻¹₊) ·₊ (y ⁻¹₊)) ≡
       ( (x ·₊ y) ⁻¹₊)
invℚ₊Dist· x y = ℚ₊≡ ℚ!


-- equivInvℚ₊ : ℚ₊ ≃ ℚ₊
-- equivInvℚ₊ = involEquiv {f = invℚ₊} λ x → ℚ₊≡ (invℚ₊-invol x)

x≤y≃x/y≤1 : ∀ x y → (x ≤ fst y) ≃ (x ／₊ y ≤ 1)
x≤y≃x/y≤1 x y = propBiimpl→Equiv (isProp≤ _ _) (isProp≤ _ _)
  (subst2 _≤_ ℚ! ℚ! ∘S ·MonoL≤ _ _ _ (<Weaken≤ _ _ (snd (y ⁻¹₊))))
  (subst2 _≤_ ℚ! ℚ! ∘S ·MonoL≤ _ _ _ (<Weaken≤ _ _ (snd y)))

x<y≃x/y<1 : ∀ x y → (x < fst y) ≃ (x ／₊ y < 1)
x<y≃x/y<1 x y = propBiimpl→Equiv (isProp< _ _) (isProp< _ _)
  (subst2 _<_ ℚ! ℚ! ∘S ·MonoL< _ _ _ (snd (y ⁻¹₊)))
  (subst2 _<_ ℚ! ℚ! ∘S ·MonoL< _ _ _ (snd y))

getPosRatio : (L₁ L₂ : ℚ₊) → (fst ((L₁ ⁻¹₊) ·₊  L₂) ≤ 1)
                           ⊎ (fst ((L₂ ⁻¹₊) ·₊  L₁) ≤ 1)
getPosRatio L₁ L₂ =
  elimBy≤ {A = λ (L₁ L₂ : ℚ) → (<L₁ : 0< L₁) → (<L₂ : 0< L₂)
                      →  (((fst ( (L₁ , <L₁) ⁻¹₊ ·₊  (L₂ , <L₂))) ≤ 1)
                           ⊎ ((fst (((L₂ , <L₂) ⁻¹₊) ·₊
                            (L₁ , <L₁))) ≤ 1))}
    (λ x y x₁ <L₁ <L₂ →
      Iso.fun (⊎.⊎-swap-Iso) (x₁ <L₂ <L₁) )
     (λ L₁ L₂ L₁<L₂ <L₁ <L₂ →
             inr (subst (_≤ 1) (·Comm L₁ _) (fst (x≤y≃x/y≤1 _ (_ , <L₂)) L₁<L₂)))
     (fst L₁) (fst L₂) (snd L₁) (snd L₂)

invℚ : ∀ q → 0 # q → ℚ
invℚ q p = sign q · fst ((0#→ℚ₊ q p) ⁻¹₊)


sign²≡1 : ∀ q → 0 # q → sign q · sign q ≡ 1
sign²≡1 q 0#q =
  sign·sign q q ∙
    fst (fst (<≃sign (q · q)))
      (⊎.rec
        (λ 0<q → 0<-m·n q q 0<q 0<q)
        (λ q<0 →
          subst (0 <_) (-·- q q)
            (0<-m·n (- q) (- q) (minus-< q 0 q<0) (minus-< q 0 q<0)))
        0#q)

invℚ₊≡invℚ : ∀ q p → invℚ (fst q) p ≡ fst (q ⁻¹₊)
invℚ₊≡invℚ q p = cong₂ _·_ (fst (<→sign (fst q)) (snd q))
   (cong (fst ∘ _⁻¹₊) (ℚ₊≡ (sym (abs'≡abs (fst q)) ∙
     0<→abs≡id (fst q) ((snd q))))) ∙ ℚR.·IdL (fst ( q ⁻¹₊))
    
fromNat-invℚ' : ∀ n p → invℚ [ ℕ₊₁→ℤ n / (1+ zero) ] p ≡ [ (pos 1) / n ]
fromNat-invℚ' n p = eq/ _ _ ℤ!


fromNat-invℚ : ∀ n p → invℚ [ pos (suc n) / (1+ zero) ] p ≡ [ (pos 1) / 1+ n ]
fromNat-invℚ n p = fromNat-invℚ' _ p


invℚ-pos : ∀ x y → 0 < x → 0 < invℚ x y
invℚ-pos x y z =
  subst (0 <_)
    (sym (invℚ₊≡invℚ (x , z) y))
      (snd ( (x , z) ⁻¹₊))


0#invℚ : ∀ q 0#q → 0 # (invℚ q 0#q)
0#invℚ q 0#q = ·Monotone0# _ _  (fst (0#sign q) 0#q)
  (inl (snd ((0#→ℚ₊ q 0#q) ⁻¹₊ )))




·DistInvℚ : ∀ x y 0#x 0#y 0#xy →
  (invℚ x 0#x) · (invℚ y 0#y) ≡ invℚ (x · y) 0#xy
·DistInvℚ x y 0#x 0#y 0#xy =
   (sym (·Assoc (sign x) (fst ((0#→ℚ₊ x 0#x) ⁻¹₊))
   (sign y · fst ( (0#→ℚ₊ y 0#y) ⁻¹₊))) ∙
    cong ((sign x) ·_)
      (·Assoc (fst ( (0#→ℚ₊ x 0#x) ⁻¹₊)) (sign y) (fst ( (0#→ℚ₊ y 0#y) ⁻¹₊))
       ∙∙ cong (_· fst ((0#→ℚ₊ y 0#y) ⁻¹₊))
         (·Comm (fst ((0#→ℚ₊ x 0#x) ⁻¹₊)) (sign y)) ∙∙
       sym (·Assoc (sign y) (fst ( (0#→ℚ₊ x 0#x) ⁻¹₊))
        (fst ( (0#→ℚ₊ y 0#y) ⁻¹₊))))
   ∙ (·Assoc (sign x) (sign y) (fst ((0#→ℚ₊ x 0#x) ⁻¹₊)
    · fst ((0#→ℚ₊ y 0#y) ⁻¹₊))))
   ∙
   cong₂ _·_
     (sign·sign x y)
     (cong fst (invℚ₊Dist· (0#→ℚ₊ x 0#x) (0#→ℚ₊ y 0#y))
       ∙ cong (fst ∘ _⁻¹₊) (ℚ₊≡ (abs'·abs' x y)) )

invℚ-sign : ∀ q 0#q → sign q ≡ (invℚ (sign q) 0#q)
invℚ-sign q =
  (λ {a} → ⊎.rec (λ p → p ∙ cong  (uncurry invℚ)
     (Σ≡Prop  (λ x → isProp# 0 x )
       {u = 1 , inl (𝟚.toWitness {Q = <Dec 0 1} tt)} {v = sign q , a} (sym p) )
     )
     ((λ p → p ∙ cong (uncurry invℚ)
    (Σ≡Prop  (λ x → isProp# 0 x)
     {u = -1 , inr (𝟚.toWitness {Q = <Dec -1 0} tt)} {v = sign q , a} (sym p) ))))
 ∘ ⊎.map (fst (fst (<≃sign q)))
   (fst (snd (snd (<≃sign q)))) ∘ invEq (0#sign q)


invℚInvol : ∀ q 0#q 0#invQ → invℚ (invℚ q 0#q) 0#invQ ≡ q
invℚInvol q 0#q 0#invQ =
  sym (·DistInvℚ (sign q) _ (fst (0#sign q) 0#q)
    (inl (snd ( ((0#→ℚ₊ q 0#q)) ⁻¹₊ )))
    0#invQ )
    ∙∙ cong₂ _·_ (sym (invℚ-sign q (fst (0#sign q) 0#q)))
     ((invℚ₊≡invℚ ( (0#→ℚ₊ q 0#q) ⁻¹₊) (inl (snd ( (0#→ℚ₊ q 0#q) ⁻¹₊)))
      ∙ invℚ₊-invol (0#→ℚ₊ q 0#q)) ∙  sym (abs'≡abs q))  ∙∙
     (·Comm (sign q) (abs q) ∙ (sign·abs q))



_／ℚ[_,_] : ℚ → ∀ r → 0 # r  → ℚ
q ／ℚ[ r , 0＃r ] = q · (invℚ r 0＃r)

x·invℚ[x] : ∀ q → (0#q : 0 # q) → q ／ℚ[ q , 0#q ] ≡ 1
x·invℚ[x] q 0#q =
  cong (_· invℚ q 0#q) (sym (sign·abs q))
  ∙ sym (·Assoc (abs q) (sign q)
      (sign q · fst ((0#→ℚ₊ q 0#q) ⁻¹₊)))
  ∙ cong {x = sign q · (sign q · fst ((0#→ℚ₊ q 0#q) ⁻¹₊))}
          {y = fst ((0#→ℚ₊ q 0#q) ⁻¹₊)}
          (abs q ·_)
       (·Assoc (sign q) (sign q) (fst ((0#→ℚ₊ q 0#q) ⁻¹₊))
       ∙∙ cong (_· fst ((0#→ℚ₊ q 0#q) ⁻¹₊)) (sign²≡1 q 0#q)
       ∙∙ ℚR.·IdL (fst ((0#→ℚ₊ q 0#q) ⁻¹₊)))
  ∙ cong (_· fst ((0#→ℚ₊ q 0#q) ⁻¹₊)) (abs'≡abs q)
  ∙ x·invℚ₊[x] (0#→ℚ₊ q 0#q)

x<z/₊y→y·x<z : ∀ x y z 
               → x < z ／₊ y
               → ((fst y) · x) < z
x<z/₊y→y·x<z x y z p = 
 subst (_ <_) ℚ!
  (·MonoL< x (z ／₊ y) (fst y) (snd y) p)


x/y<z→x<y·z : ∀ x y z
              → x ／₊ y < z
              → x < fst y · z
x/y<z→x<y·z x y z p =
  subst (_< fst y · z) ℚ!
    (<-o· _ _ (fst y) (snd y) p)

x<y·z→x/y<z : ∀ x y z
              → x < fst y · z
              → x ／₊ y < z
x<y·z→x/y<z x y z p =
  subst (x ／₊ y <_) ℚ!
    (<-·o _ _ (fst (y ⁻¹₊)) (snd (y ⁻¹₊)) p)


ℚ-x/y<z→x/z<y : ∀ x (q r : ℚ₊)
               → (x ／ℚ[ (fst r) , inl (snd r) ]) < fst q
               → (x ／ℚ[ (fst q) , inl (snd q) ]) < fst r
ℚ-x/y<z→x/z<y x q r p =
 subst2 _<_
   ℚ!
   ℚ!
   (<-·o _ _ _
     (0<-m·n _ _ (snd r) (invℚ-pos (fst q) (inl (snd q))  (snd q))) p)

invℚ≤invℚ : ∀ (p q : ℚ₊) → fst q ≤ fst p → fst ( p ⁻¹₊) ≤ fst (q ⁻¹₊)
invℚ≤invℚ p q x =
 subst2 _≤_ ℚ! ℚ!
    (≤-·o _ _ (fst (( p ⁻¹₊) ·₊ (q ⁻¹₊)))
     (0≤ℚ₊ ((p ⁻¹₊) ·₊ (q ⁻¹₊))) x)


invℚ<invℚ : ∀ (p q : ℚ₊) → fst q < fst p → fst ( p ⁻¹₊) < fst (q ⁻¹₊)
invℚ<invℚ p q x =
 subst2 _<_ ℚ! ℚ!
    (<-·o _ _ (fst (( p ⁻¹₊) ·₊ (q ⁻¹₊)))
     (snd ((p ⁻¹₊) ·₊ (q ⁻¹₊))) x)


invℚ<invℚ' : ∀ (p q : ℚ₊)  → fst ( p ⁻¹₊) < fst (q ⁻¹₊) → fst q < fst p
invℚ<invℚ' p q x =
 subst2 _<_ ℚ! ℚ!
    (<-·o _ _ (fst (( p) ·₊ (q)))
     (snd ((p) ·₊ (q))) x)


1/p+1/q : (p q : ℚ₊) → fst (p ⁻¹₊) - fst (q ⁻¹₊) ≡
                       fst ((p ·₊ q) ⁻¹₊)
                        · (fst q - fst p)
1/p+1/q _ _ = ℚ!


invℚ₊≤invℚ₊ : ∀ x y
      → fst y ≤ fst x
      → fst (x ⁻¹₊) ≤ fst ( y ⁻¹₊)
invℚ₊≤invℚ₊ x y p =
  subst2 _≤_
    ℚ! ℚ!
     (≤Monotone·-onNonNeg
      _ (fst ( y ⁻¹₊) · fst ( x ⁻¹₊)) _ _
        (≡Weaken≤ _ _ ℚ!!)
        p
        ((0≤ℚ₊ (( x ⁻¹₊) ·₊ (y ⁻¹₊))))
        ((0≤ℚ₊ y)))



invℚ₊-ℚ^ⁿ : ∀ q n → fst ((q ℚ₊^ⁿ n) ⁻¹₊) ≡ (fst (q ⁻¹₊)) ^ⁿ n
invℚ₊-ℚ^ⁿ q zero = refl
invℚ₊-ℚ^ⁿ q (suc n) =
  cong fst (sym (invℚ₊Dist· q ((q .fst ^ⁿ n) , 0<ℚ^ⁿ (q .fst) (q .snd) n)))
    ∙ cong (fst ∘ ((q ⁻¹₊) ·₊_))
     (ℚ₊≡ {x = ((q ℚ₊^ⁿ n) ⁻¹₊)}
      {y = (fst ( q ⁻¹₊) ^ⁿ n) , snd ((q ⁻¹₊) ℚ₊^ⁿ n)} (invℚ₊-ℚ^ⁿ q n))


ε<2ⁿ : (ε : ℚ₊) → Σ[ n ∈ ℕ ] fst ε < 2 ^ⁿ n
ε<2ⁿ ε =
  let n = fst (ℕ.log2ℕ (ℕ₊₁→ℕ  (fst (ceilℚ₊ ε)))) 
  in n , subst (fst ε <_) (sym (fromNat-^ 2 n))
          (isTrans< _ _ (fromNat (2 ℕ.^ n))
                  ((snd (ceilℚ₊ ε))) 
                   (<ℤ→<ℚ (ℤ.pos (ℕ₊₁→ℕ (fst (ceilℚ₊ ε)))) 
                     _ (ℤ.ℕ<→pos-<-pos _ _ ((fst (snd (ℕ.log2ℕ (ℕ₊₁→ℕ (fst (ceilℚ₊ ε)))))))))) 


1/2ⁿ<ε : (ε : ℚ₊) → Σ[ n ∈ ℕ ] [ 1 / 2 ] ^ⁿ n < fst ε
1/2ⁿ<ε ε =
 let (n , 1/ε<n) = ε<2ⁿ (ε ⁻¹₊)
 in n , subst (_< fst ε) (invℚ₊-ℚ^ⁿ 2 n ) 
         (invℚ<invℚ'  ε ((2 ℚ₊^ⁿ n) ⁻¹₊)
           (subst (fst (ε ⁻¹₊) <_) (sym (invℚ₊-invol (2 ℚ₊^ⁿ n))) 1/ε<n))

invℚ₊-<-invℚ₊ : ∀ q r → ((fst q) < (fst r))
             ≃ (fst (r ⁻¹₊) < fst (q ⁻¹₊))
invℚ₊-<-invℚ₊ (q , 0<q) (r , 0<r) = ElimProp2.go w q r 0<q 0<r
 where
 w : ElimProp2 λ q r → ∀ 0<q 0<r → (q < r) ≃
         (fst ( (r , 0<r) ⁻¹₊) < fst ( (q , 0<q) ⁻¹₊))
 w .ElimProp2.isPropB _ _ =
   isPropΠ2 λ _ _ → isOfHLevel≃ 1 (isProp< _ _) (isProp< _ _)
 w .ElimProp2.f (pos (suc n) , 1+ n') (pos (suc m) , 1+ m') u@(pos<pos x) v@(pos<pos x₁) = 
   propBiimpl→Equiv (isProp< _ _)  (isProp< _ _)
    (λ (inj a) → inj (subst2 ℤ._<_ (ℤ.·Comm (pos (suc n)) (pos (suc m')))
                                   (ℤ.·Comm (pos (suc m)) (pos (suc n'))) a))
    (λ (inj a) → inj (subst2 ℤ._<_ (ℤ.·Comm (pos (suc m')) (pos (suc n)))
                                   (ℤ.·Comm (pos (suc n')) (pos (suc m))) a))


lowerBoundℕ⁻¹ : ∀ (q : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] ([ 1 , k ] < fst q)
lowerBoundℕ⁻¹ q = 
 map-snd (subst ([ 1 , _ ] <_) (cong (fst ∘ (_⁻¹₊))
   (ℚ₊≡ {abs (fst ( q ⁻¹₊)) , 
     (subst (0 <_) (sym (0<→abs≡id _ (snd ( q ⁻¹₊))))
      (snd ( q ⁻¹₊)))}
    (0<→abs≡id _ (snd ( q ⁻¹₊)))) ∙ invℚ₊-invol q)  ∘S fst (invℚ₊-<-invℚ₊ _ [ _ / _ ]₊)) (boundℕ (fst ( q ⁻¹₊)))
