module Cubical.Data.Rationals.Order.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Fast.Base as ℤ using (ℤ;pos;negsuc;ℕ₊₁→ℤ)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Int.Fast.Properties as ℤ using ()
open import Cubical.Data.Int.Fast.Order as ℤ using ()
open import Cubical.Data.Int.Fast.Divisibility as ℤ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero;znots)
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.Rationals.Order

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Foundations.Powerset


open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection
import Cubical.Tactics.CommRingSolver.Imports as 𝓢
open import Cubical.Algebra.OrderedCommRing

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals


open PositiveRationals
open NonNegativeRationals
open PositiveHalvesℚ

open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)

0≤ℚ₊ : (ε : ℚ₊) → 0 ≤ fst ε
0≤ℚ₊ ε = <Weaken≤ 0 (fst ε) (ε .snd)

module ℚR where
 open RingStr (snd (CommRing→Ring ℚCommRing)) public
 open RingTheory (CommRing→Ring ℚCommRing) public

≠→0<abs : ∀ q r → ¬ q ≡ r → 0< abs (q - r)
≠→0<abs q r u with q ≟ r
... | lt x = isTrans<≤ 0 (r - q) (abs (q - r))
                 (-< q r x)
                   (subst (_≤ abs (q - r))
                     (-[x-y]≡y-x q r) $ ≤max' (q - r) (- (q - r)))
... | eq x = ⊥.rec (u x)
... | gt x = isTrans<≤ 0 (q - r) (abs (q - r))
                 (-< r q x) (≤max (q - r) (- (q - r)))


abs' : ℚ → ℚ
abs' = SQ.Rec.go w
 where
 w : SQ.Rec ℚ
 w .SQ.Rec.isSetB = isSetℚ
 w .SQ.Rec.f (a , b) = [ ℤ.pos (ℤ.abs a) , b ]
 w .SQ.Rec.f∼ (a , 1+ b) (a' , 1+ b') r = eq/ _ _
   ((sym (ℤ.pos·pos (ℤ.abs a) (suc b')) ∙
      cong ℤ.pos (sym (ℤ.abs· (a) (ℕ₊₁→ℤ (1+ b'))) ))
     ∙∙ cong (λ x → ℤ.pos (ℤ.abs x)) r
     ∙∙ sym ((sym (ℤ.pos·pos (ℤ.abs a') (suc b)) ∙
      cong ℤ.pos (sym (ℤ.abs· (a') (ℕ₊₁→ℤ (1+ b))) ))))

abs'≡abs : ∀ x → abs x ≡ abs' x
abs'≡abs = SQ.ElimProp.go λ where
  .SQ.ElimProp.isPropB _ → isSetℚ _ _
  .SQ.ElimProp.f (a , b) →
    abs [ a / b ]
                            ≡⟨⟩
    max [ a / b ] [ -1 ℤ.· a / 1 ·₊₁ b ]
                            ≡[ i ]⟨ max [ a / b ] [ ℤ.-1·x≡-x a i / ·₊₁-identityˡ b i ] ⟩
    max [ a / b ] [ ℤ.- a / b ]
                            ≡⟨⟩
    [ ℤ.max (a ℤ.· ℕ₊₁→ℤ b) (ℤ.- a ℤ.· ℕ₊₁→ℤ b) / b ·₊₁ b ]
                            ≡⟨ sym $ cong [_/ _ ] (ℤ.·DistPosLMax a (ℤ.- a) (ℕ₊₁→ℕ b)) ⟩
    [ ℤ.max a (ℤ.- a) ℤ.· (ℕ₊₁→ℤ b) / b ·₊₁ b ]
                            ≡⟨ ·CancelR b ⟩
    [ ℤ.max a (ℤ.- a) / b ]
                            ≡⟨ sym $ cong [_/ b ] (ℤ.abs-max a) ⟩
    _
                            ≡⟨⟩
    abs' [ a / b ]
                            ∎


ℤ+→ℚ+ : ∀ m n → [ m / 1 ] + [ n / 1 ] ≡ [ m ℤ.+ n / 1 ]
ℤ+→ℚ+ m n = eq/ _ _ ℤ!

ℤ-→ℚ- : ∀ m n → [ m / 1 ] - [ n / 1 ] ≡ [ m ℤ.- n / 1 ]
ℤ-→ℚ- m n = eq/ _ _ ℤ!

ℕ+→ℚ+ : ∀ m n → fromNat m + fromNat n ≡ fromNat (m ℕ.+ n)
ℕ+→ℚ+ m n = eq/ _ _ ℤ!

ℕ·→ℚ· : ∀ m n → fromNat m · fromNat n ≡ fromNat (m ℕ.· n)
ℕ·→ℚ· m n = eq/ _ _ ℤ!



sign : ℚ → ℚ
sign = Rec.go w
 where
 w : Rec _
 w .Rec.isSetB = isSetℚ
 w .Rec.f (p , _) = [ ℤ.sign p / 1 ]
 w .Rec.f∼ (ℤ.pos zero , (1+ nn)) (ℤ.pos zero , snd₂) x = refl
 w .Rec.f∼ (ℤ.pos zero , (1+ nn)) (ℤ.pos (suc n₁) , snd₂) x =
    ⊥.rec $ ℕ.znots $
     ℤ.injPos (x ∙ sym (ℤ.pos·pos (suc n₁) (suc nn)))
 w .Rec.f∼ (ℤ.pos (suc n₁) , snd₁) (ℤ.pos zero , (1+ nn)) x =
   ⊥.rec $ ℕ.znots $
     ℤ.injPos (sym x ∙ sym (ℤ.pos·pos (suc n₁) (suc nn)))
 w .Rec.f∼ (ℤ.pos (suc n) , snd₁) (ℤ.pos (suc n₁) , snd₂) x = refl
 w .Rec.f∼ (ℤ.pos n₁ , snd₂) (ℤ.negsuc n , snd₁) x =
    ⊥.rec (
     𝟚.toWitnessFalse
      {Q = (ℤ.discreteℤ _ _)}
       tt ((cong (ℤ.-_) (ℤ.pos·pos (suc n) (ℕ₊₁→ℕ snd₂))
        ∙ sym (ℤ.negsuc·pos n _)) ∙∙ (sym x) ∙∙ sym (ℤ.pos·pos n₁ _) ))
 w .Rec.f∼ (ℤ.negsuc n , snd₁) (ℤ.pos n₁ , snd₂) x =
   ⊥.rec (
     𝟚.toWitnessFalse
      {Q = (ℤ.discreteℤ _ _)}
       tt ((cong (ℤ.-_) (ℤ.pos·pos (suc n) (ℕ₊₁→ℕ snd₂))
        ∙ sym (ℤ.negsuc·pos n (ℕ₊₁→ℕ snd₂))) ∙∙ x ∙∙ sym (ℤ.pos·pos n₁ _) ))
 w .Rec.f∼ (ℤ.negsuc n , snd₁) (ℤ.negsuc n₁ , snd₂) x = refl

-- x+x≡2x : ∀ x → x + x ≡ 2 · x
-- x+x≡2x x = ℚ!!



<- : ∀ q r  → 0 < r - q → q < r
<- q r x = subst2 _<_ (+IdL _) ℚ!!
    (<-+o 0 (r - q) q x)

≤- : ∀ q r  → 0 ≤ r - q → q ≤ r
≤- q r x = subst2 _≤_ (+IdL _) ℚ!!
    (≤-+o 0 (r - q) q x)

-- TODO - integrate with solver
decℚ? : ∀ {x y} → {𝟚.True (discreteℚ x y)} →  (x ≡ y)
decℚ? {_} {_} {p} = 𝟚.toWitness p

decℚ<? : ∀ {x y} → {𝟚.True (<Dec x y)} →  (x < y)
decℚ<? {_} {_} {p} = 𝟚.toWitness p

decℚ≤? : ∀ {x y} → {𝟚.True (≤Dec x y)} →  (x ≤ y)
decℚ≤? {_} {_} {p} = 𝟚.toWitness p


0<sucN : ∀ n → 0 < fromNat (suc n)
0<sucN n = <ℤ→<ℚ _ _ (ℤ.pos<pos tt)

0<pos : ∀ n m → 0 < [ pos (suc n) / m ]
0<pos n m = pos<pos tt


0≤pos : ∀ n m → 0 ≤ [ pos n / m ]
0≤pos n m = inj (subst (0 ℤ.≤_)
   (sym (ℤ.·IdR _))
  (ℤ.zero-≤pos {n}))


-fromNat : ∀ n → fromNeg n ≡ - fromNat n
-fromNat zero = refl
-fromNat (suc n) = cong [_/ 1 ] (sym (ℤ.-1·x≡-x _))

neg≤pos : ∀ n m → fromNeg n ≤ fromNat m
neg≤pos n m =
 subst (_≤ fromNat m) (sym (-fromNat n))
  (isTrans≤ _ 0 (fromNat m) ((minus-≤ 0 (fromNat n) (0≤pos n 1))) (0≤pos m 1))

floor-lemma : ∀ p q → fromNat (ℕ.quotient p / (suc q))
                   + [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ]
                   ≡ [ ℤ.pos p / 1+ q ]
floor-lemma p q = eq/ _ _
     (cong {x = (ℤ.pos (ℕ.quotient p / (suc q)) ℤ.· (ℕ₊₁→ℤ (1+ q))
        ℤ.+ ℤ.pos (ℕ.remainder p / (suc q)) ℤ.· ℤ.pos 1)}
          (ℤ._· (ℕ₊₁→ℤ (1+ q))) (ℤ! ∙ cong ℤ.pos (ℕ.≡remainder+quotient (suc q) p))
       ∙ ℤ!)
       

absComm- : ∀ x y → abs (x - y) ≡ abs (y - x)
absComm- x y i = maxComm (-[x-y]≡y-x y x (~ i)) (-[x-y]≡y-x x y i) i



<≃sign : ∀ x → ((0 < x) ≃ (sign x ≡ 1))
               × ((0 ≡ x) ≃ (sign x ≡ 0))
                 × ((x < 0) ≃ (sign x ≡ -1))
<≃sign = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB _ =
  isProp× (isOfHLevel≃ 1 (isProp< _ _) (isSetℚ _ _))
     (isProp× (isOfHLevel≃ 1 (isSetℚ _ _) (isSetℚ _ _))
         (isOfHLevel≃ 1 (isProp< _ _) (isSetℚ _ _))
       )
 w .ElimProp.f (ℤ.pos zero , (1+ n)) =
  propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    ((λ (inj x₁) → ⊥.rec $ ℤ.isIrrefl< x₁))
      (λ x → ⊥.rec $ ℕ.znots (ℤ.injPos (eq/⁻¹ _ _ x))) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     (λ _ → refl) (λ _ → eq/ _ _ refl) ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ (inj x) → ⊥.rec (ℤ.¬-pos<-zero x))
          (λ x → ⊥.rec $ ℤ.posNotnegsuc _ _ ((eq/⁻¹ _ _ x))))

 w .ElimProp.f (ℤ.pos (suc n) , snd₁) =
   propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    (λ _ → refl) (λ _ → pos<pos _) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     ((λ b → ⊥.rec
      (znots $ ℤ.injPos (b ∙ ℤ.·IdR (ℤ.pos (suc n))))) ∘S eq/⁻¹ _ _)
     (λ x → ⊥.rec (ℕ.snotz $ ℤ.injPos (eq/⁻¹ _ _ x)))  ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ (inj x) → ⊥.rec (ℤ.¬-pos<-zero (subst (ℤ._< 0)
         (sym (ℤ.pos·pos (suc n) 1)) x)))
          λ x → ⊥.rec (ℤ.posNotnegsuc _ _ (eq/⁻¹ _ _ x)))

 w .ElimProp.f (ℤ.negsuc n , snd₁) =
   propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
    ((λ (inj x₁) → ⊥.rec $
   ℤ.¬pos≤negsuc (subst ((ℤ.pos 1) ℤ.≤_) (ℤ.negsuc·pos n 1 ∙
    cong ℤ.-_ (sym (ℤ.pos·pos (suc n) 1)) ) (ℤ.<→suc≤ x₁))))
     ((λ x → ⊥.rec (ℤ.posNotnegsuc 1 0 (sym x))) ∘S eq/⁻¹ _ _) ,
   (propBiimpl→Equiv (isSetℚ _ _) (isSetℚ _ _)
     ((λ x → ⊥.rec (ℤ.posNotnegsuc _ _
     (eq/⁻¹ _ _ x ∙ ℤ.·IdR (ℤ.negsuc n)))))
     ((⊥.rec ∘ ℤ.posNotnegsuc _ _ ∘ sym ) ∘S eq/⁻¹ _ _ )  ,
      propBiimpl→Equiv (isProp< _ _) (isSetℚ _ _)
        (λ _ → refl)
         λ _ → negsuc<pos)


<→sign : ∀ x → (0 < x → sign x ≡ 1)
               × (0 ≡ x → sign x ≡ 0)
                 × (x < 0 → sign x ≡ -1)
<→sign x =
 let ((y , _) , (y' , _) , (y'' , _)) = <≃sign x
 in (y , y' , y'')

abs≡sign· : ∀ x → abs x ≡ x · (sign x)
abs≡sign· x = abs'≡abs x ∙ ElimProp.go w x
 where
 w : ElimProp (λ z → abs' z ≡ z · sign z)
 w .ElimProp.isPropB _ = isSetℚ _ _
 w .ElimProp.f x@(ℤ.pos zero , snd₁)    = decℚ?
 w .ElimProp.f x@(ℤ.pos (suc n) , snd₁) = sym (·CancelR 1)
 w .ElimProp.f x@(ℤ.negsuc n , snd₁)    = sym (·CancelR 1)

absPos : ∀ x → 0 < x → abs x ≡ x
absPos x 0<x = abs≡sign· x ∙∙ cong (x ·_) (fst (<→sign x) 0<x)  ∙∙ (·IdR x)

absNonNeg : ∀ x → 0 ≤ x → abs x ≡ x
absNonNeg x 0<x with x ≟ 0
... | lt x₁ = ⊥.rec $ ≤→≯ 0 x 0<x x₁
... | eq x₁ = cong abs x₁ ∙ sym x₁
... | gt x₁ = absPos x x₁


absNeg : ∀ x → x < 0 → abs x ≡ - x
absNeg x x<0 = abs≡sign· x ∙∙ cong (x ·_) (snd (snd (<→sign x)) x<0)
                 ∙∙ ·Comm x -1


data Trichotomy0· (m n : ℚ) : Type₀ where
  eqₘ₌₀ : m ≡ 0 → m · n ≡ 0  → Trichotomy0· m n
  eqₙ₌₀ : n ≡ 0 → m · n ≡ 0 → Trichotomy0· m n
  lt-lt : m < 0 → n < 0 → 0 < m · n  → Trichotomy0· m n
  lt-gt : m < 0 → 0 < n → m · n < 0  → Trichotomy0· m n
  gt-lt : 0 < m → n < 0 → m · n < 0  → Trichotomy0· m n
  gt-gt : 0 < m → 0 < n → 0 < m · n  → Trichotomy0· m n

trichotomy0· : ∀ m n → Trichotomy0· m n
trichotomy0· m n with m ≟ 0 | n ≟ 0
... | eq p | _    = eqₘ₌₀ p (cong (_· n) p ∙ ·AnnihilL n)
... | _    | eq p = eqₙ₌₀ p (cong (m ·_) p ∙ ·AnnihilR m)
... | lt x₁ | lt x₂ = lt-lt x₁ x₂
  (subst (0 <_) (-·- m n)
    (0<-m·n (- m) (- n) (minus-< m 0 x₁) (minus-< n 0 x₂)))
... | lt x₁ | gt x₂ = lt-gt x₁ x₂
 ((subst (m · n <_) (·AnnihilL n) $ <-·o m 0 n x₂ x₁ ))
... | gt x₁ | lt x₂ = gt-lt x₁ x₂
 (subst (m · n <_) (·AnnihilR m) $ <-o· n 0 m x₁ x₂ )
... | gt x₁ | gt x₂ = gt-gt x₁ x₂ (0<-m·n m n x₁ x₂)

sign·sign : ∀ x y → sign x · sign y ≡ sign (x · y)
sign·sign x y = h $ trichotomy0· x y

 where

 x' = <→sign x
 y' = <→sign y
 x·y' = <→sign (x · y)

 h : Trichotomy0· x y → _ -- ·AnnihilL
 h (eqₘ₌₀ p p₁) =
  cong (_· sign y) (fst (snd x') (sym p))
   ∙∙ ℚ!! ∙∙ sym (fst (snd x·y') (sym p₁))
 h (eqₙ₌₀ p p₁) =   cong (sign x ·_) (fst (snd y') (sym p))
   ∙∙ ℚ!! ∙∙ sym (fst (snd x·y') (sym p₁))
 h (lt-lt p p₁ p₂) = cong₂ _·_ (snd (snd x') p) (snd (snd y') p₁)
  ∙ (sym $ fst x·y' p₂)
 h (lt-gt p p₁ p₂) = cong₂ _·_  (snd (snd x') p) (fst y' p₁)
          ∙ sym (snd (snd x·y') p₂)
 h (gt-lt p p₁ p₂) = cong₂ _·_ (fst x' p) (snd (snd y') p₁)
          ∙ sym (snd (snd x·y') p₂)
 h (gt-gt p p₁ p₂) = cong₂ _·_ (fst x' p) (fst y' p₁)
  ∙ (sym $ fst x·y' p₂)


abs·abs : ∀ x y → abs x · abs y ≡ abs (x · y)
abs·abs x y = cong₂ _·_ (abs≡sign· x) (abs≡sign· y)
 ∙∙ (sym (·Assoc x (sign x) (y · sign y))) ∙∙
  cong (x ·_) (( (·Assoc (sign x) y (sign y))) ∙∙
  congS (_· sign y) (·Comm (sign x) y) ∙∙ (sym (·Assoc y (sign x) (sign y))))
   ∙∙ (·Assoc x y (sign·sign x y i0))
 ∙∙ (λ i → x · y · sign·sign x y i) ∙ sym (abs≡sign· (x · y))


0≤x² : ∀ x → 0 ≤ x · x
0≤x² = ElimProp.go w
 where
 w : ElimProp (λ z → 0 ≤ z · z)
 w .ElimProp.isPropB _ = isProp≤ _ _
 w .ElimProp.f (p , q) = inj (subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.0≤x² p))


abs² : ∀ x → abs x · abs x ≡ x · x 
abs² x = abs·abs x x ∙ absNonNeg (x · x) (0≤x² x)

abs'·abs' : ∀ x y → abs' x · abs' y ≡ abs' (x · y)
abs'·abs' x y = cong₂ _·_ (sym (abs'≡abs x)) (sym (abs'≡abs y))
  ∙∙ abs·abs x y ∙∙ abs'≡abs (x · y)

pos·abs : ∀ x y → 0 ≤ x →  abs (x · y) ≡ x · (abs y)
pos·abs x y 0≤x = sym (abs·abs x y) ∙ cong (_· (abs y))
  (absNonNeg x 0≤x)


absCases : (q : ℚ) → (abs q ≡ - q) ⊎ (abs q ≡ q)
absCases q with (- q) ≟ q
... | lt x = inr (maxComm q (- q) ∙ (≤→max (- q) q $ <Weaken≤ (- q) q x))
... | eq x = inr (maxComm q (- q) ∙ (≤→max (- q) q $ ≡Weaken≤ (- q) q x))
... | gt x = inl (≤→max q (- q) (<Weaken≤ q (- q) x) )

byAbsCases : ∀ {ℓ} (q : ℚ) → {P : ℚ → Type ℓ} → P (- q) → P q → P (abs q)  
byAbsCases q {P} P-q Pq = ⊎.rec (λ p → subst P (sym p) P-q) (λ p → subst P (sym p) Pq) (absCases q)

distFromℤ : ∀ m n →  abs ([ m / 1 ] - [ n / 1 ]) < 1 → m ≡ n
distFromℤ m = ℤ.byTrichotomy m w
 where
 open ℤ.TrichotomyRec
 
 h : (m n : ℤ) → n ℤ.< m → abs ([ m / 1 ] - [ n / 1 ]) < 1 → m ≡ n
 h m n n<m ∣m-n∣<1 = ⊥.rec (≤→≯ _ _
    (≤ℤ→≤ℚ _ _ (ℤ.<→suc≤ n<m)) (subst {x = 1 + [ n / 1 ]} ([ m / 1 ] <_)
      (ℚ! ∙ λ i → [ (ℤ.sucℤ≡1+ n (~ i)) / 1 ]) (<≤ℚ![ m-n<1 ] )))
  where
  m-n<1 :  ([ m / 1 ] - [ n / 1 ]) < 1
  m-n<1  = subst (_< 1) (absPos ([ m / 1 ] - [ n / 1 ])
    (<≤ℚ![ <ℤ→<ℚ _ _ n<m ])) ∣m-n∣<1 
  
 w : ℤ.TrichotomyRec m _
 w .lt-case = h m
 w .eq-case _ = refl
 w .gt-case n m<n x =
   sym (h n m m<n (subst (_< 1) (absComm- [ m / 1 ] [ n / 1 ]) x))
   
record Floor (x : ℚ) : Type₀ where
 no-eta-equality
 field
  integralPart : ℤ
  fractionalPart : ℚ₀₊
  x≡ip+fp : x ≡ [ integralPart / 1 ] + fst (fractionalPart)
  fp<1 : fst fractionalPart < 1

unquoteDecl FloorIsoΣ = declareRecordIsoΣ FloorIsoΣ (quote Floor)



isPropFloor : ∀ x → isProp (Floor x) 
isPropFloor x = isOfHLevelRetractFromIso 1 FloorIsoΣ $ w
 where
  w : isProp _
  w (integralPart₀ , fractionalPart₀ ,  x≡ip+fp₀ , fp<1₀)
    (integralPart₁ , fractionalPart₁ ,  x≡ip+fp₁ , fp<1₁) =
      ΣPathP (iP₀=iP₁ , ΣPathP (fP₀=fP₁ ,
              isProp→PathP (λ i → isProp× (isSetℚ _ _) (isProp< _ _))  _ _))
    where

    p :   [ integralPart₀ / 1 ] - [ integralPart₁ / 1 ]
        ≡ fst fractionalPart₁ - fst fractionalPart₀
    p = ℚR.equalByDifference ([ integralPart₀ / 1 ] - [ integralPart₁ / 1 ])
         _ (ℚ!! ∙ sym (cong₂ _-_ (x≡ip+fp₀) (x≡ip+fp₁)) ∙ ℚ!!)

    iP₀=iP₁ : integralPart₀ ≡ integralPart₁
    iP₀=iP₁ = distFromℤ _ _ (subst (_< 1) (sym (cong abs p))
                 (byAbsCases (fst fractionalPart₁ - fst fractionalPart₀)
                  {_< 1} (<≤ℚ![ fp<1₀ ]) (<≤ℚ![ fp<1₁ ])))
                  
    fP₀=fP₁ : fractionalPart₀ ≡ fractionalPart₁
    fP₀=fP₁ = sym $ ℚ₀₊≡ (ℚR.equalByDifference _ _
                (sym p ∙ ℚR.differenceByEqual _ _ (cong [_/ 1 ] iP₀=iP₁)))
    


∙floor : ∀ {x y} → x ≡ y → Floor x → Floor y
∙floor p f = f'
 where
 open Floor ; module F = Floor f
 f' : _
 f' .integralPart = F.integralPart
 f' .fractionalPart = F.fractionalPart 
 f' .x≡ip+fp = sym p ∙ F.x≡ip+fp
 f' .fp<1 = F.fp<1

pqFloor₊ : ∀ p q → Floor [ pos p / q ]
pqFloor₊ p (1+ q) = rf
 where
 open Floor

 rf : _
 rf .integralPart = pos (ℕ.quotient p / (suc q))
 rf .fractionalPart = [ ℤ.pos (ℕ.remainder p / (suc q)) / 1+ q ]
   , inj (subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.zero-≤pos {remainder p / suc q}))
 rf .x≡ip+fp = sym (floor-lemma p q)
 rf .fp<1 = inj (subst2 ℤ._<_
     (sym (ℤ.·IdR (pos (remainder p / suc q)))) (sym (ℤ.·IdL (pos (suc q))))
     (ℤ.suc≤→< (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.mod< q p))))

pqFloor : ∀ p q → Floor [ p / q ]
pqFloor (pos p) q = pqFloor₊ p q
pqFloor (negsuc n) q = decRec rf
 (rf' ∘S (≤→¬≡→< 0 (fst F₊.fractionalPart) (snd F₊.fractionalPart) ))
 (discreteℚ 0 (fst F₊.fractionalPart))

 where
  open Floor ; module F₊ = Floor (pqFloor₊ (suc n) q)

  module _ (p : 0 ≡ fst (F₊.fractionalPart)) where
   rf : Floor [ negsuc n / q ]    
   rf .integralPart = ℤ.- F₊.integralPart
   rf .fractionalPart = 0
   rf .x≡ip+fp =
      ℚ! ∙∙ cong -_ (F₊.x≡ip+fp
           ∙ cong ([ F₊.integralPart / 1 ] +_) (sym p)) ∙∙ ℚ!

   rf .fp<1 = inj (ℤ.pos<pos tt)

  module _ ((F₊fp , _) : ℚ₊) (F₊fp<1 : F₊fp < 1) where
   lem1 : 0 ≤ - (F₊fp - 1)
   lem1 = <≤ℚ![ F₊fp<1 ]
   lem2 :  - (F₊fp - 1) < 1
   lem2 = <≤ℚ!
   
  module _ (0<fp : 0 < fst F₊.fractionalPart) where
   rf' : Floor [ negsuc n / q ]

   rf' .integralPart = ℤ.- (1 ℤ.+ F₊.integralPart)
   rf' .fractionalPart = (- (fst F₊.fractionalPart - 1) ,
     lem1 (_ , 0<fp) F₊.fp<1)
   rf' .x≡ip+fp = ℚ! ∙∙ cong -_ (F₊.x≡ip+fp) ∙∙ ℚ!
   rf' .fp<1 = lem2 (_ , 0<fp) F₊.fp<1
    


floorℚ : ∀ x → Floor x
floorℚ = ElimProp.go w
 where
 w : ElimProp _
 w .ElimProp.isPropB = isPropFloor
 w .ElimProp.f (p , q) = pqFloor p q  

floor-fracℚ₊ : ∀ (x : ℚ₊) → Σ (ℕ × ℚ) λ (k , q) →
                       (fromNat k + q ≡ fst x ) × ((0 ≤ q)  × (q < 1))
floor-fracℚ₊ (x , 0<x) =
 let fx = floorℚ x
     (p , q) = lem fx (x≡ip+fp fx)
 in (p , fst (fx .fractionalPart)) ,
    cong (λ z → [ z / 1 ] + fst (fractionalPart fx)) q
     ∙ sym (fx .x≡ip+fp) , snd (fractionalPart fx)  , fx .fp<1

 where
  open Floor
  lem : (f : Floor x) → x ≡ [ integralPart f / 1+ 0 ] + fst (fractionalPart f)
           →  Σ[ k ∈ ℕ ] pos k ≡ f .integralPart
  lem f p with f .integralPart
  ... | pos n = _ , refl
  ... | negsuc n = ⊥.rec (isAsym< _ _
     (isTrans<≤ _ _ _ (<-o+ _ _ [ negsuc _ / 1 ] (f .fp<1))
       (≤minus→≤ _ _ (subst {x = [ pos n / 1 ]} (0 ≤_) ℚ!  (inj (ℤ.pos≤pos tt))))
       )
     (subst (0 <_) p 0<x))

ceilℚ₊ : (q : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] (fst q) < fromNat (ℕ₊₁→ℕ k)
ceilℚ₊ q = 

 1+ (fst (fst (floor-fracℚ₊ q))) ,
    subst2 (_<_) --  (fromNat (suc (fst (fst (floor-fracℚ₊ q)))))
       (+Comm (floor-fracℚ₊ q .fst .snd) _ ∙ fst (snd (floor-fracℚ₊ q)))
       ((ℕ+→ℚ+ 1 _))
        (<-+o _ _ (fromNat (fst (fst (floor-fracℚ₊ q))))
          (snd (snd (snd (floor-fracℚ₊ q)))))





-- -- -- 0≤abs : ∀ x → 0 ≤ abs x
-- -- -- 0≤abs x with x ≟ 0
-- -- -- ... | lt x₁ = subst (0 ≤_) (sym (absNeg x x₁)) ((<Weaken≤ 0 (- x) (minus-< x 0 x₁) ))
-- -- -- ... | eq x₁ = subst ((0 ≤_) ∘ abs) (sym x₁) (isRefl≤ 0)
-- -- -- ... | gt x₁ = subst (0 ≤_) (sym (absPos x x₁)) (<Weaken≤ 0 x x₁)


-- -- -- 0≤x² : ∀ x → 0 ≤ x · x
-- -- -- 0≤x² = ElimProp.go w
-- -- --  where
-- -- --  w : ElimProp (λ z → 0 ≤ z · z)
-- -- --  w .ElimProp.isPropB _ = isProp≤ _ _
-- -- --  w .ElimProp.f (p , q) = inj (subst (0 ℤ.≤_) (sym (ℤ.·IdR _)) (ℤ.0≤x² p))

-- -- -- signX·signX : ∀ x → 0 # x → sign x · sign x ≡ 1
-- -- -- signX·signX x y = sign·sign x x ∙
-- -- --    fst (fst (<≃sign (x · x)))
-- -- --     (⊎.rec (λ z → 0<-m·n _ _ z z)
-- -- --       ((λ z → subst (0 <_) (-·- x x) (0<-m·n (- x) (- x) z z)) ∘S minus-< x 0) y)


absFrom≤×≤ : ∀ ε q →
                - ε ≤ q
                → q ≤ ε
                → abs q ≤ ε
absFrom≤×≤ ε q x x₁ with absCases q
... | inl x₂ = subst2 (_≤_) (sym x₂) (-Invol ε) (minus-≤ (- ε) q x  )
... | inr x₂ = subst (_≤ ε) (sym x₂) x₁


absFrom<×< : ∀ ε q →
                - ε < q
                → q < ε
                → abs q < ε
absFrom<×< ε q x x₁ with absCases q
... | inl x₂ = subst2 (_<_) (sym x₂) (-Invol ε) (minus-< (- ε) q x  )
... | inr x₂ = subst (_< ε) (sym x₂) x₁


abs+pos : ∀ x y → 0 < x → abs (x + y) ≤ x + abs y
abs+pos x y x₁ with y ≟ 0
... | lt x₂ =
 let xx = (≤-o+ y (- y) x
            (<Weaken≤ y (- y) $ isTrans< y 0 (- y) x₂ ((minus-< y 0 x₂))))
 in subst (λ yy → abs (x + y) ≤ x + yy)
        (sym (absNeg y x₂)) (absFrom≤×≤ (x - y) _
          (subst (_≤ x + y)
            (sym (-Distr' x y)) (≤-+o (- x) x y
             (<Weaken≤ (- x) x $ isTrans< (- x) 0 x (minus-< 0 x x₁) x₁))) xx)
... | eq x₂ = subst2 _≤_ (sym (absPos x x₁)
        ∙ cong abs (sym (+IdR x) ∙ cong (x +_) ( (sym x₂))))
   (sym (+IdR x) ∙ cong (x +_) (cong abs (sym x₂))  ) (isRefl≤ x)
... | gt x₂ = subst2 _≤_ (sym (absPos _ (<Monotone+ 0 x 0 y x₁ x₂)))
    (cong (x +_) (sym (absPos y x₂)))
   $ isRefl≤ (x + y)


abs+≤abs+abs : ∀ x y → abs (x + y) ≤ abs x + abs y
abs+≤abs+abs x y with (x ≟ 0) | (y ≟ 0)
... | _ | gt x₁ = subst2 (_≤_)
                   (cong abs (+Comm y x))
            ((+Comm y (abs x)) ∙ cong ((abs x) +_ ) (sym (absPos y x₁)))
             (abs+pos y x x₁)
... | eq x₁ | _ = subst2 _≤_ (cong abs (sym (+IdL y) ∙
    cong (_+ y) (sym x₁) ))
                    (sym (+IdL (abs y)) ∙
                     cong (_+ (abs y)) (cong abs (sym x₁)))
                      (isRefl≤ (abs y))
... | gt x₁ | _ = subst (abs (x + y) ≤_)
            (cong (_+ (abs y)) (sym (absPos x x₁)))
              (abs+pos x y x₁)
... | lt x₁ | lt x₂ =
  subst2 _≤_ (sym (-Distr x y) ∙ sym (absNeg (x + y)
    (<Monotone+ x 0 y 0 x₁ x₂)))
     (cong₂ _+_ (sym (absNeg x x₁)) (sym (absNeg y x₂))) (isRefl≤ ((- x) - y) )
... | lt x₁ | eq x₂ =
  subst2 _≤_ ((cong abs (sym (+IdR x) ∙
    cong (x +_) (sym x₂))))
     (sym (+IdR (abs x)) ∙
                     cong ((abs x) +_ ) (cong abs (sym x₂)))
    ((isRefl≤ (abs x)))


clamp≤ : ∀ L L' x → clamp L L' x ≤ L'
clamp≤ L L' x = min≤' (max L x) L'


≤cases : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
≤cases x y with x ≟ y
... | lt x₁ = inl (<Weaken≤ _ _ x₁)
... | eq x₁ = inl (≡Weaken≤ _ _ x₁)
... | gt x₁ = inr (<Weaken≤ _ _ x₁)

elimBy≤ : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x y → x ≤ y → A x y)
  → ∀ x y → A x y
elimBy≤ s f x y = ⊎.rec
  (f _ _ ) (s _ _ ∘ f _ _ ) (≤cases x y)

-- -- -- elim≤By≡⊎< : ∀ {ℓ} (a : ℚ) {A : ∀ x → a ≤ x → Type ℓ}
-- -- --   → (A a (isRefl≤ a))
-- -- --   → (∀ x a<x → A x (<Weaken≤ _ _ a<x)  )
-- -- --   → ∀ x a<x → A x a<x
-- -- -- elim≤By≡⊎< a {A = A} r f x =
-- -- --   ⊎.rec
-- -- --     (λ a=x → subst (uncurry A) (Σ≡Prop (isProp≤ a) a=x) r)
-- -- --     (subst (A x) (isProp≤ a x _ _) ∘ f x)
-- -- --     ∘ (≤→≡⊎< a x)

-- -- -- elimBy≡⊎< : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
-- -- --   → (∀ x y → A x y → A y x)
-- -- --   → (∀ x → A x x)
-- -- --   → (∀ x y → x < y → A x y)
-- -- --   → ∀ x y → A x y
-- -- -- elimBy≡⊎< {A = A} s r f =
-- -- --  elimBy≤ s (λ x y → ⊎.rec (λ p → subst (A x) p (r x)) (f x y) ∘ ≤→≡⊎< x y)


-- -- -- max< : ∀ x y z → x < z → y < z → max x y < z
-- -- -- max< = elimBy≤
-- -- --   (λ x y X z y<z x<z → subst (_< z) (maxComm x y) (X z x<z y<z) )
-- -- --   λ x y x≤y z x<z y<z →
-- -- --     subst (_< z) (sym (≤→max x y x≤y)) y<z

maxDistMin : ∀ x y z → min (max x y) z ≡ max (min x z) (min y z)
maxDistMin = elimBy≤
 (λ x y p z → cong (flip min z) (maxComm y x)  ∙∙ p z ∙∙
                maxComm (min x z) (min y z) )
 λ x y p z → cong (flip min z) (≤→max x y p) ∙
   sym (≤→max (min x z) (min y z) (≤MonotoneMin x y z z p (isRefl≤ z) ))



minDistMax : ∀ x y y' → max x (min y y') ≡ min (max x y) (max x y')
minDistMax x = elimBy≤
  (λ y y' X → cong (max x) (minComm y' y) ∙∙ X ∙∙ minComm (max x y) (max x y'))
  λ y y' y≤y' → cong (max x) (≤→min _ _ y≤y') ∙
    sym (≤→min (max x y) (max x y')
      (≤MonotoneMax x x y y' (isRefl≤ x) y≤y'))

≤clamp : ∀ L L' x → L ≤ L' →  L ≤ clamp L L' x
≤clamp L L' x y =
 subst (L ≤_) (cong (λ y → max y _) (sym $ ≤→min L L' y)
      ∙ sym (maxDistMin L x L')) (≤max L (min x L'))

clamped≤ : ∀ L L' x → L ≤ x → clamp L L' x ≤ x
clamped≤ L L' x L≤x = subst (_≤ x)
  (cong (flip min L') (sym (≤→max L x L≤x))) (min≤ x L')

-- -- -- abs'Comm- : ∀ x y → abs' (x - y) ≡ abs' (y - x)
-- -- -- abs'Comm- x y = sym (abs'≡abs (x - y)) ∙∙ absComm- x y ∙∙ abs'≡abs (y - x)

≤MonotoneClamp : ∀ L L' x y → x ≤ y → clamp L L' x ≤ clamp L L' y
≤MonotoneClamp L L' x y p =
 ≤MonotoneMin
  (max L x) (max L y) L'
   L' (≤MonotoneMax L L x y (isRefl≤ L) p) (isRefl≤ L')



inClamps : ∀ L L' x → L ≤ x → x ≤ L' → clamp L L' x ≡ x
inClamps L L' x u v =
  cong (λ y → min y L') (≤→max L x u)
    ∙ ≤→min x L' v

-- -- -- ≤abs : ∀ x → x ≤ abs x
-- -- -- ≤abs x = ≤max x (- x)

-- -- -- ≤abs' : ∀ x → x ≤ abs' x
-- -- -- ≤abs' x = subst (x ≤_) (abs'≡abs x) (≤abs x)


<→ℚ₊ : ∀ x y → x < y → ℚ₊
<→ℚ₊ x y x<y .fst = y - x
<→ℚ₊ x y x<y .snd = -< x y x<y


-ℚ₊<0 : (ε : ℚ₊) → - (fst ε) < 0
-ℚ₊<0 ε = minus-< 0 (fst ε) (snd ε)

-ℚ₊≤0 : (ε : ℚ₊) → - (fst ε) ≤ 0
-ℚ₊≤0 ε = <Weaken≤ (- (fst ε)) 0 (minus-< 0 (fst ε) (snd ε))

-abs : ∀ x → abs x ≡ abs (- x)
-abs x = maxComm x (- x)
  ∙ cong (max (- x)) (sym (-Invol x))

-abs' : ∀ x → abs' x ≡ abs' (- x)
-abs' x = sym (abs'≡abs x) ∙∙ -abs x ∙∙ abs'≡abs (- x)

-- -- -- -≤abs' : ∀ x → - x ≤ abs' x
-- -- -- -≤abs' x = subst (- x ≤_) (sym (-abs' x)) (≤abs' (- x))

-- -- -- -≤abs : ∀ x → - x ≤ abs x
-- -- -- -≤abs x = subst (- x ≤_) (sym (-abs x)) (≤abs (- x))


-- -- -- absTo≤×≤ : ∀ ε q
-- -- --                 → abs q ≤ ε
-- -- --                 → (- ε ≤ q) × (q ≤ ε)

-- -- -- absTo≤×≤ ε q abs[q]≤ε .fst =
-- -- --  subst (- ε ≤_) (-Invol q) (minus-≤ _ _ (isTrans≤ _ _ _ (-≤abs q) abs[q]≤ε))
-- -- -- absTo≤×≤ ε q abs[q]≤ε .snd = isTrans≤ _ _ _ (≤abs q) abs[q]≤ε


Dichotomyℚ : ∀ (n m : ℚ) → (n ≤ m) ⊎ (m < n)
Dichotomyℚ n m = decRec inr (inl ∘ ≮→≥ _ _) (<Dec m n)

sign·abs : ∀ x → abs x · (sign x) ≡ x
sign·abs x with 0 ≟ x
... | lt x₁ =
 cong₂ _·_ (absPos x x₁) (fst (<→sign x) x₁)
    ∙ ·IdR x
... | eq x₁ = cong (abs x ·_) ( (fst (snd (<→sign x)) x₁))
 ∙ ·AnnihilR (abs x) ∙ x₁
... | gt x₁ =
  cong₂ _·_ (absNeg x x₁) (snd (snd (<→sign x)) x₁)
    ∙ -·- x 1 ∙ ·IdR x

opaque
 0#→0<abs' : ∀ q → 0 # q → 0 < abs' q
 0#→0<abs' q (inl x) =
   subst (0 <_) (sym (absPos q x) ∙ (abs'≡abs q)) x
 0#→0<abs' q (inr y) =
   subst (0 <_) (sym (absNeg q y) ∙ (abs'≡abs q)) (minus-< q 0 y)

0#→ℚ₊ : ∀ q → 0 # q → ℚ₊
0#→ℚ₊ q x = abs' q ,  (0#→0<abs' q x)

·Monotone0# : ∀ q q' → 0 # q → 0 # q' → 0 # (q · q')
·Monotone0# q q' (inl x) (inl x₁) =
 inl ( (·0< q q' (x) ( x₁)))
·Monotone0# q q' (inl x) (inr x₁) =
  inr (minus-<' 0 (q · q')
        (subst {x = q · - q'} {y = - (q · q')} (0 <_) ℚ!!
         ( (·0< q (- q') ( x) ( (minus-< q' 0 x₁)))) ))
·Monotone0# q q' (inr x) (inl x₁) =
  inr (minus-<' 0 (q · q')
     (subst (0 <_) (sym (·Assoc -1 q q'))
       (( (·0< (- q) q' ( (minus-< q 0 x)) ( x₁))))))
·Monotone0# q q' (inr x) (inr x₁) =
 inl (subst (0 <_) (-·- q q') (
     (·0< (- q) (- q') ( (minus-< q 0 x)) ( (minus-< q' 0 x₁)))) )



0#sign : ∀ q → 0 # q ≃ 0 # (sign q)
0#sign q =
 propBiimpl→Equiv (isProp# _ _) (isProp# _ _)
   (⊎.map (((flip (subst (0 <_))
     (𝟚.toWitness {Q = <Dec 0 1} _)) ∘ sym) ∘S fst (<→sign q))
     ((((flip (subst (_< 0))
     (𝟚.toWitness {Q = <Dec -1 0} _)) ∘ sym) ∘S snd (snd (<→sign q)))))
     (⊎.rec (⊎.rec ((λ y z → ⊥.rec (isIrrefl# (sign q) (subst (_# (sign q))
        (sym y) z))) ∘S fst (snd (<→sign q))) (const ∘ inl) ∘ ≤→≡⊎< _ _ ) (λ x _ → inr x)
      (Dichotomyℚ 0 q))


-- -- -- -- ceil-fracℚ₊ : ∀ (x : ℚ₊) → Σ (ℕ × ℚ) λ (k , q) →
-- -- -- --                        (fromNat k + q ≡ fst x ) × (q < 1)
-- -- -- -- ceil-fracℚ₊ = {!!}

boundℕ : ∀ q → Σ[ k ∈ ℕ₊₁ ] (abs q < ([ ℕ₊₁→ℤ k , 1 ]))
boundℕ q =
  ⊎.rec (λ x → 1 , subst (_< 1) x (decℚ<? {0} {1}))
        (λ x →  let ((k , f) , e , e' , e'') = floor-fracℚ₊ (abs q ,  x)
                in
                 (1+ k , subst2 (_<_)
                         (+Comm f _ ∙ e)
                          (ℕ+→ℚ+ 1 k) ((<-+o f 1 [ pos k / 1+ 0 ] e''))))
    (≤→≡⊎< 0 (abs q) (0≤abs q))
    


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



elimBy≡⊎<' : ∀ {ℓ} {A : ℚ → ℚ → Type ℓ}
  → (∀ x y → A x y → A y x)
  → (∀ x → A x x)
  → (∀ x (ε : ℚ₊) → A x (x + fst ε))
  → ∀ x y → A x y
elimBy≡⊎<' {A = A} s r f' =
 elimBy≤ s (λ x y → ⊎.rec (λ p → subst (A x) p (r x)) (f x y) ∘ ≤→≡⊎< x y)

 where
 f : ∀ x y → x < y → A x y
 f x y v = subst (A x) ℚ!! $ f' x (y - x , <≤ℚ![ v ])


riseQandD : ∀ p q r → Path ℚ ([ p / q ]) ([ p ℤ.· ℕ₊₁→ℤ r / (q ·₊₁ r) ])
riseQandD p q r = ℚ!


+MaxDistrℚ : ∀ x y z → (max x y) + z ≡ max (x + z) (y + z)
+MaxDistrℚ = SQ.elimProp3 (λ _ _ _ → isSetℚ _ _)
  $ uncurry λ a a' → uncurry λ b b' → uncurry λ c c' →
   let zzz' : ∀ a' b' c' →
            (ℤ.max (a ℤ.· b') (b ℤ.· a') ℤ.· (pos c') ℤ.+ c ℤ.· (a' ℤ.· b'))
                 ≡
            (ℤ.max ((a ℤ.· (pos c') ℤ.+ c ℤ.· a') ℤ.· b')
                   ((b ℤ.· (pos c') ℤ.+ c ℤ.· b') ℤ.· a'))
       zzz' a' b' c' =
            cong (ℤ._+ _) (ℤ.·DistPosLMax (a ℤ.· b') (b ℤ.· a') c' ∙
              cong₂
               {x = a ℤ.· b' ℤ.· pos c'}
               {a ℤ.· pos c' ℤ.· b'}
               ℤ.max ℤ! ℤ!)
          ∙∙ ℤ.+DistLMax (a ℤ.· pos c' ℤ.· b') (b ℤ.· pos c' ℤ.· a') (c ℤ.· (a' ℤ.· b'))
          ∙∙ cong₂ ℤ.max ℤ! ℤ!
       z* = _

   in congS (SQ.[_] ∘S (_, a' ·₊₁ b' ·₊₁ c'))
        (  congS ((λ ab → ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a')
             ℤ.· pos (suc (ℕ₊₁.n c')) ℤ.+
             ab) ∘ (c ℤ.·_)) (ℤ.pos·pos (ℕ₊₁→ℕ a') (ℕ₊₁→ℕ b'))
              ∙ zzz' (ℕ₊₁→ℤ a') (ℕ₊₁→ℤ b') (suc (ℕ₊₁.n c')))
        ∙∙ (sym (·IdR z*) ∙ cong (z* ·_)
            (eq/ _ ( ℕ₊₁→ℤ c' , c' )
          (ℤ.·Comm (pos (ℕ₊₁→ℕ one)) (ℕ₊₁→ℤ c'))) ) ∙∙

        cong₂ [_/_]
               ((ℤ.·DistPosLMax
                 ((a ℤ.· pos (suc (ℕ₊₁.n c')) ℤ.+ c ℤ.· ℕ₊₁→ℤ a') ℤ.· ℕ₊₁→ℤ b')
                 ((b ℤ.· pos (suc (ℕ₊₁.n c')) ℤ.+ c ℤ.· ℕ₊₁→ℤ b') ℤ.· ℕ₊₁→ℤ a')
             (suc (ℕ₊₁.n c'))) ∙ cong₂
            ℤ.max ℤ! ℤ!)
            (ℕ₊₁→ℕ-inj (ℤ.injPos ℤ!))



+MinDistrℚ : ∀ x y z → (min x y) + z ≡ min (x + z) (y + z)
+MinDistrℚ = SQ.elimProp3 (λ _ _ _ → isSetℚ _ _)
  $ uncurry λ a a' → uncurry λ b b' → uncurry λ c c' →
   let z : ∀ a' b' c' →
              (ℤ.min (a ℤ.· pos b') (b ℤ.· pos a') ℤ.· pos c'
                 ℤ.+ c ℤ.· (pos a' ℤ.· pos b')) ℤ.· pos c'
               ≡
               ℤ.min
                ((a ℤ.· pos c' ℤ.+ c ℤ.· pos a') ℤ.· (pos b' ℤ.· pos c'))
                ((b ℤ.· pos c' ℤ.+ c ℤ.· pos b') ℤ.· (pos a' ℤ.· pos c'))

       z a' b' c' =
            _ ≡⟨ ℤ! ∙  ((λ i → (ℤ.·DistPosLMin (a ℤ.· pos b') (b ℤ.· pos a') (c' ℕ.· c') i
                 ℤ.+ c ℤ.· (pos a' ℤ.· pos b') ℤ.· pos c')  )) ⟩
            _ ≡⟨ ℤ.+DistLMin (a ℤ.· pos b' ℤ.· pos (c' ℕ.· c'))
                             (b ℤ.· pos a' ℤ.· pos (c' ℕ.· c'))
                             (c ℤ.· (pos a' ℤ.· pos b') ℤ.· pos c') ⟩
            _ ≡⟨ cong₂ ℤ.min ℤ! ℤ! ⟩
             _ ∎
   in riseQandD
         (ℤ.min (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· ℕ₊₁→ℤ c' ℤ.+
               c ℤ.· ℕ₊₁→ℤ (a' ·₊₁ b')) ( a' ·₊₁ b' ·₊₁ c') c'
            ∙ 
              (cong₂ [_/_]
                 ((λ i →
                      (ℤ.min (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· ℕ₊₁→ℤ c' ℤ.+
                         c ℤ.· ℤ.pos·pos (ℕ₊₁→ℕ a') (ℕ₊₁→ℕ b') (i))
                        ℤ.· ℕ₊₁→ℤ c' )
                   ∙∙ z (suc (ℕ₊₁.n a')) (suc (ℕ₊₁.n b')) (suc (ℕ₊₁.n c'))
                   ∙∙ cong₂ ℤ.min ℤ! ℤ!)
                 (ℕ₊₁→ℕ-inj (ℤ.injPos ℤ!)))
                    --


<MonotoneMax : ∀ m o n s → m < n → o < s → max m o < max n s
<MonotoneMax =
  elimBy≤ (λ x y X o s u v → subst2 _<_ (maxComm x y) (maxComm s o)
                 ((X s o) v u))
   λ x y x≤y n s _ y<s →
     subst (_< max n s) (sym (≤→max x y x≤y))
      (isTrans<≤ _ _ _ y<s (≤max' n s))

<MonotoneMin : ∀ n s m o  → m < n → o < s → min m o < min n s
<MonotoneMin =
  elimBy≤ (λ x y X o s u v → subst2 _<_ (minComm s o) (minComm x y)
                 ((X s o) v u))
   λ x y x≤y n s n<x _ →
     subst (min n s <_) (sym (≤→min x y x≤y))
       (isTrans≤< _ _ _ (min≤ n s) n<x)


clampDelta : ∀ L L' x → clamp L L' x ≡
               (x + clamp (L - x) (L' - x) 0)
clampDelta L L' x =
     cong₂ min
       (cong₂ {x = L} {y = (L - x) + x} max (ℚ!!) {x} {0 + x}
         (sym $ +IdL x) ∙ sym (+MaxDistrℚ (L - x) 0 x))
       (ℚ!!)
  ∙∙ sym (+MinDistrℚ (max (L - x) 0) (L' - x) x)
  ∙∙ +Comm (min (max (L - x) 0) (L' - x)) x



clampDiff : ∀ L L' x y → x ≤ y →
    clamp L L' y - clamp L L' x ≤ y - x
clampDiff L L' x y z =
  (subst2 _≤_
     ((sym ℚ!!) ∙
       cong₂ _-_ (sym $ clampDelta L L' y)
                   (sym $ clampDelta L L' x))
     (+IdR (y - x))
     (≤-o+ ((a' - a)) 0 (y - x)
      (subst (_≤ 0) (-[x-y]≡y-x a a')
       $ minus-≤ 0 (a - a') (-≤ a' a zz'))  ))

 where

 a = clamp (L - x) (L' - x) 0
 a' = clamp (L - y) (L' - y) 0
 zz' : a' ≤ a
 zz' = ≤MonotoneMin _ _ _ _
          (≤MonotoneMax _ _ _ _
           (≤-o+ (- y) (- x) L (minus-≤ x y z)) (isRefl≤ 0)
            ) (≤-o+ (- y) (- x) L' $ minus-≤ x y z)


minDiff : ∀ L' x y → x ≤ y →
    min y L' - min x L' ≤ y - x
minDiff L' x y x≤y =
 subst (_≤ (y - x))
    (cong₂ _-_
     (cong (flip min L') (≤→max x y x≤y ))
     (cong (flip min L') (maxIdem x)))
     (clampDiff x L' x y x≤y)


clampDist' : ∀ L L' x y → x ≤ y →
    abs (clamp L L' y - clamp L L' x) ≤ abs (y - x)
clampDist' L L' x y z =
 subst2 _≤_
  (sym (absNonNeg (clamp L L' y - clamp L L' x)
          (-≤ _ _ (≤MonotoneClamp L L' x y z))))
  (sym (absNonNeg (y - x)
    (-≤ x y z)
    ))
  (clampDiff L L' x y z)

clampDist : ∀ L L' x y →
    abs (clamp L L' y - clamp L L' x) ≤ abs (y - x)
clampDist L L' =
 elimBy≤ (λ x y → subst2 _≤_ (absComm- (clamp L L' y) (clamp L L' x))
    (absComm- y x)) (clampDist' L L')

maxDist : ∀ M x y →
    abs (max M y - max M x) ≤ abs (y - x)
maxDist M x y =
  subst2 {x = min (max M y) (max M (max x y))}
          {(max M y)}
    {z = min (max M x) (max M (max x y))} {(max M x)}
    (λ a b → abs (a - b) ≤ abs (y - x))
    (≤→min _ _ (subst (max M y ≤_)
      (sym (maxAssoc M y x) ∙ cong (max M) (maxComm y x))
      (≤max _ x)))
    (≤→min _ _
      ((subst (max M x ≤_)
      (sym (maxAssoc M x y))
      (≤max _ y))))
    (clampDist M (max M (max x y)) x y)


≤→<⊎≡ : ∀ p q → p ≤ q → (p ≡ q) ⊎ (p < q)
≤→<⊎≡ p q x with p ≟ q
... | lt x₁ = inr x₁
... | eq x₁ = inl x₁
... | gt x₁ = ⊥.rec $ ≤→≯ p q x x₁

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


·MaxDistrℚ : ∀ x y z → 0< z → (max x y) · z ≡ max (x · z) (y · z)
·MaxDistrℚ = SQ.elimProp3 (λ _ _ _ → isPropΠ λ _ → isSetℚ _ _)
  www

 where
 www : (a b c : ℤ.ℤ × ℕ₊₁) →
         0< _//_.[ c ] →
         max _//_.[ a ] _//_.[ b ] · _//_.[ c ] ≡
         max (_//_.[ a ] · _//_.[ c ]) (_//_.[ b ] · _//_.[ c ])
 www (a , a') (b , b') (c@(pos (suc n)) , c') (inj (ℤ.pos<pos x)) = eq/ _ _ wwww
  where


   wwww : ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· c
            ℤ.· ℕ₊₁→ℤ (a' ·₊₁ c' ·₊₁ (b' ·₊₁ c'))
          ≡ ℤ.max ((a ℤ.· c) ℤ.· ℕ₊₁→ℤ (b' ·₊₁ c'))
                    ((b ℤ.· c) ℤ.· ℕ₊₁→ℤ (a' ·₊₁ c'))  ℤ.·
              ℕ₊₁→ℤ (a' ·₊₁ b' ·₊₁ c')
   wwww =
    cong (ℤ.max (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n) ℤ.·_)
      (cong (λ ac → ℕ₊₁→ℤ (ac ·₊₁ (b' ·₊₁ c'))) (·₊₁-comm a'  c')
       ∙∙ cong ℕ₊₁→ℤ (sym (·₊₁-assoc c' a' (b' ·₊₁ c'))) ∙∙
         ℤ.pos·pos (suc (c' .ℕ₊₁.n)) (ℕ₊₁→ℕ (a' ·₊₁ (b' ·₊₁ c'))))
      ∙∙ ℤ! ∙∙
    cong₂ (ℤ._·_)
       (cong (ℤ._· (pos (ℕ₊₁→ℕ c')))
         (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ b') (b ℤ.· ℕ₊₁→ℤ a') (suc n))
         ∙ ℤ.·DistPosLMax
              ((a ℤ.· ℕ₊₁→ℤ b') ℤ.· pos (suc n))
              ((b ℤ.· ℕ₊₁→ℤ a') ℤ.· pos (suc n)) (ℕ₊₁→ℕ c')
          ∙ cong₂ ℤ.max ℤ! ℤ!)
           (cong ℕ₊₁→ℤ (·₊₁-assoc a' b' c'))


·MaxDistrℚ' : ∀ x y z → 0 ≤ z → (max x y) · z ≡ max (x · z) (y · z)
·MaxDistrℚ' x y z =
  ⊎.rec (λ p → cong ((max x y) ·_) (sym p) ∙
        ·AnnihilR (max x y)  ∙ cong₂ max (sym (·AnnihilR x) ∙ cong (x ·_) p)
            (sym (·AnnihilR y) ∙ cong (y ·_) p))
    (·MaxDistrℚ x y z) ∘ (≤→≡⊎< 0 z)

≤Monotone·-onNonNeg : ∀ x x' y y' →
  x ≤ x' →
  y ≤ y' →
  0 ≤ x →
  0 ≤ y →
   x · y ≤ x' · y'
≤Monotone·-onNonNeg x x' y y' x≤x' y≤y' 0≤x 0≤y =
  isTrans≤ _ _ _ (≤-·o x x' y 0≤y x≤x')
   (≤-o· y y' x' (isTrans≤ 0 _ _ 0≤x x≤x') y≤y')

<Monotone·-onPos : ∀ x x' y y' →
  x < x' →
  y < y' →
  0 ≤ x →
  0 ≤ y →
   x · y < x' · y'
<Monotone·-onPos x x' y y' x₁ x₂ x₃ x₄ =
   let zz = 0<-m·n (x' - x) (y' - y) (-< x x' x₁) (-< y y' x₂)
   in subst2 _<_ (+IdL _ ∙ +IdR _)
          (ℚ!!)
        (<≤Monotone+ 0 ((x' - x) · (y' - y)) (x · y + 0)
             (x' · y + ((x · (y' - y)))) zz
               (≤Monotone+ (x · y) (x' · y) 0  (x · (y' - y))
                (≤-·o x x' y x₄ (<Weaken≤ x x' x₁))
                (subst (_≤ x · (y' - y))
                  (·AnnihilL (y' - y)) $ ≤-·o 0 x (y' - y)
                  (<Weaken≤ 0 (y' - y) (-< y y' x₂) ) x₃)))


≤<Monotone·-onPos : ∀ x x' y y' →
  x ≤ x' →
  y < y' →
  0 < x →
  0 ≤ y →
   x · y < x' · y'
≤<Monotone·-onPos x x' y y' x≤x' y<y' 0<x 0≤y =
  isTrans≤< _ _ _
    (≤-·o x x' y 0≤y x≤x')
    (<-o· y y' x' (isTrans<≤ 0 _ _ 0<x x≤x') y<y')


invℚ : ∀ q → 0 # q → ℚ
invℚ q p = sign q · fst ((0#→ℚ₊ q p) ⁻¹₊)


invℚ₊≡invℚ : ∀ q p → invℚ (fst q) p ≡ fst (q ⁻¹₊)
invℚ₊≡invℚ q p = cong₂ _·_ (fst (<→sign (fst q)) (snd q))
   (cong (fst ∘ _⁻¹₊) (ℚ₊≡ (sym (abs'≡abs (fst q)) ∙
     absPos (fst q) ((snd q))))) ∙ ℚR.·IdL (fst ( q ⁻¹₊))
    
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

x<z/₊y→y·x<z : ∀ x y z 
               → x < z ／₊ y
               → ((fst y) · x) < z
x<z/₊y→y·x<z x y z p = 
 subst (_ <_) ℚ!
  (·MonoL< x (z ／₊ y) (fst y) (snd y) p)



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


maxWithPos : ℚ₊ → ℚ → ℚ₊
maxWithPos ε q .fst = max (fst ε) q
maxWithPos ε q .snd = 
 (isTrans<≤ 0 (fst ε) _ (snd ε) (≤max (fst ε) q))


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


clam∈ℚintervalℙ : ∀ a b → (a ≤ b) → ∀ x → clamp a b x ∈ ℚintervalℙ a b
clam∈ℚintervalℙ a b a≤b x = ≤clamp _ _ _ a≤b , (clamp≤ a _ x)

∈ℚintervalℙ→clam≡ : ∀ a b → ∀ x →
    x ∈ ℚintervalℙ a b → x ≡ clamp a b x
∈ℚintervalℙ→clam≡ a b x = sym ∘ uncurry (inClamps a b x)


clamp-contained-agree : ∀ (a b a' b' x : ℚ)
  → a ≤ a'
  → b' ≤ b
  → x ∈ ℚintervalℙ a' b'
  → clamp a b x ≡ clamp a' b' x
clamp-contained-agree a b a' b' x a≤a' b'≤b x∈ =
  sym (∈ℚintervalℙ→clam≡ a b x
   ((isTrans≤ _ _ _ a≤a' (fst x∈)) ,
    (isTrans≤ _ _ _ (snd x∈) b'≤b))) ∙ ∈ℚintervalℙ→clam≡ a' b' x x∈

module Exponentiationℚ =
  Exponentiation ℚCommRing renaming (_^_ to _^ⁿ_) 

open Exponentiationℚ using (_^ⁿ_) public 

0<ℚ^ⁿ : ∀ q (0<q : 0< q) n → 0< (q ^ⁿ n)
0<ℚ^ⁿ q 0<q zero = inj (ℤ.pos<pos tt)
0<ℚ^ⁿ q 0<q (suc n) = snd ((q , 0<q) ·₊  ((q ^ⁿ n) , 0<ℚ^ⁿ q 0<q n))

0≤ℚ^ⁿ : ∀ q (0≤q : 0 ≤ q) n → 0 ≤ (q ^ⁿ n)
0≤ℚ^ⁿ q 0≤q zero = 𝟚.toWitness {Q = ≤Dec 0 1} tt
0≤ℚ^ⁿ q 0≤q (suc n) = ≤Monotone·-onNonNeg
 0 _ 0 _
  0≤q (0≤ℚ^ⁿ q 0≤q n)
    (isRefl≤ 0) (isRefl≤ 0)


x^ⁿ≤1 : ∀ x n → 0 ≤ x → x ≤ 1 →  (x ^ⁿ n) ≤ 1
x^ⁿ≤1 x zero 0≤x x≤1 = isRefl≤ 1
x^ⁿ≤1 x (suc n) 0≤x x≤1 =
 ≤Monotone·-onNonNeg _ 1 _ 1
   x≤1 (x^ⁿ≤1 x n 0≤x x≤1)   0≤x (0≤ℚ^ⁿ x 0≤x n)

1≤x^ⁿ : ∀ x n → 1 ≤ x →  1 ≤ (x ^ⁿ n)
1≤x^ⁿ x zero 1≤x = isRefl≤ 1
1≤x^ⁿ x (suc n) 1≤x =
 ≤Monotone·-onNonNeg 1 _ 1 _
  1≤x (1≤x^ⁿ x n 1≤x) decℚ≤? decℚ≤?

1<x^ⁿ : ∀ x n → 1 < x →  1 < (x ^ⁿ (suc n))
1<x^ⁿ x zero 1<x = subst (1 <_) ℚ!! 1<x
1<x^ⁿ x (suc n) 1<x =
 <Monotone·-onPos 1 _ 1 _ 
   1<x (1<x^ⁿ x n 1<x)    (decℚ≤? {0} {1})
     (decℚ≤? {0} {1})


·-ℚ^ⁿ : ∀ n m x → (x ^ⁿ n) · (x ^ⁿ m) ≡ (x ^ⁿ (n ℕ.+ m))
·-ℚ^ⁿ zero m x = ℚ!!
·-ℚ^ⁿ (suc n) m x = ℚ!! ∙ cong (x ·_) (·-ℚ^ⁿ n m x)

_ℚ₊^ⁿ_ : ℚ₊ → ℕ → ℚ₊
(q , 0<q) ℚ₊^ⁿ n = (q ^ⁿ n) , 0<ℚ^ⁿ q 0<q n


fromNat-^ : ∀ m n → ((fromNat m) ^ⁿ n ) ≡ fromNat (m ℕ.^ n)
fromNat-^ m ℕ.zero = refl
fromNat-^ m (suc n) =   
 cong ((fromNat m) ·_) (fromNat-^ m n) ∙
   ℕ·→ℚ· m (m ℕ.^ n)

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


0^ⁿ :  ∀ n → 0 ^ⁿ (suc n) ≡ 0
0^ⁿ n = ℚR.0LeftAnnihilates (0 ^ⁿ n)

1^ⁿ :  ∀ n → 1 ^ⁿ n ≡ 1
1^ⁿ zero = refl
1^ⁿ (suc n) = ℚR.·IdL _ ∙ 1^ⁿ n




-1ⁿ : ℕ → ℚ
-1ⁿ zero = 1
-1ⁿ (suc zero) = -1
-1ⁿ (suc (suc x)) = -1ⁿ x

abs[-1ⁿ]≡1 : ∀ n → abs (-1ⁿ n) ≡ 1
abs[-1ⁿ]≡1 zero = refl
abs[-1ⁿ]≡1 (suc zero) = refl
abs[-1ⁿ]≡1 (suc (suc n)) = abs[-1ⁿ]≡1 n

-1ⁿ· : ℕ → ℚ → ℚ
-1ⁿ· zero x = x
-1ⁿ· (suc zero) = -_
-1ⁿ· (suc (suc n)) = -1ⁿ· n

-1ⁿ·-suc : ∀ n x → -1ⁿ· (suc n) x ≡ - (-1ⁿ· n x)
-1ⁿ·-suc zero x = refl
-1ⁿ·-suc (suc zero) x = sym (-Invol x)
-1ⁿ·-suc (suc (suc n)) x = -1ⁿ·-suc n x

-1ⁿ·-·2 : ∀ n x → -1ⁿ· (n ℕ.· 2) x ≡ x
-1ⁿ·-·2 zero x = refl
-1ⁿ·-·2 (suc n) x = -1ⁿ·-·2 n x

-1ⁿ-suc : ∀ n →  (-1ⁿ (suc n)) ≡ - ((-1ⁿ n))
-1ⁿ-suc zero = refl
-1ⁿ-suc (suc zero) = refl
-1ⁿ-suc (suc (suc n)) = -1ⁿ-suc n

-1ⁿ·≡· : ∀ n x → -1ⁿ· n x ≡  (-1ⁿ n) · x
-1ⁿ·≡· zero x = sym (ℚR.·IdL _)
-1ⁿ·≡· (suc zero) x = refl
-1ⁿ·≡· (suc (suc n)) x = -1ⁿ·≡· n x

absᵣ∘-1ⁿ· : ∀ n x → abs (-1ⁿ· n x) ≡ abs x
absᵣ∘-1ⁿ· zero x = refl
absᵣ∘-1ⁿ· (suc zero) x = abs- x
absᵣ∘-1ⁿ· (suc (suc n)) x = absᵣ∘-1ⁿ· n x


^ⁿ-odd : ∀ n x → - (x ^ⁿ suc (n ℕ.· 2)) ≡ ((- x) ^ⁿ suc (n ℕ.· 2))
^ⁿ-even : ∀ n x → (x ^ⁿ (n ℕ.· 2)) ≡ ((- x) ^ⁿ (n ℕ.· 2))

^ⁿ-even zero x = refl
^ⁿ-even (suc n) x = ·Assoc x x _ ∙
  cong₂ _·_ (sym (-·- x x)) (^ⁿ-even n x)
  ∙ sym (·Assoc (- x) (- x) _)

^ⁿ-odd n x =  sym (ℚR.-DistL· x _) ∙ cong ((- x) ·_)  (^ⁿ-even n x) 


seqSumUpTo : (ℕ → ℚ) → ℕ →  ℚ
seqSumUpTo s zero = 0
seqSumUpTo s (suc n) = s zero + seqSumUpTo (s ∘ suc) n


seqSumUpTo' : (ℕ → ℚ) → ℕ →  ℚ
seqSumUpTo' s zero = 0
seqSumUpTo' s (suc n) = seqSumUpTo' s n + s n

seqΣ : (ℕ → ℚ) → (ℕ → ℚ)
seqΣ = seqSumUpTo'


seqΣ' : (ℕ → ℚ) → (ℕ → ℚ)
seqΣ' = seqSumUpTo


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
     (subst (0 <_) (sym (absPos _ (snd ( q ⁻¹₊))))
      (snd ( q ⁻¹₊)))}
    (absPos _ (snd ( q ⁻¹₊)))) ∙ invℚ₊-invol q)  ∘S fst (invℚ₊-<-invℚ₊ _ [ _ / _ ]₊)) (boundℕ (fst ( q ⁻¹₊)))
