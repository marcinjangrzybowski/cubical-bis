module Cubical.Data.Rationals.Order.AbsoluteValue where

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

