module Cubical.Data.Rationals.Bisection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos·pos; pos0+; pos; negsuc; ℕ₊₁→ℤ) renaming
  (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; abs to ∣_∣ℤ ; sign to sgn)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.HITs.SetQuotients as SetQuotient renaming (_/_ to _//_)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc) renaming
  (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.NatPlusOne hiding (_+₁_)
open import Cubical.Data.Sigma renaming (_×_ to _Σ×_) 
open import Cubical.Data.Prod
open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.Data.Bool as 𝟚

open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.Base

open import Cubical.Data.Nat.GCD
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Coprime
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int.Fast using (ℤCommRing)

open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Inverse hiding (lowerBoundℕ⁻¹)
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Floor
open import Cubical.Data.Rationals.Order.Algebra

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties

open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)

open import Cubical.Tactics.CommRingSolver.OrderedReflection



seqΣ∘·2 : ∀ s n → seqΣ s (n ℕ.· 2) ≡
                  seqΣ (λ n → s (n ℕ.· 2) + s (suc (n ℕ.· 2))) n
seqΣ∘·2 s zero = refl
seqΣ∘·2 s (suc n) =
    sym (+Assoc (seqΣ s (n ·ℕ 2)) _ _)
  ∙ cong₂ _+_ (seqΣ∘·2 _ n) refl



lowerBoundℕ⁻¹ : ∀ (q : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] ([ 1 , k ] ≤ fst q)
lowerBoundℕ⁻¹ q = 
 let (m , n) , (_ , p) = reduced (fst q)
     w = subst (0 <_) (sym p) (snd q)
 in n , subst ([ 1 / n ] ≤_) p ([k/n]≤[k'/n] _ _ _
   (ℤ.<→suc≤ (0<[k/n]→0<k _ _ w)))
 

private
 variable
  ℓ : Level
  A : Type ℓ

preStep : A → A → A → Bool → (A × A)
preStep x mid _ false = x , mid
preStep _ mid y true = mid , y


IsCauchySequenceℚ : (ℕ → ℚ) → Type
IsCauchySequenceℚ s =
  ∀ (ε : ℚ₊) → Σ[ N ∈ ℕ ] (∀ m n → N ℕ.< n → N ℕ.< m →
    abs (s n - s m) <  (fst ε))


module GenericBisect (f : A → Bool) (nextA : A → A → A) where
 preGenericStep : A → A → A → (A × A)
 preGenericStep x mid y = preStep x mid y (f mid)
 
 step : (A × A) → (A × A)
 step (x , y) =
    preGenericStep x (nextA x y) y

  

 subStep : ℕ → A → A → A → Bool → (A × A)
 
 iterSteps stepsIter : A → A → ℕ → (A × A)
 stepsIter x y n = ℕ.iter' n step (x , y)
 iterSteps x y zero  = x , y
 iterSteps x y (suc n) = subStep n x mid y (f mid) 
  where
  mid = nextA x y

 

 subStep n x mid y false = iterSteps x mid n
 subStep n x mid y true = iterSteps mid y n

 

 iterSteps≡stepsIter : ∀ n a b →
   iterSteps a b n ≡ stepsIter a b n
 iterSteps≡stepsIter zero a b = refl
 iterSteps≡stepsIter (suc n) a b with (f (nextA a b))
 ... | false = iterSteps≡stepsIter n a (nextA a b) 
 ... | true = iterSteps≡stepsIter n (nextA a b) b
 
fastMean : ℚ → ℚ → ℚ
fastMean a b = reduce ([ 1 / 2 ] · (a + b))

module ℚBisect (f : ℚ → Bool) where
 open GenericBisect f fastMean public

 stepDist : (ℚ × ℚ) → ℚ
 stepDist ab = proj₂ ab - proj₁ ab

 distCases : ∀ a b →
   preStep a ([ 1 / 2 ] · (a + b)) b (f (fastMean a b))
   ≡ preStep a (fastMean a b) b (f (fastMean a b))
 distCases a b i = preStep a (reducedEqual ([ 1 / 2 ] · (a + b)) i) b
   (f (fastMean a b))
   
 distStep : ∀ ab → stepDist ab ≡ 2 · stepDist (step ab) 
 distStep (a , b) with f (fastMean a b) | (distCases a b)
 ... | false | p = ℚ!! ∙ cong ((2 ·_) ∘ stepDist) p
 ... | true | p = ℚ!! ∙ cong ((2 ·_) ∘ stepDist) p


 bisectDist' : ∀ n ab → stepDist ab ≡  (2 ^ⁿ n)
    · stepDist (ℕ.iter' n step ab)
 bisectDist' zero ab = ℚ!!
 bisectDist' (suc n) ab =
  distStep ab
   ∙ cong (2 ·_)
        (bisectDist' n (step ab))
   ∙ ·Assoc 2 (2 ^ⁿ n) _ 

 bisectDist : ∀ n a b → stepDist (a , b) ≡  (2 ^ⁿ n)
  · stepDist (iterSteps a b n)
 bisectDist n a b = bisectDist' n (a , b) ∙ cong (((2 ^ⁿ n) ·_) ∘ stepDist)
   (sym (iterSteps≡stepsIter n a b))

 module _ a b where


  StepInequalities : (ℚ × ℚ) → Type
  StepInequalities s = (proj₁ s ≤ proj₂ s)
       Σ× (a ≤ proj₁ s) Σ× (proj₂ s ≤ b)

  module _ (a≤b : a ≤ b) where
   private
    p = (reducedEqual ([ 1 / 2 ] · (a + b)))
    h₁ : [ 1 / 2 ] · (a + b) ≤ b
    h₁ = <≤ℚ![ a≤b ]
    h₂ : a ≤ [ 1 / 2 ] · (a + b)
    h₂ = <≤ℚ![ a≤b ]

   stepInequalities : StepInequalities (step (a , b))
   stepInequalities with f (fastMean a b) 
   ... | false = subst (a ≤_) p h₂ , isRefl≤ a , subst (_≤ b) p  h₁
   ... | true =
    subst (_≤ b) p  h₁ , subst (a ≤_) p h₂ , isRefl≤ b
 
 bisectMonotone' : ∀ a b → (a ≤ b) → ∀ n →
        StepInequalities a b (stepsIter a b n)

 bisectMonotone' a b a≤b zero = a≤b , isRefl≤ a , isRefl≤ b 
 bisectMonotone' a b a≤b (suc n) with (step (a , b))
  | bisectMonotone' 
         (proj₁ (step (a , b)))
         (proj₂ (step (a , b))) (fst (stepInequalities a b a≤b)) n
        | stepInequalities a b a≤b
 ... | a' , b' | u , v , w | u' , v' , w' =
     u
   , isTrans≤ _ _ _ v' v
    , isTrans≤ _ _ _ w w'
 
 bisectMonotone* : ∀ a b → (a ≤ b) → ∀ n n' → n ℕ.≤ n' →
        (proj₁ (stepsIter a b n) ≤ proj₁ (stepsIter a b n'))
     Σ× (proj₂ (stepsIter a b n') ≤ proj₂ (stepsIter a b n))
 
 bisectMonotone* a b a≤b (suc n) zero x = ⊥.rec (ℕ.snotz (ℕ.≤0→≡0 {suc n} x))
 bisectMonotone* a b a≤b zero n' x = snd (bisectMonotone' a b a≤b n')
 bisectMonotone* a b a≤b (suc n) (suc n') x with (step (a , b))
  | bisectMonotone*
         (proj₁ (step (a , b)))
         (proj₂ (step (a , b))) (fst (stepInequalities a b a≤b)) n n' (ℕ.predℕ-≤-predℕ x)
 ... | _ , _ | ww = ww


 bisectMonotone : ∀ a b → (a ≤ b) → ∀ n n' → n ℕ.≤ n' →
        (proj₁ (iterSteps a b n) ≤ proj₁ (iterSteps a b n'))
     Σ× (proj₂ (iterSteps a b n') ≤ proj₂ (iterSteps a b n))
 bisectMonotone a b a≤b n n' n≤n' =
  map-×
    (subst2 _≤_ (cong proj₁ (sym (iterSteps≡stepsIter n a b)))
                 (cong proj₁ (sym (iterSteps≡stepsIter n' a b))))
    (subst2 _≤_ (cong proj₂ (sym (iterSteps≡stepsIter n' a b)) )
                (cong proj₂ (sym (iterSteps≡stepsIter n a b)) ))
   $ bisectMonotone* a b a≤b n n' n≤n'
   
 module Solve a b (a<b : a < b) where

  a≤b = <Weaken≤ a b a<b
        
  bisectSequence : ∀ n → ℚ × ℚ
  bisectSequence n = iterSteps a b n

  bs = proj₁ ∘S bisectSequence

  bs↑ = proj₂ ∘S bisectSequence
  bs≤bs↑ : ∀ n → bs n ≤ bs↑ n
  bs≤bs↑ n = subst2 _≤_ (cong proj₁ (sym (iterSteps≡stepsIter n a b)))
       (cong proj₂ (sym (iterSteps≡stepsIter n a b)))
     (fst (bisectMonotone' a b a≤b n))

  1/2^n-ineq : ∀ m n →  n ℕ.< m  →
        [ 1 / 2 ] ^ⁿ m <  [ 1 / 2 ] ^ⁿ n
  1/2^n-ineq m n (m' , p) =
   let p' = sym (ℕ.+-suc m' n) ∙ p
   in subst2 _<_ (λ i → invℚ₊-ℚ^ⁿ 2 (p' i) i) (invℚ₊-ℚ^ⁿ 2 n)
      (invℚ<invℚ (2 ℚ₊^ⁿ (suc m' ℕ.+ n)) (2 ℚ₊^ⁿ n)
        (subst2 (_<_) (·IdR _) (·Comm (2 ^ⁿ n) _ ∙ Exponentiationℚ.·-of-^-is-^-of-+ 2 (suc m') n)
         (·MonoL< 1 (2 ^ⁿ (suc m')) (2 ^ⁿ n) (snd (2 ℚ₊^ⁿ n))
          (1<x^ⁿ 2 m'  (pos<pos tt)))))
  
  is2ⁿcauchy' :  ∀ N m n → m ℕ.≤ n → N ℕ.< n → N ℕ.< m  →
        abs (bs n - bs m) <  (b - a) · [ 1 / 2 ] ^ⁿ N
  is2ⁿcauchy' N m n m≤n N<n N<m =
    let u , v = bisectMonotone a b a≤b m n m≤n
        
        w = x=y/z→x·z=y _ (stepDist (iterSteps a b m)) ([ 1 / 2 ]₊ ℚ₊^ⁿ m)
             (bisectDist m a b ∙ cong (_· stepDist (iterSteps a b m))
              ((sym $ invℚ₊-ℚ^ⁿ [ 1 / 2 ]₊ m)) ∙
                 ·Comm (fst (([ 1 / 2 ]₊ ℚ₊^ⁿ m) ⁻¹₊))  (stepDist (iterSteps a b m)))
        
    in subst (_< _) (sym (0≤→abs≡id (bs n - bs m) (≤→0≤Δ _ _ u)))
         (isTrans≤< _ ((b - a) · [ 1 / 2 ] ^ⁿ m) _
           (isTrans≤ _ _ _ (+Mono≤ (bs n) (bs↑ m) (- bs m)
             (- bs m) (isTrans≤ _ (bs↑ n) _ (bs≤bs↑ n) v)
             (isRefl≤ _))
             (≡Weaken≤ _ _ (sym w)))
           (·MonoL<  _ _ (b - a) (<→0<Δ _ _ a<b) (1/2^n-ineq _ _ N<m) ))
  
  is2ⁿcauchy :  ∀ N  m n → N ℕ.< n → N ℕ.< m →
        abs (bs n - bs m) <  (b - a) · ([ 1 / 2 ] ^ⁿ N)
  is2ⁿcauchy N = ℕ.elimBy≤
    (λ x y A u v → subst (_< _) (abs-Comm (bs y) (bs x) ) (A v u))
      (is2ⁿcauchy' N)
  Δ : ℚ₊
  Δ = (b - a , <→0<Δ _ _ a<b)
  
  isCauchySequenceSolve : IsCauchySequenceℚ bs
  isCauchySequenceSolve ε =
    let (N , p) = 1/2ⁿ<ε (ε ₊／₊ Δ)
    in N , λ m n N<n N<m →
       isTrans< _ _ _ (is2ⁿcauchy N m n N<n N<m) (x<z/₊y→y·x<z _ Δ _ p)
  
-- -- elimBy≤

module ℚIncrFunBisect (a b : ℚ) (a<b : a < b) (f : ℚ → ℚ) (y : ℚ) where
 open ℚBisect (λ q → 𝟚.Dec→Bool (≤Dec (f q) y)) public
 open Solve a b a<b public

 -- fBisect : ℕ → ℚ
 -- fBisect n = proj₁ (iterSteps a b n)

 -- fBisectR : ℕ → ℤ Σ× ℕ
 -- fBisectR n = map-snd ℕ₊₁→ℕ (fst (reduced (proj₁ (iterSteps a b n))))

 
module ℚIncrFunBisectFamily (a b : ℚ) (a<b : a < b) (f : ℚ → ℚ) where
 module Run y = ℚIncrFunBisect a b a<b f y

 bs : ℚ → ℕ → ℚ
 bs y n = proj₁ (Run.iterSteps y a b n)

 bs↑ : ℚ → ℕ → ℚ
 bs↑ y n = proj₂ (Run.iterSteps y a b n)

 BracketsTarget : ℚ → Type
 BracketsTarget y = (f a ≤ y) Σ× (y ≤ f b)

 SlopeBoundedBelow : ℚ₊ → Type
 SlopeBoundedBelow L =
   ∀ x x' → a ≤ x → x ≤ x' → x' ≤ b →
     fst L · (x' - x) ≤ f x' - f x

 ≰→> : ∀ x y → ¬ (x ≤ y) → y < x
 ≰→> x y x≰y with x ≟ y
 ... | lt x<y = ⊥.rec (x≰y (<Weaken≤ _ _ x<y))
 ... | eq x≡y = ⊥.rec (x≰y (≡Weaken≤ _ _ x≡y))
 ... | gt y<x = y<x

 lowerEndpointValidIter : ∀ y l u n →
   f l ≤ y →
   f (proj₁ (Run.iterSteps y l u n)) ≤ y
 lowerEndpointValidIter y l u zero fl≤y = fl≤y
 lowerEndpointValidIter y l u (suc n) fl≤y with ≤Dec (f (fastMean l u)) y
 ... | yes fmid≤y = lowerEndpointValidIter y (fastMean l u) u n fmid≤y
 ... | no _ = lowerEndpointValidIter y l (fastMean l u) n fl≤y

 upperEndpointValidIter : ∀ y l u n →
   y ≤ f u →
   y ≤ f (proj₂ (Run.iterSteps y l u n))
 upperEndpointValidIter y l u zero y≤fu = y≤fu
 upperEndpointValidIter y l u (suc n) y≤fu with ≤Dec (f (fastMean l u)) y
 ... | yes _ = upperEndpointValidIter y (fastMean l u) u n y≤fu
 ... | no fmid≰y =
   upperEndpointValidIter y l (fastMean l u) n
     (<Weaken≤ _ _ (≰→> (f (fastMean l u)) y fmid≰y))

 bs-lower-valid : ∀ y → f a ≤ y → ∀ n → f (bs y n) ≤ y
 bs-lower-valid y fa≤y n = lowerEndpointValidIter y a b n fa≤y

 bs↑-upper-valid : ∀ y → y ≤ f b → ∀ n → y ≤ f (bs↑ y n)
 bs↑-upper-valid y y≤fb n = upperEndpointValidIter y a b n y≤fb

 intervalBoundsIter : ∀ y l u n →
   l ≤ u → a ≤ l → u ≤ b →
     (proj₁ (Run.iterSteps y l u n) ≤ proj₂ (Run.iterSteps y l u n))
       Σ× (a ≤ proj₁ (Run.iterSteps y l u n))
       Σ× (proj₂ (Run.iterSteps y l u n) ≤ b)
 intervalBoundsIter y l u zero l≤u a≤l u≤b = l≤u , a≤l , u≤b
 intervalBoundsIter y l u (suc n) l≤u a≤l u≤b with ≤Dec (f (fastMean l u)) y
 ... | yes _ =
   intervalBoundsIter y (fastMean l u) u n
     mid≤u
     (isTrans≤ _ _ _ a≤l l≤mid)
     u≤b
  where
   p = reducedEqual ([ 1 / 2 ] · (l + u))
   l≤mid : l ≤ fastMean l u
   l≤mid = subst (l ≤_) p <≤ℚ![ l≤u ]
   mid≤u : fastMean l u ≤ u
   mid≤u = subst (_≤ u) p <≤ℚ![ l≤u ]
 ... | no _ =
   intervalBoundsIter y l (fastMean l u) n
     l≤mid
     a≤l
     (isTrans≤ _ _ _ mid≤u u≤b)
  where
   p = reducedEqual ([ 1 / 2 ] · (l + u))
   l≤mid : l ≤ fastMean l u
   l≤mid = subst (l ≤_) p <≤ℚ![ l≤u ]
   mid≤u : fastMean l u ≤ u
   mid≤u = subst (_≤ u) p <≤ℚ![ l≤u ]

 intervalBounds : ∀ y n → (bs y n ≤ bs↑ y n) Σ× (a ≤ bs y n) Σ× (bs↑ y n ≤ b)
 intervalBounds y n = intervalBoundsIter y a b n (<Weaken≤ a b a<b) (isRefl≤ a) (isRefl≤ b)

 bs≤bs↑ : ∀ y n → bs y n ≤ bs↑ y n
 bs≤bs↑ y n = fst (intervalBounds y n)

 a≤bs : ∀ y n → a ≤ bs y n
 a≤bs y n = fst (snd (intervalBounds y n))

 bs↑≤b : ∀ y n → bs↑ y n ≤ b
 bs↑≤b y n = snd (snd (intervalBounds y n))

 a≤bs↑ : ∀ y n → a ≤ bs↑ y n
 a≤bs↑ y n = isTrans≤ _ _ _ (a≤bs y n) (bs≤bs↑ y n)

 bs≤b : ∀ y n → bs y n ≤ b
 bs≤b y n = isTrans≤ _ _ _ (bs≤bs↑ y n) (bs↑≤b y n)

 width : ℚ → ℕ → ℚ
 width y n = bs↑ y n - bs y n

 widthNonNeg : ∀ y n → 0 ≤ width y n
 widthNonNeg y n = -≤ (bs y n) (bs↑ y n) (bs≤bs↑ y n)

 divNonNeg : ∀ L q → 0 ≤ q → 0 ≤ q ／₊ L
 divNonNeg L q 0≤q =
   subst2 _≤_ ℚ! refl
     (≤-·o 0 q (fst (L ⁻¹₊)) (<Weaken≤ _ _ (snd (L ⁻¹₊))) 0≤q)

 absDivNonNeg : ∀ L q → 0 ≤ abs q ／₊ L
 absDivNonNeg L q = divNonNeg L (abs q) (0≤abs q)

 ≤self+ : ∀ x d → 0 ≤ d → x ≤ x + d
 ≤self+ x d 0≤d = <≤ℚ![ 0≤d ]

 slope≤→≤+／ : ∀ L x x' d →
   fst L · (x' - x) ≤ d →
   x' ≤ x + d ／₊ L
 slope≤→≤+／ L x x' d LΔ≤d =
   ≤minus→≤ x' (x + d ／₊ L) <≤ℚ![ Δ≤d/L ]
  where
   Δ≤d/L : x' - x ≤ d ／₊ L
   Δ≤d/L =
     ≤-·o-cancel (x' - x) (d ／₊ L) (fst L) (snd L)
       (subst2 _≤_ ℚ! ℚ! LΔ≤d)

 widthEq : ∀ y n → width y n ≡ (b - a) · ([ 1 / 2 ] ^ⁿ n)
 widthEq y n =
   sym (x=y/z→x·z=y _ (Run.stepDist y (Run.iterSteps y a b n))
     ([ 1 / 2 ]₊ ℚ₊^ⁿ n)
       (Run.bisectDist y n a b ∙
        cong (_· Run.stepDist y (Run.iterSteps y a b n))
          ((sym $ invℚ₊-ℚ^ⁿ [ 1 / 2 ]₊ n)) ∙
        ·Comm (fst (([ 1 / 2 ]₊ ℚ₊^ⁿ n) ⁻¹₊))
          (Run.stepDist y (Run.iterSteps y a b n))))

 width< : ∀ y N n → N ℕ.< n →
   width y n < (b - a) · ([ 1 / 2 ] ^ⁿ N)
 width< y N n N<n =
   isTrans≤< _ ((b - a) · ([ 1 / 2 ] ^ⁿ n)) _
     (≡Weaken≤ _ _ (widthEq y n))
     (·MonoL< _ _ (b - a) (<→0<Δ _ _ a<b)
       (Run.1/2^n-ineq y n N N<n))

 widthEventually< : ∀ y (ε : ℚ₊) →
   Σ[ N ∈ ℕ ] (∀ n → N ℕ.< n → width y n < fst ε)
 widthEventually< y ε =
   let Δ = (b - a , <→0<Δ _ _ a<b)
       (N , p) = 1/2ⁿ<ε (ε ₊／₊ Δ)
   in N , λ n N<n →
      isTrans< _ _ _
        (width< y N n N<n)
        (x<z/₊y→y·x<z _ Δ _ p)

 crossEndpoint≤ : ∀ L → SlopeBoundedBelow L →
   ∀ y z → BracketsTarget y → BracketsTarget z → y ≤ z →
   ∀ n m → bs y n ≤ bs↑ z m
 crossEndpoint≤ L slope y z y∈ z∈ y≤z n m =
   ≮→≥ (bs↑ z m) (bs y n) λ bs↑z<bsY →
     let LΔ≤fz-fy =
           slope (bs↑ z m) (bs y n)
             (a≤bs↑ z m)
             (<Weaken≤ _ _ bs↑z<bsY)
             (bs≤b y n)
         fz-fy≤0 : f (bs y n) - f (bs↑ z m) ≤ 0
         fz-fy≤0 =
           isTrans≤ _ _ _
             (≤-+o (f (bs y n)) y (- f (bs↑ z m))
               (bs-lower-valid y (fst y∈) n))
             (isTrans≤ _ _ _
               (≤-+o y z (- f (bs↑ z m)) y≤z)
               (subst ((z - f (bs↑ z m)) ≤_) (+InvR (f (bs↑ z m)))
                 (≤-+o z (f (bs↑ z m)) (- f (bs↑ z m))
                   (bs↑-upper-valid z (snd z∈) m))))
         0<LΔ : 0 < fst L · (bs y n - bs↑ z m)
         0<LΔ =
           ·0< (fst L) (bs y n - bs↑ z m)
             (snd L)
             (<→<minus _ _ bs↑z<bsY)
     in ≤→≯ _ _ (isTrans≤ _ _ _ LΔ≤fz-fy fz-fy≤0) 0<LΔ

 orderedUpperEstimate : ∀ L → SlopeBoundedBelow L →
   ∀ y z → BracketsTarget y → BracketsTarget z → y ≤ z →
   ∀ n m → bs z n ≤ bs↑ y m + (z - y) ／₊ L
 orderedUpperEstimate L slope y z y∈ z∈ y≤z n m
   with Dichotomyℚ (bs z n) (bs↑ y m)
 ... | inl bsZ≤bs↑Y =
   isTrans≤ _ _ _ bsZ≤bs↑Y
     (≤self+ (bs↑ y m) ((z - y) ／₊ L)
       (divNonNeg L (z - y) (-≤ y z y≤z)))
 ... | inr bs↑Y<bsZ =
   slope≤→≤+／ L (bs↑ y m) (bs z n) (z - y)
     (isTrans≤ _ _ _
       (slope (bs↑ y m) (bs z n)
         (a≤bs↑ y m)
         (<Weaken≤ _ _ bs↑Y<bsZ)
         (bs≤b z n))
       (isTrans≤ _ _ _
         (≤-+o (f (bs z n)) z (- f (bs↑ y m))
           (bs-lower-valid z (fst z∈) n))
         (≤-o+ (- f (bs↑ y m)) (- y) z
           (minus-≤ y (f (bs↑ y m))
             (bs↑-upper-valid y (snd y∈) m)))))

 endpoint≤upper+absSlope : ∀ L → SlopeBoundedBelow L →
   ∀ y z → BracketsTarget y → BracketsTarget z →
   ∀ n m → bs y n ≤ bs↑ z m + abs (y - z) ／₊ L
 endpoint≤upper+absSlope L slope y z y∈ z∈ n m
   with Dichotomyℚ z y
 ... | inl z≤y =
   subst (λ d → bs y n ≤ bs↑ z m + d ／₊ L)
     (sym (0≤→abs≡id (y - z) (-≤ z y z≤y)))
     (orderedUpperEstimate L slope z y z∈ y∈ z≤y n m)
 ... | inr y<z =
   isTrans≤ _ _ _
     (crossEndpoint≤ L slope y z y∈ z∈ (<Weaken≤ _ _ y<z) n m)
     (≤self+ (bs↑ z m) (abs (y - z) ／₊ L)
       (absDivNonNeg L (y - z)))

 diff≤→-≤diff : ∀ x y e → x - y ≤ e → - e ≤ y - x
 diff≤→-≤diff x y e x-y≤e =
   subst2 _≤_ refl ℚ! (minus-≤ (x - y) e x-y≤e)

 +-diff-comm : ∀ x y d → (x + d) - y ≡ d + (x - y)
 +-diff-comm x y d = ℚ!

 endpointDistance≤ : ∀ L → SlopeBoundedBelow L →
   ∀ y z → BracketsTarget y → BracketsTarget z →
   ∀ n m →
     abs (bs y n - bs z m)
       ≤ (abs (y - z) ／₊ L) + (width y n + width z m)
 endpointDistance≤ L slope y z y∈ z∈ n m =
   absFrom≤×≤ _ _
     (diff≤→-≤diff (bs z m) (bs y n) e lowerDiff≤)
     upperDiff≤
  where
   d = abs (y - z) ／₊ L
   wy = width y n
   wz = width z m
   e = d + (wy + wz)

   finYZ : bs y n ≤ bs↑ z m + d
   finYZ = endpoint≤upper+absSlope L slope y z y∈ z∈ n m

   finZY : bs z m ≤ bs↑ y n + d
   finZY =
     subst (λ q → bs z m ≤ bs↑ y n + q ／₊ L)
       (abs-Comm z y)
       (endpoint≤upper+absSlope L slope z y z∈ y∈ m n)

   wz≤wy+wz : wz ≤ wy + wz
   wz≤wy+wz =
     subst (wz ≤_) (+Comm wz wy)
       (≤self+ wz wy (widthNonNeg y n))

   wy≤wy+wz : wy ≤ wy + wz
   wy≤wy+wz = ≤self+ wy wz (widthNonNeg z m)

   upperDiff≤ : bs y n - bs z m ≤ e
   upperDiff≤ =
     isTrans≤ _ _ _
       (≤-+o (bs y n) (bs↑ z m + d) (- bs z m) finYZ)
       (isTrans≤ _ _ _
         (≡Weaken≤ _ _ (+-diff-comm (bs↑ z m) (bs z m) d))
         (≤-o+ wz (wy + wz) d wz≤wy+wz))

   lowerDiff≤ : bs z m - bs y n ≤ e
   lowerDiff≤ =
     isTrans≤ _ _ _
       (≤-+o (bs z m) (bs↑ y n + d) (- bs y n) finZY)
       (isTrans≤ _ _ _
         (≡Weaken≤ _ _ (+-diff-comm (bs↑ y n) (bs y n) d))
         (≤-o+ wy (wy + wz) d wy≤wy+wz))

 half+half≡ : ∀ ε → fst (ε /2₊) + fst (ε /2₊) ≡ fst ε
 half+half≡ ε = ℚ!

 widthsEventually< : ∀ y z (ε : ℚ₊) →
   Σ[ N ∈ ℕ ] (∀ n m → N ℕ.< n → N ℕ.< m →
     width y n + width z m < fst ε)
 widthsEventually< y z ε =
   let (Ny , wy) = widthEventually< y (ε /2₊)
       (Nz , wz) = widthEventually< z (ε /2₊)
       N = ℕ.max Ny Nz
   in N , λ n m N<n N<m →
      subst (width y n + width z m <_) (half+half≡ ε)
        (<Monotone+ _ _ _ _
          (wy n (ℕ.≤<-trans (ℕ.left-≤-max {Ny} {Nz}) N<n))
          (wz m (ℕ.≤<-trans (ℕ.right-≤-max {Ny} {Nz}) N<m)))

 bsLimitLipschitz : ∀ L → SlopeBoundedBelow L →
   ∀ y z → BracketsTarget y → BracketsTarget z →
   (ε : ℚ₊) →
   Σ[ N ∈ ℕ ] (∀ n m → N ℕ.< n → N ℕ.< m →
     abs (bs y n - bs z m) < (abs (y - z) ／₊ L) + fst ε)
 bsLimitLipschitz L slope y z y∈ z∈ ε =
   let (N , widths<) = widthsEventually< y z ε
       d = abs (y - z) ／₊ L
   in N , λ n m N<n N<m →
      isTrans≤< _ _ _
        (endpointDistance≤ L slope y z y∈ z∈ n m)
        (≤<Monotone+ d d (width y n + width z m) (fst ε)
          (isRefl≤ d)
          (widths< n m N<n N<m))


-- module ℚBisectTests where

--  module Sqrt2 where

  

--   open ℚIncrFunBisect 1 2 decℚ<? (λ x → x · x) 2


--   -- bisectSqrt2 : ℕ → ℚ
--   -- bisectSqrt2 = fBisect 

--   -- bisectSqrt2R : ℕ → ℤ Σ× ℕ
--   -- bisectSqrt2R = fBisectR 


--   -- bisectSqrt2[5] : ℚ
--   -- bisectSqrt2[5] = {!bs 100!}
