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
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order.Properties

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties

open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_)

open import Cubical.Tactics.CommRingSolver.OrderedReflection

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

 

-- module ℚBisectTests where

--  module Sqrt2 where

  

--   open ℚIncrFunBisect 1 2 decℚ<? (λ x → x · x) 2


--   -- bisectSqrt2 : ℕ → ℚ
--   -- bisectSqrt2 = fBisect 

--   -- bisectSqrt2R : ℕ → ℤ Σ× ℕ
--   -- bisectSqrt2R = fBisectR 


--   -- bisectSqrt2[5] : ℚ
--   -- bisectSqrt2[5] = {!bs 100!}
