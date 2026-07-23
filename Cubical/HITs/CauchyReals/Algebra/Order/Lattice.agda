module Cubical.HITs.CauchyReals.Algebra.Order.Lattice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core


max-lem : ∀ x x' y →
  maxᵣ (maxᵣ x y) (maxᵣ x' y) ≡ maxᵣ (maxᵣ x x') y
max-lem x x' y =
  maxᵣAssoc _ _ _
  ∙ cong (flip maxᵣ y) (maxᵣComm _ _)
  ∙ sym (maxᵣAssoc _ _ _)
  ∙ cong (maxᵣ x')
      (sym (maxᵣAssoc _ _ _) ∙ cong (maxᵣ x) (maxᵣIdem y))
  ∙ maxᵣAssoc _ _ _
  ∙ cong (flip maxᵣ y) (maxᵣComm _ _)


opaque

 minᵣIdem : ∀ x → minᵣ x x ≡ x
 minᵣIdem = ≡Continuous _ _
   (cont₂minᵣ _ _ IsContinuousId IsContinuousId)
   IsContinuousId
   (λ r → minᵣ-rat r r ∙ cong rat (ℚ.minIdem r))


min-lem : ∀ x x' y →
  minᵣ (minᵣ x y) (minᵣ x' y) ≡ minᵣ (minᵣ x x') y
min-lem x x' y =
  minᵣAssoc _ _ _
  ∙ cong (flip minᵣ y) (minᵣComm _ _)
  ∙ sym (minᵣAssoc _ _ _)
  ∙ cong (minᵣ x')
      (sym (minᵣAssoc _ _ _) ∙ cong (minᵣ x) (minᵣIdem y))
  ∙ minᵣAssoc _ _ _
  ∙ cong (flip minᵣ y) (minᵣComm _ _)


max≤-lem : ∀ x x' y → x ≤ᵣ y → x' ≤ᵣ y → maxᵣ x x' ≤ᵣ y
max≤-lem x x' y p p' = ≡→≤ᵣ
  (sym (max-lem _ _ _)
    ∙∙ cong₂ maxᵣ (≤ᵣ→≡ p) (≤ᵣ→≡ p')
    ∙∙ maxᵣIdem y)


opaque
 unfolding _<ᵣ_

 max<-lem : ∀ x x' y → x <ᵣ y → x' <ᵣ y → maxᵣ x x' <ᵣ y
 max<-lem x x' y = PT.map2
   λ ((q , q') , (a , a' , a''))
     ((r , r') , (b , b' , b'')) →
      (ℚ.max q r , ℚ.max q' r') ,
        max≤-lem x x' (rat (ℚ.max q r))
          (isTrans≤ᵣ x _ _ a (≤ℚ→≤ᵣ _ _ (ℚ.≤max q r)))
          (isTrans≤ᵣ x' _ _ b (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r))) ,
        ℚ.<MonotoneMax _ _ _ _ a' b' ,
        subst (_≤ᵣ y) (maxᵣ-rat q' r')
          (max≤-lem (rat q') (rat r') _ a'' b'')

 minDistMaxᵣ : ∀ x y y' →
   maxᵣ x (minᵣ y y') ≡ minᵣ (maxᵣ x y) (maxᵣ x y')
 minDistMaxᵣ x y y' = ≡Continuous _ _
    (IsContinuousMaxR _)
    (cont₂minᵣ _ _ (IsContinuousMaxR _) (IsContinuousMaxR _))
    (λ xR →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR))
          (IsContinuousMinR y'))
        (IsContinuous∘ _ _ (IsContinuousMinR _)
          (IsContinuousMaxL (rat xR)))
        (λ yR →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuousMaxL (rat xR))
              (IsContinuousMinL (rat yR)))
            (IsContinuous∘ _ _
              (IsContinuousMinL (maxᵣ (rat xR) (rat yR)))
              (IsContinuousMaxL (rat xR)))
            (λ r →
              cong (maxᵣ (rat xR)) (minᵣ-rat yR r)
              ∙ maxᵣ-rat xR (ℚ.min yR r)
              ∙ cong rat (ℚ.minDistMax xR yR r)
              ∙ sym (minᵣ-rat (ℚ.max xR yR) (ℚ.max xR r))
              ∙ cong₂ minᵣ
                  (sym (maxᵣ-rat xR yR))
                  (sym (maxᵣ-rat xR r)))
            y')
        y)
    x


≤maxᵣ : ∀ m n → m ≤ᵣ maxᵣ m n
≤maxᵣ m n = ≡→≤ᵣ
  (maxᵣAssoc _ _ _ ∙ cong (flip maxᵣ n) (maxᵣIdem m))


opaque
 unfolding _≤ᵣ_

 ≤min-lem : ∀ x y y' → x ≤ᵣ y → x ≤ᵣ y' → x ≤ᵣ minᵣ y y'
 ≤min-lem x y y' p p' =
   minDistMaxᵣ x y y' ∙ cong₂ minᵣ p p'


opaque
 unfolding _<ᵣ_

 <min-lem : ∀ x x' y → y <ᵣ x → y <ᵣ x' → y <ᵣ minᵣ x x'
 <min-lem x x' y = PT.map2
   λ ((q , q') , (a , a' , a''))
     ((r , r') , (b , b' , b'')) →
      (ℚ.min q r , ℚ.min q' r') ,
        subst (y ≤ᵣ_) (minᵣ-rat q r) (≤min-lem y _ _ a b) ,
        ℚ.<MonotoneMin _ _ _ _ a' b' ,
        ≤min-lem (rat (ℚ.min q' r')) x x'
          (isTrans≤ᵣ (rat (ℚ.min q' r')) _ _
            (≤ℚ→≤ᵣ _ _ (ℚ.min≤ q' r')) a'')
          (isTrans≤ᵣ (rat (ℚ.min q' r')) _ _
            (≤ℚ→≤ᵣ _ _ (ℚ.min≤' q' r')) b'')


opaque

 <min-rr : ∀ p q r → p <ᵣ rat q → p <ᵣ rat r
   → p <ᵣ minᵣ (rat q) (rat r)
 <min-rr p q r = <min-lem (rat q) (rat r) p


maxᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊
maxᵣ₊ (x , 0<x) (y , 0<y) =
  maxᵣ x y , isTrans<≤ᵣ _ _ _ 0<x (≤maxᵣ _ _)


minᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊
minᵣ₊ (x , 0<x) (y , 0<y) =
  minᵣ x y , <min-lem _ _ _ 0<x 0<y


minᵣ₀₊ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
minᵣ₀₊ (x , 0≤x) (y , 0≤y) =
  minᵣ x y , ≤min-lem _ _ _ 0≤x 0≤y


maxᵣ₀₊ : ℝ₀₊ → ℝ₀₊ → ℝ₀₊
maxᵣ₀₊ (x , 0≤x) (y , 0≤y) =
  maxᵣ x y , isTrans≤ᵣ _ _ _ 0≤x (≤maxᵣ x y)


opaque
 unfolding _≤ᵣ_ absᵣ

 maxAbsorbLMinᵣ : ∀ x y → maxᵣ x (minᵣ x y) ≡ x
 maxAbsorbLMinᵣ x =
   ≡Continuous _ _
     (IsContinuous∘ _ _
       (IsContinuousMaxL x) (IsContinuousMinL x))
     (IsContinuousConst _)
     λ y' →
       ≡Continuous _ _
         (cont₂maxᵣ _ _ IsContinuousId (IsContinuousMinR _))
         IsContinuousId
         (λ x' →
           cong (maxᵣ (rat x')) (minᵣ-rat x' y')
           ∙ maxᵣ-rat x' (ℚ.min x' y')
           ∙ cong rat (ℚ.maxAbsorbLMin x' y'))
         x

 maxDistMinᵣ : ∀ x y z →
   minᵣ x (maxᵣ y z) ≡ maxᵣ (minᵣ x y) (minᵣ x z)
 maxDistMinᵣ x y y' =
   ≡Continuous _ _
    (IsContinuousMinR _)
    (cont₂maxᵣ _ _ (IsContinuousMinR _) (IsContinuousMinR _))
    (λ xR →
      ≡Continuous _ _
        (IsContinuous∘ _ _ (IsContinuousMinL (rat xR))
          (IsContinuousMaxR y'))
        (IsContinuous∘ _ _ (IsContinuousMaxR _)
          (IsContinuousMinL (rat xR)))
        (λ yR →
          ≡Continuous _ _
            (IsContinuous∘ _ _ (IsContinuousMinL (rat xR))
              (IsContinuousMaxL (rat yR)))
            (IsContinuous∘ _ _
              (IsContinuousMaxL (minᵣ (rat xR) (rat yR)))
              (IsContinuousMinL (rat xR)))
            (λ r →
              cong (minᵣ (rat xR)) (maxᵣ-rat yR r)
              ∙ minᵣ-rat xR (ℚ.max yR r)
              ∙ cong rat
                  (ℚ.minComm xR (ℚ.max yR r)
                    ∙∙ ℚ.maxDistMin yR r xR
                    ∙∙ cong₂ ℚ.max
                        (ℚ.minComm yR xR)
                        (ℚ.minComm r xR))
              ∙ sym (maxᵣ-rat (ℚ.min xR yR) (ℚ.min xR r))
              ∙ cong₂ maxᵣ
                  (sym (minᵣ-rat xR yR))
                  (sym (minᵣ-rat xR r)))
            y')
        y)
    x

 min≤ᵣ : ∀ m n → minᵣ m n ≤ᵣ m
 min≤ᵣ m n = maxᵣComm (minᵣ m n) m ∙ maxAbsorbLMinᵣ m n

 min≤ᵣ' : ∀ m n → minᵣ m n ≤ᵣ n
 min≤ᵣ' m n = subst (_≤ᵣ n) (minᵣComm n m) (min≤ᵣ n m)

 ≤→minᵣ : ∀ m n → m ≤ᵣ n → minᵣ m n ≡ m
 ≤→minᵣ m n p =
   cong₂ minᵣ (sym (maxᵣIdem m)) (sym p)
   ∙ sym (minDistMaxᵣ m m n)
   ∙ maxAbsorbLMinᵣ m n

 ≤→maxᵣ : ∀ m n → m ≤ᵣ n → maxᵣ m n ≡ n
 ≤→maxᵣ m n p = p


opaque
 unfolding maxᵣ

 maxMonotoneᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s →
   maxᵣ m o ≤ᵣ maxᵣ n s
 maxMonotoneᵣ m n o s m≤n o≤s =
   max≤-lem _ _ _
     (isTrans≤ᵣ _ _ _ m≤n (≤maxᵣ _ _))
     (isTrans≤ᵣ _ _ _ o≤s
       (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ n) (maxᵣComm s n)))


opaque
 unfolding minᵣ

 minMonotoneᵣ : ∀ m n o s → m ≤ᵣ n → o ≤ᵣ s →
   minᵣ m o ≤ᵣ minᵣ n s
 minMonotoneᵣ m n o s m≤n o≤s =
   ≤min-lem _ _ _
     (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) m≤n)
     (isTrans≤ᵣ _ _ _
       (isTrans≡≤ᵣ _ _ _ (minᵣComm m o) (min≤ᵣ _ m)) o≤s)


opaque
 unfolding _≤ᵣ_ absᵣ

 incr→max≤ : (f : ∀ x → 0 <ᵣ x → ℝ)
   → (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
   → ∀ u v 0<u 0<v →
     maxᵣ (f u 0<u) (f v 0<v)
       ≤ᵣ f (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
 incr→max≤ f incr u v 0<u 0<v =
   isTrans≤≡ᵣ (maxᵣ (f u 0<u) (f v 0<v)) _ _
     (maxMonotoneᵣ (f u 0<u) _ (f v 0<v) _
       (incr u 0<u (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
        (≤maxᵣ u v))
       (incr v 0<v (maxᵣ u v) (snd (maxᵣ₊ (u , 0<u) (v , 0<v)))
        (isTrans≤≡ᵣ v _ _ (≤maxᵣ v u) (maxᵣComm v u))))
     (maxᵣIdem _)


opaque
 unfolding minᵣ

 incr→≤min : (f : ∀ x → 0 <ᵣ x → ℝ)
   → (∀ x 0<x y 0<y → x ≤ᵣ y → f x 0<x ≤ᵣ f y 0<y)
   → ∀ u v 0<u 0<v →
     f (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
       ≤ᵣ minᵣ (f u 0<u) (f v 0<v)
 incr→≤min f incr u v 0<u 0<v =
   isTrans≡≤ᵣ _ _ _
     (sym (minᵣIdem _))
     (minMonotoneᵣ _ _ _ _
       (incr (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
         u 0<u (min≤ᵣ _ _))
       (incr (minᵣ u v) (snd (minᵣ₊ (u , 0<u) (v , 0<v)))
         v 0<v
         (isTrans≡≤ᵣ _ _ _ (minᵣComm u v) (min≤ᵣ _ u))))
