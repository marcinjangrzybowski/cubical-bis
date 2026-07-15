module Cubical.HITs.CauchyReals.Calculus.Integration.FundamentalTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; negsuc)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Properties
open import Cubical.HITs.CauchyReals.Calculus.Integration.Uniform
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.MeanValue
open import Cubical.HITs.CauchyReals.Analysis.Uniform using
  ( IsUContinuousConst
  ; IsUContinuous-ᵣ₂
  ; IsUContinuousℙ+ᵣ₂
  ; IsUContinuousℙ-const
  ; clampDistᵣ
  ; clampᵣ∼
  ; IsUCauchyFSequence
  ; IsUContFSequence
  ; fromUCauchyFSequence
  ; fromCauchySequence'₁≡fromUCauchyFSequence
  ; IsUCauchyFSequence-lim
  ; fromUCauchyFSequence-+
  ; isCauchyFSequenceAt
  ; isUCauchyFSequence-ᵣ
  ; isUCauchyFSequence+ᵣ
  )
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open IntegrationUC rtp-1/n

interval-diameter : ∀ a b u v →
  a ≤ᵣ u → u ≤ᵣ b →
  a ≤ᵣ v → v ≤ᵣ b →
  absᵣ (v -ᵣ u) ≤ᵣ b -ᵣ a
interval-diameter a b u v a≤u u≤b a≤v v≤b =
  isTrans≡≤ᵣ _ _ _
    (abs-max (v -ᵣ u))
    (max≤-lem (v -ᵣ u) (-ᵣ (v -ᵣ u)) (b -ᵣ a)
      v-u≤b-a
      -[v-u]≤b-a)
 where
  v-u≤b-a : v -ᵣ u ≤ᵣ b -ᵣ a
  v-u≤b-a =
    a+d≤c+b⇒a-b≤c-d v u b a
      (≤ᵣMonotone+ᵣ _ _ _ _ v≤b a≤u)

  -[v-u]≤b-a : -ᵣ (v -ᵣ u) ≤ᵣ b -ᵣ a
  -[v-u]≤b-a =
    isTrans≡≤ᵣ _ _ _
      (-[x-y]≡y-x v u)
      (a+d≤c+b⇒a-b≤c-d u v b a
        (≤ᵣMonotone+ᵣ _ _ _ _ u≤b a≤v))

abs-max-min≤abs : ∀ x y →
  maxᵣ x y -ᵣ minᵣ x y ≤ᵣ absᵣ (y -ᵣ x)
abs-max-min≤abs x y =
  isTrans≡≤ᵣ _ _ _
    (sym (absᵣNonNeg (maxᵣ x y -ᵣ minᵣ x y)
      (x≤y→0≤y-x (minᵣ x y) (maxᵣ x y)
        (isTrans≤ᵣ _ _ _ (min≤ᵣ x y) (≤maxᵣ x y)))))
    (isTrans≡≤ᵣ _ _ _
      (absᵣ-min-max x y)
      (≡ᵣWeaken≤ᵣ _ _ (minusComm-absᵣ x y)))

min-point-width≤abs : ∀ x y z →
  minᵣ x y ≤ᵣ z → z ≤ᵣ maxᵣ x y →
  z -ᵣ minᵣ x y ≤ᵣ absᵣ (y -ᵣ x)
min-point-width≤abs x y z m≤z z≤M =
  isTrans≤ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _
      (sym (absᵣNonNeg (z -ᵣ minᵣ x y)
        (x≤y→0≤y-x (minᵣ x y) z m≤z)))
      (interval-diameter (minᵣ x y) (maxᵣ x y)
        (minᵣ x y) z
        (≤ᵣ-refl (minᵣ x y))
        (isTrans≤ᵣ _ _ _ (min≤ᵣ x y) (≤maxᵣ x y))
        m≤z z≤M))
    (abs-max-min≤abs x y)

integral-diff-from : ∀ x₀ m z (x₀≤m : x₀ ≤ᵣ m) (m≤z : m ≤ᵣ z)
  (f : ℝ → ℝ) (ucf : IsUContinuous f) →
  fst (Integrate-UContinuous x₀ z (isTrans≤ᵣ _ _ _ x₀≤m m≤z) f ucf)
    -ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf)
  ≡ fst (Integrate-UContinuous m z m≤z f ucf)
integral-diff-from x₀ m z x₀≤m m≤z f ucf =
  cong (_-ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf))
    (sym (IntegralConcat x₀ m z x₀≤m m≤z f ucf))
  ∙ cong (_-ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf))
      (+ᵣComm
        (fst (Integrate-UContinuous x₀ m x₀≤m f ucf))
        (fst (Integrate-UContinuous m z m≤z f ucf)))
  ∙ Rℝ.plusMinus
      (fst (Integrate-UContinuous m z m≤z f ucf))
      (fst (Integrate-UContinuous x₀ m x₀≤m f ucf))

integral-diff-minus-const : ∀ x₀ m z (x₀≤m : x₀ ≤ᵣ m) (m≤z : m ≤ᵣ z)
  (f : ℝ → ℝ) (ucf : IsUContinuous f) C →
  fst (Integrate-UContinuous x₀ z (isTrans≤ᵣ _ _ _ x₀≤m m≤z) f ucf)
    -ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf)
    -ᵣ C ·ᵣ (z -ᵣ m)
  ≡ fst (Integrate-UContinuous m z m≤z
       (λ t → f t -ᵣ C)
       (IsUContinuous-ᵣ₂ f (λ _ → C) ucf (IsUContinuousConst C)))
integral-diff-minus-const x₀ m z x₀≤m m≤z f ucf C =
  cong (_-ᵣ C ·ᵣ (z -ᵣ m))
    (integral-diff-from x₀ m z x₀≤m m≤z f ucf)
  ∙ cong (λ q → fst (Integrate-UContinuous m z m≤z f ucf) -ᵣ q)
      (sym (IntegralConst m z m≤z C (IsUContinuousConst C)))
  ∙ Integral- m z m≤z f (λ _ → C) ucf (IsUContinuousConst C)

Integrate-UContinuous≤≡ : ∀ a b (p q : a ≤ᵣ b) f ucf →
  fst (Integrate-UContinuous a b p f ucf)
  ≡ fst (Integrate-UContinuous a b q f ucf)
Integrate-UContinuous≤≡ a b p q f ucf =
  cong fst
    (IntegratedProp a b p f
      (Integrate-UContinuous a b p f ucf)
      (Integrate-UContinuous a b q f ucf))

common-min-error-path : ∀ Fx Fy Fm C x y m →
  Fy -ᵣ Fx -ᵣ C ·ᵣ (y -ᵣ x) ≡
  ((Fy -ᵣ Fm) -ᵣ C ·ᵣ (y -ᵣ m))
    -ᵣ ((Fx -ᵣ Fm) -ᵣ C ·ᵣ (x -ᵣ m))
common-min-error-path Fx Fy Fm C x y m = ℝ!

ftoc-final-algebra : ∀ I Fb → I ≡ Fb -ᵣ (Fb +ᵣ -ᵣ I)
ftoc-final-algebra I Fb = ℝ!

≤maxᵣ' : ∀ x y → y ≤ᵣ maxᵣ x y
≤maxᵣ' x y = isTrans≤≡ᵣ _ _ _ (≤maxᵣ y x) (maxᵣComm y x)

FTOC⇒ : ∀ x₀ (f : ℝ → ℝ) (ucf : IsUContinuous f) →
  uDerivativeOfℙ (pred≥ x₀) ,
    (λ x x₀≤x → fst (Integrate-UContinuous x₀ x x₀≤x f ucf))
    is (λ x _ → f x)
FTOC⇒ x₀ f ucf ε =
  let ε₂ = ε /2₊
      δ , X = ucf ε₂
  in ∣ (δ /2₊) , derivative-bound δ X ∣₁
 where
  derivative-bound : (δ : ℚ₊) →
    (∀ u v → u ∼[ δ ] v → f u ∼[ ε /2₊ ] f v) →
    ∀ x x₀≤x y x₀≤y →
    absᵣ (y -ᵣ x) ≤ᵣ rat (fst (δ /2₊)) →
    absᵣ
      (derivativeErrorℙ (pred≥ x₀)
        (λ z x₀≤z → fst (Integrate-UContinuous x₀ z x₀≤z f ucf))
        (λ z _ → f z)
        x x₀≤x y x₀≤y)
      ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x)
  derivative-bound δ X x x₀≤x y x₀≤y y-x≤δ/2 =
    isTrans≤ᵣ _ _ _
      (isTrans≡≤ᵣ _ _ _
        (cong absᵣ
          (common-min-error-path
            (fst (Integrate-UContinuous x₀ x x₀≤x f ucf))
            (fst (Integrate-UContinuous x₀ y x₀≤y f ucf))
            (fst (Integrate-UContinuous x₀ m x₀≤m f ucf))
            (f x) x y m))
        (absᵣ-triangle'' Ey Ex))
      (isTrans≤ᵣ _ _ _
        (≤ᵣMonotone+ᵣ _ _ _ _
          Ey≤ Ex≤)
        (isTrans≤≡ᵣ _ _ _
          (≤ᵣMonotone+ᵣ _ _ _ _
            εx εy)
          (ε/2+ε/2·abs≡ε·abs ε (y -ᵣ x))))
   where
    m M : ℝ
    m = minᵣ x y
    M = maxᵣ x y

    x₀≤m : x₀ ≤ᵣ m
    x₀≤m = ≤min-lem x₀ x y x₀≤x x₀≤y

    m≤x : m ≤ᵣ x
    m≤x = min≤ᵣ x y

    m≤y : m ≤ᵣ y
    m≤y = min≤ᵣ' x y

    x≤M : x ≤ᵣ M
    x≤M = ≤maxᵣ x y

    y≤M : y ≤ᵣ M
    y≤M = ≤maxᵣ' x y

    ε₂₊ : ℚ₊
    ε₂₊ = ε /2₊

    dist-to-x<δ : ∀ z → m ≤ᵣ z → z ≤ᵣ M →
      ∀ t → t ∈ intervalℙ m z →
      absᵣ (t -ᵣ x) <ᵣ rat (fst δ)
    dist-to-x<δ z m≤z z≤M t (m≤t , t≤z) =
      isTrans≤<ᵣ _ _ _
        (isTrans≤ᵣ _ _ _
          (interval-diameter m M x t m≤x x≤M m≤t
            (isTrans≤ᵣ _ _ _ t≤z z≤M))
          (abs-max-min≤abs x y))
        (isTrans≤<ᵣ _ _ _
          y-x≤δ/2
          (<ℚ→<ᵣ _ _ (x/2<x δ)))

    integrand≤ : ∀ z → (m≤z : m ≤ᵣ z) → z ≤ᵣ M →
      ∀ t → t ∈ intervalℙ m z →
      absᵣ (f t -ᵣ f x) ≤ᵣ rat (fst ε₂₊)
    integrand≤ z m≤z z≤M t t∈ =
      <ᵣWeaken≤ᵣ _ _
        (fst (∼≃abs<ε (f t) (f x) ε₂₊)
          (X t x
            (invEq (∼≃abs<ε t x δ)
              (dist-to-x<δ z m≤z z≤M t t∈))))

    Ex Ey : ℝ
    Ex = fst (Integrate-UContinuous x₀ x x₀≤x f ucf)
      -ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf)
      -ᵣ f x ·ᵣ (x -ᵣ m)
    Ey = fst (Integrate-UContinuous x₀ y x₀≤y f ucf)
      -ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf)
      -ᵣ f x ·ᵣ (y -ᵣ m)

    Ex≤ : absᵣ Ex ≤ᵣ rat (fst ε₂₊) ·ᵣ (x -ᵣ m)
    Ex≤ =
      isTrans≡≤ᵣ _ _ _
        (cong absᵣ
          (cong (λ I →
             I -ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf)
               -ᵣ f x ·ᵣ (x -ᵣ m))
             (Integrate-UContinuous≤≡ x₀ x x₀≤x
               (isTrans≤ᵣ _ _ _ x₀≤m m≤x) f ucf)
           ∙ integral-diff-minus-const x₀ m x x₀≤m m≤x f ucf (f x)))
        (IntegralAbs m x m≤x
          (λ t → f t -ᵣ f x)
          (IsUContinuous-ᵣ₂ f (λ _ → f x) ucf (IsUContinuousConst (f x)))
          (rat (fst ε₂₊))
          (integrand≤ x m≤x x≤M))

    Ey≤ : absᵣ Ey ≤ᵣ rat (fst ε₂₊) ·ᵣ (y -ᵣ m)
    Ey≤ =
      isTrans≡≤ᵣ _ _ _
        (cong absᵣ
          (cong (λ I →
             I -ᵣ fst (Integrate-UContinuous x₀ m x₀≤m f ucf)
               -ᵣ f x ·ᵣ (y -ᵣ m))
             (Integrate-UContinuous≤≡ x₀ y x₀≤y
               (isTrans≤ᵣ _ _ _ x₀≤m m≤y) f ucf)
           ∙ integral-diff-minus-const x₀ m y x₀≤m m≤y f ucf (f x)))
        (IntegralAbs m y m≤y
          (λ t → f t -ᵣ f x)
          (IsUContinuous-ᵣ₂ f (λ _ → f x) ucf (IsUContinuousConst (f x)))
          (rat (fst ε₂₊))
          (integrand≤ y m≤y y≤M))

    εx : rat (fst ε₂₊) ·ᵣ (y -ᵣ m)
      ≤ᵣ rat (fst ε₂₊) ·ᵣ absᵣ (y -ᵣ x)
    εx =
      ≤ᵣ-o·ᵣ _ _ (rat (fst ε₂₊))
        (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ ε₂₊)))
        (min-point-width≤abs x y y m≤y y≤M)

    εy : rat (fst ε₂₊) ·ᵣ (x -ᵣ m)
      ≤ᵣ rat (fst ε₂₊) ·ᵣ absᵣ (y -ᵣ x)
    εy =
      ≤ᵣ-o·ᵣ _ _ (rat (fst ε₂₊))
        (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ ε₂₊)))
        (min-point-width≤abs x y x m≤x x≤M)

FTOC⇒' : ∀ a b → a ≤ᵣ b
          → (f : ∀ x → x ∈ intervalℙ a b → ℝ)
          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → (uDerivativeOfℙ (intervalℙ a b) ,
                        (λ x (a≤x , x≤b) →
                          fst (Integrate-UContinuousℙ a x a≤x
                             (λ x x∈ → f x (fst x∈ , isTrans≤ᵣ _ _ _
                               (snd x∈) x≤b))
                           (map-snd
                             (λ X → λ u v u∈ v∈ u∼v →
                              X u v ((fst u∈ , isTrans≤ᵣ _ _ _
                               (snd u∈) x≤b))
                               (((fst v∈ , isTrans≤ᵣ _ _ _
                               (snd v∈) x≤b))) u∼v)
                             ∘ ucf)))
                        is f)
FTOC⇒' a b a≤b f ucf ε = do
 (δ , X) ← FTOC⇒ a (λ x → f (clampᵣ a b x)
       (clampᵣ∈ℚintervalℙ a b a≤b x))
       (map-snd (λ X u v u∼v →
        X _ _ (clampᵣ∈ℚintervalℙ a b a≤b u)
              (clampᵣ∈ℚintervalℙ a b a≤b v)
               (clampᵣ∼ u∼v)) ∘ ucf) ε
 ∣ δ , (λ x x∈ h h∈ ∣h-x∣≤δ →
    let z = X x (fst x∈) h (fst h∈)
            ∣h-x∣≤δ
     in isTrans≡≤ᵣ _ _ _
         (cong absᵣ
            (cong₂ _-ᵣ_
               (cong₂ _-ᵣ_
                 (Integrate-UContinuous-≡-∈ a _ _ _ _ _ _
                   λ x' x'∈ → cong (uncurry f)
                       (Σ≡Prop (∈-isProp (intervalℙ a b))
                         (sym (∈ℚintervalℙ→clampᵣ≡  a _ x' x'∈)
                           ∙ ∈ℚintervalℙ→clampᵣ≡  a b x' (fst x'∈ ,
                             isTrans≤ᵣ _ _ _ (snd x'∈) (snd h∈)))))

                        ((Integrate-UContinuous-≡-∈ a _ _ _ _ _ _
                   λ x' x'∈ → cong (uncurry f)
                       (Σ≡Prop (∈-isProp (intervalℙ a b))
                         (sym (∈ℚintervalℙ→clampᵣ≡  a _ x' x'∈)
                           ∙ ∈ℚintervalℙ→clampᵣ≡  a b x' (fst x'∈ ,
                             isTrans≤ᵣ _ _ _ (snd x'∈) (snd x∈)))))))
              (cong₂ _·ᵣ_
                (cong (uncurry f)
                  (Σ≡Prop (∈-isProp (intervalℙ a b))
                    (∈ℚintervalℙ→clampᵣ≡  a b x x∈)))
                refl)))
         z) ∣₁

FTOC⇒* : ∀ a b → a ≤ᵣ b
          → (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
          → (ax⊆ab : ∀ x → (x∈ : x ∈ intervalℙ a b) →
                 ∀ y → y ∈ intervalℙ a x
                     → y ∈ intervalℙ a b)
          → (∀ x → (x∈ : x ∈ intervalℙ a b) →
                on[ a , x ]IntegralOf (λ y ≤y y≤ →
                  f y (ax⊆ab x x∈ y (≤y , y≤)))
                 is (F x x∈))
          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → uDerivativeOfℙ (intervalℙ a b) , F is f
FTOC⇒* a b a≤b f F ax⊆ab X ucf  =
  subst
    (λ F → uDerivativeOfℙ (intervalℙ a b) , F is f)
    (funExt₂ (λ y y∈ →
      let
        f≤y : ∀ x → x ∈ intervalℙ a y → ℝ
        f≤y x x∈ =
          f x (fst x∈ , isTrans≤ᵣ x y b (snd x∈) (snd y∈))

        f≤y-cont : IsUContinuousℙ (intervalℙ a y) f≤y
        f≤y-cont =
          map-snd
            (λ X → λ u v u∈ v∈ u∼v →
              X u v
                (fst u∈ , isTrans≤ᵣ u y b (snd u∈) (snd y∈))
                (fst v∈ , isTrans≤ᵣ v y b (snd v∈) (snd y∈))
                u∼v)
            ∘ ucf

        fy : ∀ x → x ∈ intervalℙ a y → ℝ
        fy x x∈ = f x (ax⊆ab y y∈ x x∈)

        fy-cont : IsUContinuousℙ (intervalℙ a y) fy
        fy-cont =
          map-snd
            (λ X → λ u v u∈ v∈ u∼v →
              X u v (ax⊆ab y y∈ u u∈) (ax⊆ab y y∈ v v∈) u∼v)
            ∘ ucf

        p : ∀ x x∈ → f≤y x x∈ ≡ fy x x∈
        p x x∈ = cong (f x) (∈-isProp (intervalℙ a b) _ _ _)
      in Integrate-UContinuousℙ-≡ a y (fst y∈)
              f≤y fy f≤y-cont fy-cont p
            ∙ IntegralUniq a y (fst y∈)
                (λ z a≤z z≤y → fy z (a≤z , z≤y))
                (fst (Integrate-UContinuousℙ a y (fst y∈) fy fy-cont))
                (F y y∈)
                (snd (Integrate-UContinuousℙ a y (fst y∈) fy fy-cont))
                (X y y∈)))
    (FTOC⇒' a b a≤b f ucf)

FTOC⇐' : ∀ a b (a≤b : a ≤ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
          → ∀ (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → uDerivativeOfℙ (intervalℙ a b) , F is f
          → fst (Integrate-UContinuousℙ a b a≤b f ucf)
              ≡ F b (a≤b , ≤ᵣ-refl b)
                  -ᵣ F a (≤ᵣ-refl a , a≤b)
FTOC⇐' a b a≤b f F ucf udc =
  let f∘clamp = λ x → f (clampᵣ a b x) (clampᵣ∈ℚintervalℙ a b a≤b x)
      ucfℙ∘clamp : IsUContinuous f∘clamp
      ucfℙ∘clamp ε =
        map-snd
          (λ {δ} X u v u∼v →
            X _ _ _ _
              (invEq (∼≃abs<ε _ _ _)
                (isTrans≤<ᵣ _ _ _
                  (clampDistᵣ a b v u)
                  (fst (∼≃abs<ε _ _ _) u∼v))))
          (ucf ε)
      ucf∘clamp : IsUContinuous f∘clamp
      ucf∘clamp =
        map-snd
          (λ {δ} X u v u∼v →
            X _ _ _ _ (clampᵣ∼ {a} {b} u∼v))
          ∘ ucf

      f* : (r : ℝ) → r ∈ intervalℙ a b → ℝ
      f* r r∈ =
        -ᵣ (fst (Integrate-UContinuous a r (fst r∈) f∘clamp ucf∘clamp))

      z =
        uDerivativeOfℙ-ᵣ (pred≥ a)
          (λ x a≤x → fst (Integrate-UContinuous a x a≤x f∘clamp ucf∘clamp))
          (λ x _ → f∘clamp x)
          (FTOC⇒ a f∘clamp ucf∘clamp)

      z∣ : uDerivativeOfℙ (intervalℙ a b) , f* is (λ x _ → -ᵣ (f∘clamp x))
      z∣ =
        uDerivativeOfℙ-restr (pred≥ a) (intervalℙ a b)
          (λ x a≤x → -ᵣ (fst (Integrate-UContinuous a x a≤x f∘clamp ucf∘clamp)))
          (λ x _ → -ᵣ (f∘clamp x))
          (λ x x∈ → fst x∈)
          z

      zD : uDerivativeOfℙ (intervalℙ a b) ,
        (λ x x∈ → F x x∈ +ᵣ f* x x∈)
        is (λ x x∈ → f x x∈ +ᵣ -ᵣ (f∘clamp x))
      zD =
        +uDerivativeℙ (intervalℙ a b) _ _
          f* (λ x _ → -ᵣ (f∘clamp x))
          udc z∣

      b∈ : b ∈ intervalℙ a b
      b∈ = a≤b , ≤ᵣ-refl _

      a∈ : a ∈ intervalℙ a b
      a∈ = ≤ᵣ-refl _ , a≤b

      z' : F a (≤ᵣ-refl a , a≤b) ≡ F b (a≤b , ≤ᵣ-refl b) +ᵣ f* b b∈
      z' =
        sym
          (Rℝ.+IdR' _ _
            (cong -ᵣ_
              (Integral'-empty a f∘clamp _
                (snd (Integrate-UContinuous a a (≤ᵣ-refl a) f∘clamp ucf∘clamp)))
             ∙ -ᵣ-rat 0))
        ∙ nullDerivative→const a b a∈ b∈ a≤b
            (λ r r∈ → F r r∈ +ᵣ f* r r∈)
            (subst (uDerivativeOfℙ (intervalℙ a b) ,
              (λ r r∈ → F r r∈ +ᵣ f* r r∈) is_)
              (funExt₂ (λ x x∈ →
                cong₂ _-ᵣ_ refl
                  (cong (uncurry f)
                    (Σ≡Prop (∈-isProp (intervalℙ a b))
                      (sym (∈ℚintervalℙ→clampᵣ≡ a b x x∈))))
                ∙ +-ᵣ _))
              zD)
  in Integrate-UContinuous-≡ a b a≤b f∘clamp f∘clamp
       ucfℙ∘clamp ucf∘clamp (λ _ → refl)
     ∙ ftoc-final-algebra
         (fst (Integrate-UContinuous a b a≤b f∘clamp ucf∘clamp))
         (F b b∈)
     ∙ cong₂ _-ᵣ_ refl (sym z')

FTOC⇐ : ∀ a b (a≤b : a ≤ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
       → IsUContinuousℙ (intervalℙ a b) f
          → uDerivativeOfℙ (intervalℙ a b) , F is f
          → (on[ a , b ]IntegralOf curry ∘ f is
              (F b (a≤b , ≤ᵣ-refl b)
                -ᵣ F a (≤ᵣ-refl a , a≤b)))
FTOC⇐ a b a≤b f F ucf udc =
    subst (on[ a , b ]IntegralOf curry ∘ f is_)
    (FTOC⇐' a b a≤b _ _ ucf udc)
    (snd (Integrate-UContinuousℙ a b a≤b f ucf))

uCauchy∫ : ∀ a b → a ≤ᵣ b →
              (fₙ Fₙ : ℕ → ∀ x → x ∈ intervalℙ a b → ℝ)
            → (∀ n x x∈ →
                on[ a , x ]IntegralOf (λ x ≤x x≤ → fₙ n x (≤x ,
                  isTrans≤ᵣ _ _ _ x≤ (snd x∈)))
                  is (Fₙ n) x x∈)
            → (icf : IsUCauchyFSequence (intervalℙ a b) fₙ)
            → ∀ ucf
            → ∀ iucF ucF → ∀ x x∈
            → on[ a , x ]IntegralOf
                    (λ x ≤x x≤ →
                       fst (fromUCauchyFSequence (intervalℙ a b) fₙ icf ucf) x
                        (≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)))
                   is
                 (fst (fromUCauchyFSequence (intervalℙ a b) Fₙ iucF ucF) x x∈)

uCauchy∫ a b a≤b fₙ Fₙ fₙ≡∫Fₙ icf ucf iucF uF x x∈ ε = do
  (η₊ , b-a<η₊) ← ∃ℚ₊LargerThanℝ₀₊ ((b -ᵣ a) , x≤y→0≤y-x _ _ a≤b)
  let Nf , Xf = IsUCauchyFSequence-lim (intervalℙ a b)
              fₙ icf ucf
        (((ε /2₊) /2₊) ℚ₊· invℚ₊ η₊)
      NF , XF = IsUCauchyFSequence-lim (intervalℙ a b) _
                 iucF uF ((ε /2₊) /2₊)
      Nf⊔NF = ℕ.max Nf NF
  (δ , Xδ) ← fₙ≡∫Fₙ (suc Nf⊔NF) x x∈ (ε /2₊)
  return
    (δ , λ tp msh≤ →
          fst (∼≃abs<ε _ _ ε)
              (subst∼ ℚ!!
                (triangle∼
                  {ε = (((ε /2₊) /2₊) +₊ (ε /2₊))}
                  {η = ((ε /2₊) /2₊)}
                  (triangle∼ {ε = ((ε /2₊) /2₊)} {η = ε /2₊}
                     (sym∼ _ _ _ $ invEq (∼≃abs<ε _ _ ((ε /2₊) /2₊))
                        (isTrans≡<ᵣ _ _ _
                          (cong absᵣ (riemannSum- (snd tp) _ _
                           ∙ riemannSum-clamp (snd tp) _))
                          (isTrans≤<ᵣ _ _ _
                            (isTrans≤ᵣ _ _ _
                             (riemannSum'-absᵣ≤ (snd tp) _)
                             (riemannSum'≤ (snd tp) _ _
                               λ r ≤x x≤ →
                                <ᵣWeaken≤ᵣ _ _
                                  (Xf _ _ (suc Nf⊔NF)
                                  (ℕ.suc-≤-suc  (ℕ.left-≤-max {Nf} {NF})))))
                            (isTrans≡<ᵣ _ _ _
                              (riemannSum'Const (snd tp) _
                               ∙ cong₂ _·ᵣ_ (rat·ᵣrat _ _) refl
                               ∙ sym (·ᵣAssoc _ _ _)
                               ∙ cong₂ _·ᵣ_ refl (·ᵣComm _ _))
                              (isTrans<≡ᵣ _ _ _
                                 (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ ((ε /2₊) /2₊))
                                  (isTrans≡<ᵣ _ _ _
                                    (cong₂ _·ᵣ_ refl (sym (invℝ₊-rat η₊)))
                                    (invEq (z/y<x₊≃z<y₊·x _ _ _)
                                     (isTrans<≡ᵣ _ _ _
                                       (isTrans≤<ᵣ _ _ _
                                         (≤ᵣ-+o _ _ (-ᵣ a) (snd x∈)) b-a<η₊)
                                       (sym (·IdR _))))))
                                 (·IdR _))))))
                    (invEq (∼≃abs<ε _ _ (ε /2₊)) (Xδ tp msh≤)))
                  (invEq (∼≃abs<ε _ _ ((ε /2₊) /2₊)) (XF x x∈ (suc Nf⊔NF)
                    (ℕ.suc-≤-suc (ℕ.right-≤-max {NF} {Nf})))))))

Integral-additive : ∀ a b c a≤b b≤c → ∀ f s s' s+s' →
  on[ a , b ]IntegralOf (λ x ≤x x≤ → f x ≤x (isTrans≤ᵣ _ _ _ x≤ b≤c)) is s →
  on[ b , c ]IntegralOf (λ x ≤x x≤ → f x (isTrans≤ᵣ _ _ _ a≤b ≤x ) x≤) is s' →
  on[ a , c ]IntegralOf f is s+s' →
  s +ᵣ s' ≡ s+s'
Integral-additive a b c a≤b b≤c f s s' s+s' ∫ab ∫bc ∫ac =
  Integral'-additive a b c a≤b b≤c
   (λ x → f (clampᵣ a c x)
     (≤clampᵣ a c x (isTrans≤ᵣ _ _ _ a≤b b≤c))
     (clamp≤ᵣ a c x))
   s s' s+s'
     (Integral'≡ _ _ a≤b  _ _
         s (λ x x∈@(≤x , x≤) →
              cong (uncurry (uncurry ∘ f))
         (Σ≡Prop (∈-isProp (intervalℙ a c))
           (sym (∈ℚintervalℙ→clampᵣ≡  a b x x∈) ∙
             ∈ℚintervalℙ→clampᵣ≡  a c x
               (≤x , isTrans≤ᵣ _ _ _ x≤ b≤c))))
         (invEq (clampᵣ-IntegralOf' a b a≤b _ s) ∫ab))
        (Integral'≡ _ _ b≤c  _ _
         s' (λ x x∈@(≤x , x≤) →
              cong (uncurry (uncurry ∘ f))
         (Σ≡Prop (∈-isProp (intervalℙ a c))
           ((sym (∈ℚintervalℙ→clampᵣ≡  b c x x∈) ∙
             ∈ℚintervalℙ→clampᵣ≡  a c x
               (isTrans≤ᵣ _ _ _ a≤b ≤x , x≤ )))))
          (invEq (clampᵣ-IntegralOf' b c b≤c _ s') ∫bc))
    (invEq (clampᵣ-IntegralOf' a c (isTrans≤ᵣ _ _ _ a≤b b≤c)
     (uncurry ∘ f) s+s') ∫ac)

Integral-additive* : ∀ (P : ℙ ℝ ) a b c → a ≤ᵣ b →  b ≤ᵣ c
  → ∀ (f : ∀ x → x ∈ P → ℝ)
  → {ab⊂P : intervalℙ a b ⊆ P}
  → {bc⊂P : intervalℙ b c ⊆ P}
  → {ac⊂P : intervalℙ a c ⊆ P}
  → ∀ {s s' s+s'} →
  on[ a , b ]IntegralOf (λ x ≤x x≤ → f x (ab⊂P x (≤x , x≤))) is s →
  on[ b , c ]IntegralOf (λ x ≤x x≤ → f x (bc⊂P x (≤x , x≤))) is s' →
  on[ a , c ]IntegralOf (λ x ≤x x≤ → f x (ac⊂P x (≤x , x≤))) is s+s' →
  s +ᵣ s' ≡ s+s'
Integral-additive* P a b c a≤b b≤c f {s = s} {s'} s∫ s'∫ s+s'∫ =
 Integral-additive a b c a≤b b≤c _ _ _ _
   (subst (on[ a , b ]IntegralOf_is s)
    (funExt₃ λ x _ _ → cong (f x) (snd (P _) _ _)) s∫)
   (subst (on[ b , c ]IntegralOf_is s')
    (funExt₃ λ x _ _ → cong (f x) (snd (P _) _ _)) s'∫)
   s+s'∫

FTOC⇐'' : ∀ a b (a<b : a <ᵣ b) (f F : ∀ x → x ∈ intervalℙ a b → ℝ)
          → (ucf : IsUContinuousℙ (intervalℙ a b) f)
          → uDerivativeOfℙ (intervalℙ a b) , F is f
          → ∀ x x∈
          → on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is
              (F x x∈ -ᵣ F a (≤ᵣ-refl a , <ᵣWeaken≤ᵣ _ _ a<b ))
FTOC⇐'' a b a<b f F ucf fd x x∈ =
  PT.rec (isPropΠ λ _ → squash₁)
    (⊎.rec
     (λ x<b →
       let zz = FTOC⇐ x b (<ᵣWeaken≤ᵣ _ _ x<b)
                (λ x₁ (≤x , x≤)
                  → f x₁ (isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤))
                (λ x₁ (≤x , x≤)
                  → F x₁ (isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤))
                  (IsUContinuousℙ-restr
                    (intervalℙ a b)
                    (intervalℙ x b)
                    f
                    (λ x (≤x , x≤) → isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤) ucf)
                   (uDerivativeOfℙ-restr
                    (intervalℙ a b)
                    (intervalℙ x b)
                    F
                    f
                    (λ x (≤x , x≤) → isTrans≤ᵣ _ _ _  (fst x∈) ≤x , x≤) fd)
           zzzW = (snd (Integrate-UContinuousℙ a x (fst x∈) _
                           ((IsUContinuousℙ-restr
                        (intervalℙ a b)
                        (intervalℙ a x)
                        f
                        (λ x (≤x , x≤) →
                         ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) ucf))))
           zzz = Integral-additive a x b (fst x∈) (snd x∈)
                        _ _ _ _
                        zzzW
                        zz
                        (FTOC⇐ a b (<ᵣWeaken≤ᵣ _ _ a<b) _ _ ucf fd)
       in subst (on[ a , x ]IntegralOf
              (λ x₁ ≤x x≤ → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈))) is_)
               (sym (Rℝ.plusMinus _ _)
                ∙∙ cong₂ _-ᵣ_ zzz
                   (cong₂ _-ᵣ_
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl)))
                     ((cong (uncurry F)
                        (Σ≡Prop (∈-isProp (intervalℙ a b))
                         refl))))
                ∙∙ [x-y]-[x-z]≡z-y _ _ _)
               zzzW)
      λ a<x →
       subst (on[ a , x ]IntegralOf _ is_)
        (cong₂ _-ᵣ_
         (cong (uncurry F)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 refl))
        (cong (uncurry F)
                (Σ≡Prop (∈-isProp (intervalℙ a b))
                 refl)))
        (FTOC⇐ a x (<ᵣWeaken≤ᵣ _ _ a<x)
         (λ x₁ (≤x , x≤)
           → f x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈)))
         (λ x₁ (≤x , x≤)
           → F x₁ (≤x , isTrans≤ᵣ x₁ x b x≤ (snd x∈)))
           (IsUContinuousℙ-restr
             (intervalℙ a b)
             (intervalℙ a x)
             f
             (λ x (≤x , x≤) → ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) ucf)
            (uDerivativeOfℙ-restr
             (intervalℙ a b)
             (intervalℙ a x)
             F
             f
             (λ x (≤x , x≤) → ≤x , isTrans≤ᵣ _ _ _ x≤ (snd x∈)) fd)))
    (Dichotomyℝ' a x b a<b)

uCauchyDer : ∀ a b → a <ᵣ b → ∀ fₙ Fₙ →
             ∀ (icf : IsUCauchyFSequence (intervalℙ a b) fₙ)

             uf uF
             (icF : IsUCauchyFSequence (intervalℙ a b) Fₙ)
             → (∀ n → uDerivativeOfℙ (intervalℙ a b) , Fₙ n is fₙ n)
             → uDerivativeOfℙ (intervalℙ a b) ,
                  (fst (fromUCauchyFSequence (intervalℙ a b) Fₙ icF uF))
                  is
                  (fst (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf))
uCauchyDer a b a<b fₙ Fₙ  icf uf uF icF Fₙ'=fₙ =
   uDerivativeℙ-cancelConst
   (intervalℙ a b) C
   (fst (fromUCauchyFSequence (intervalℙ a b) Fₙ icF uF))
   (fst (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf))
   uzu2
 where
 a≤b : a ≤ᵣ b
 a≤b = <ᵣWeaken≤ᵣ a b a<b

 F-F-ucfs : IsUContFSequence (intervalℙ a b)
      (λ n x₁ x∈₁ → Fₙ n x₁ x∈₁ -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 F-F-ucfs n = IsUContinuousℙ+ᵣ₂
    (intervalℙ a b)
    (Fₙ n)
    (λ x₁ x∈₁ → -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
    (uF n)
    (IsUContinuousℙ-const (intervalℙ a b) (-ᵣ Fₙ n a (≤ᵣ-refl a , a≤b)))

 icf-a :
   IsUCauchyFSequence (intervalℙ a b)
     (λ n x₁ x∈₁ → -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 icf-a = isUCauchyFSequence-ᵣ
                   (intervalℙ a b)
                   (λ n x₁ x∈₁ → Fₙ n a (≤ᵣ-refl a , a≤b))
                   (map-snd (λ X _ _ m n x₃ x₄ →
                     X _ _ m n x₃ x₄)
                     ∘ icF)

 F-F-uchfs : IsUCauchyFSequence (intervalℙ a b)
      (λ n x₁ x∈₁ → Fₙ n x₁ x∈₁ -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
 F-F-uchfs = isUCauchyFSequence+ᵣ
    (intervalℙ a b)
    Fₙ
    (λ n x₁ x∈₁ → -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
    icF icf-a

 icaFa :
      IsCauchySequence' (λ z → -ᵣ Fₙ z a (≤ᵣ-refl a , a≤b))
 C : ℝ
 C = fromCauchySequence'₁
      (λ z → -ᵣ Fₙ z a (≤ᵣ-refl a , a≤b))
      ∣ icaFa ∣₁

 icaFa =
   fst (map-fromCauchySequence'
  1 (λ z → Fₙ z a (≤ᵣ-refl a , a≤b))
    (isCauchyFSequenceAt
      (intervalℙ a b)
      Fₙ
      icF
      a
      (≤ᵣ-refl a , a≤b))
   -ᵣ_ -ᵣ-lip)

 uzu2 : uDerivativeOfℙ intervalℙ a b ,
        (λ r z → fst
           (fromUCauchyFSequence (intervalℙ a b)
            Fₙ icF uF)
           r z +ᵣ C)
        is
        (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf .fst)
 uzu2 = subst2 (uDerivativeOfℙ (intervalℙ a b) ,_is_)
           (funExt₂ λ x x∈@(≤x , x≤) →
              IntegralUniq a x (≤x) _ _ _
             (snd ((Integrate-UContinuousℙ a x ≤x
              (λ x₁ x∈₁ →
                 fromUCauchyFSequence (intervalℙ a b) fₙ icf uf .fst x₁
                 (fst x∈₁ , isTrans≤ᵣ x₁ x b (snd x∈₁) x≤))
              (map-snd
               (λ X u v u∈ v∈ →
                  X u v (fst u∈ , isTrans≤ᵣ u x b (snd u∈) x≤)
                  (fst v∈ , isTrans≤ᵣ v x b (snd v∈) (x∈ .snd)))
               ∘ snd (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf)))))
             (uCauchy∫ _ _ a≤b fₙ
                     (λ n x x∈ → Fₙ n x x∈ -ᵣ Fₙ n a (≤ᵣ-refl _ , a≤b))
                    (λ n x x∈ →
                       FTOC⇐'' a b a<b (fₙ n) (Fₙ n) (uf n)
                     (Fₙ'=fₙ n) x x∈)
                      icf uf
                      F-F-uchfs
                      F-F-ucfs
                      x x∈)
               ∙ sym (fromUCauchyFSequence-+ (intervalℙ a b)
                 Fₙ
                 icF
                 uF
                 (λ n x x∈ → -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
                 icf-a
                 (λ n → IsUContinuousℙ-const
                   (intervalℙ a b)
                   (-ᵣ Fₙ n a (≤ᵣ-refl a , a≤b)))
                 F-F-uchfs
                 F-F-ucfs
                 x x∈)
                 ∙ cong₂ _+ᵣ_ refl
                  (sym
                   (fromCauchySequence'₁≡fromUCauchyFSequence
                    (intervalℙ a b)
                    (λ n x x∈ → -ᵣ Fₙ n a (≤ᵣ-refl a , a≤b))
                    x x∈
                    icf-a
                    (λ n → IsUContinuousℙ-const
                        (intervalℙ a b)
                        (-ᵣ Fₙ n a (≤ᵣ-refl a , a≤b)))
                    ∣ icaFa ∣₁)))
           refl
           (FTOC⇒' a b a≤b _
            (snd (fromUCauchyFSequence (intervalℙ a b) fₙ icf uf)))
