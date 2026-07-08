module Cubical.HITs.CauchyReals.FundamentalTheoremOfCalculus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; negsuc)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.Partition
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.HITs.CauchyReals.RationalsImports

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
