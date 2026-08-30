module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕO
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
  using (+MonoR<; ·MonoR<; ·MonoR≤)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition

private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


rationalMultiplication : ℚ → ℚ → ℚ
rationalMultiplication x y = x ℚR.· y


private
  multiplicationDifference : ∀ a b c d →
    a ℚR.· b ℚR.- c ℚR.· d ≡
      (a ℚR.- c) ℚR.· b ℚR.+ c ℚR.· (b ℚR.- d)
  multiplicationDifference a b c d = ℚ!

  rationalMultiplication-bounded : ∀ B₁ B₂ a b c d ε →
    abs b ℚ.≤ fst B₂ →
    abs c ℚ.≤ fst B₁ →
    abs (a ℚR.- c) ℚ.< fst ε →
    abs (b ℚR.- d) ℚ.< fst ε →
    abs (rationalMultiplication a b ℚR.- rationalMultiplication c d)
      ℚ.< fst ((B₂ +₊ B₁) ·₊ ε)
  rationalMultiplication-bounded B₁ B₂ a b c d ε
      absb≤B₂ absc≤B₁ a-c<ε b-d<ε =
    begin<
      abs (rationalMultiplication a b ℚR.- rationalMultiplication c d)
        ≡→≤⟨ cong abs (multiplicationDifference a b c d) ⟩
      abs ((a ℚR.- c) ℚR.· b ℚR.+ c ℚR.· (b ℚR.- d))
        ≤⟨ triangularInequality
          ((a ℚR.- c) ℚR.· b) (c ℚR.· (b ℚR.- d)) ⟩
      abs ((a ℚR.- c) ℚR.· b) ℚR.+ abs (c ℚR.· (b ℚR.- d))
        ≡→≤⟨ cong₂ ℚR._+_
          (sym (abs·abs (a ℚR.- c) b))
          (sym (abs·abs c (b ℚR.- d))) ⟩
      abs (a ℚR.- c) ℚR.· abs b ℚR.+
        abs c ℚR.· abs (b ℚR.- d)
        ≤⟨ +Mono≤ _ _ _ _
          (·MonoL≤ (abs b) (fst B₂) (abs (a ℚR.- c))
            (0≤abs (a ℚR.- c)) absb≤B₂)
          (·MonoR≤ (abs c) (fst B₁) (abs (b ℚR.- d))
            (0≤abs (b ℚR.- d)) absc≤B₁) ⟩
      abs (a ℚR.- c) ℚR.· fst B₂ ℚR.+
        fst B₁ ℚR.· abs (b ℚR.- d)
        <⟨ +Mono< _ _ _ _
          (·MonoR< (abs (a ℚR.- c)) (fst ε) (fst B₂)
            (snd B₂) a-c<ε)
          (·MonoL< (abs (b ℚR.- d)) (fst ε) (fst B₁)
            (snd B₁) b-d<ε) ⟩
      fst ε ℚR.· fst B₂ ℚR.+ fst B₁ ℚR.· fst ε
        ≡→≤⟨ cong₂ ℚR._+_ (ℚ.·Comm (fst ε) (fst B₂)) refl
          ∙ sym (ℚ.·DistR+ (fst B₂) (fst B₁) (fst ε)) ⟩
      fst ((B₂ +₊ B₁) ·₊ ε) ◾

  three : ℚ₊
  three = (1 +₊ 1) +₊ 1

  anchorBound : ℚ → ℚ₊
  anchorBound a = three +₊ maxWithPos 1 (abs a)

  closeToAnchor-bounded : ∀ a q →
    abs (q ℚR.- a) ℚ.< fst three →
    abs q ℚ.≤ fst (anchorBound a)
  closeToAnchor-bounded a q q-a<three = begin≤
    abs q
      ≡→≤⟨ sym (cong abs
        (cong (q ℚR.+_) ℚRing.0Selfinverse ∙ ℚR.+IdR q)) ⟩
    abs (q ℚR.- 0)
      ≤⟨ triangularInequality- q 0 a ⟩
    abs (q ℚR.- a) ℚR.+ abs (a ℚR.- 0)
      ≡→≤⟨ cong (abs (q ℚR.- a) ℚR.+_)
        (cong abs
          (cong (a ℚR.+_) ℚRing.0Selfinverse ∙ ℚR.+IdR a)) ⟩
    abs (q ℚR.- a) ℚR.+ abs a
      <⟨ +MonoR< _ _ (abs a) q-a<three ⟩
    fst three ℚR.+ abs a
      ≤⟨ +MonoL≤ (abs a) (fst (maxWithPos 1 (abs a)))
        (fst three) (ℚ.≤max' 1 (abs a)) ⟩
    fst (anchorBound a) ◾

  approximation-bounded : ∀ a (x : ℕ → Real.ℝ) K
    (xc : ∀ m n → K ℕO.≤ m → K ℕO.≤ n →
      x m Real.Base.≈ᶜ[ 1 ] x n)
    H m → K ℕO.≤ H → K ℕO.≤ m →
    ∀ δ → δ <₊ 1 →
    Real.ιℚ a Real.Base.≈ᶜ[ 1 ] x H →
    ∀ q → Real.ιℚ q Real.Base.≈ᶜ[ δ ] x m →
    abs q ℚ.≤ fst (anchorBound a)
  approximation-bounded a x K xc H m K≤H K≤m δ δ<1
      ιa∼xH q ιq∼xm =
    closeToAnchor-bounded a q
      (Real.Approximation.ι-ι→≈ q a three ιq∼a)
    where
    ιq∼xm-at-one : Real.ιℚ q Real.Base.≈ᶜ[ 1 ] x m
    ιq∼xm-at-one =
      Real.Base.isMonotone≈ᶜ< (Real.ιℚ q) (x m) δ 1 δ<1 ιq∼xm

    ιq∼xH : Real.ιℚ q Real.Base.≈ᶜ[ 1 +₊ 1 ] x H
    ιq∼xH = Real.Premetric.tri≈ᶜ (Real.ιℚ q) (x m) (x H) 1 1
      ιq∼xm-at-one (xc m H K≤m K≤H)

    ιq∼a : Real.ιℚ q Real.Base.≈ᶜ[ three ] Real.ιℚ a
    ιq∼a = Real.Premetric.tri≈ᶜ (Real.ιℚ q) (x H) (Real.ιℚ a)
      (1 +₊ 1) 1 ιq∼xH
      (Real.Base.sym≈ᶜ (Real.ιℚ a) (x H) 1 ιa∼xH)

  tripleQuarter< : ∀ ε →
    ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚR._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
        (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾

  inputRadius : ℚ₊ → ℚ₊ → ℚ₊
  inputRadius C ε = min₊ 1 ((ε /4₊) ₊／₊ C) /4₊

  inputTriple : ℚ₊ → ℚ₊ → ℚ₊
  inputTriple C ε =
    (inputRadius C ε +₊ inputRadius C ε) +₊ inputRadius C ε

  inputRadius<one : ∀ C ε → inputRadius C ε <₊ 1
  inputRadius<one C ε =
    ℚ.isTrans<≤ _ (fst (min₊ 1 ((ε /4₊) ₊／₊ C))) _
      (/4₊<id (min₊ 1 ((ε /4₊) ₊／₊ C)))
      (min₊≤L 1 ((ε /4₊) ₊／₊ C))

  inputTriple<ratio : ∀ C ε →
    inputTriple C ε <₊ ((ε /4₊) ₊／₊ C)
  inputTriple<ratio C ε =
    ℚ.isTrans<≤ _ (fst (min₊ 1 ((ε /4₊) ₊／₊ C))) _
      (tripleQuarter< (min₊ 1 ((ε /4₊) ₊／₊ C)))
      (min₊≤R 1 ((ε /4₊) ₊／₊ C))

  scaledInputTriple<quarter : ∀ C ε →
    C ·₊ inputTriple C ε <₊ ε /4₊
  scaledInputTriple<quarter C ε = begin<
    fst (C ·₊ inputTriple C ε)
      <⟨ ·MonoL<
        (fst (inputTriple C ε)) (fst ((ε /4₊) ₊／₊ C))
        (fst C) (snd C) (inputTriple<ratio C ε) ⟩
    fst (C ·₊ ((ε /4₊) ₊／₊ C))
      ≡→≤⟨ ·／ C (ε /4₊) ⟩
    fst (ε /4₊) ◾


opaque
  rationalMultiplication-presCauchyGraphs :
    ∀ (x y z : ℕ → Real.ℝ) →
    (∀ n → B.BaseGraphClosure rationalMultiplication
      (x n) (y n) (z n)) →
    Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y → Real.Base.IsCauchySequence z
  rationalMultiplication-presCauchyGraphs x y z joint gx gy ε =
    PT.rec squash₁ withCoarseLeft (gx 1)
    where
    withCoarseLeft : Real.Base.CauchyTail x 1 →
      ∥ Real.Base.CauchyTail z ε ∥₁
    withCoarseLeft (K , xc) =
      PT.rec squash₁ (withCoarseRight K xc) (gy 1)
      where
      withCoarseRight :
        (K : ℕ) →
        (∀ m n → K ℕO.≤ m → K ℕO.≤ n →
          x m Real.Base.≈ᶜ[ 1 ] x n) →
        Real.Base.CauchyTail y 1 →
        ∥ Real.Base.CauchyTail z ε ∥₁
      withCoarseRight K xc (L , yc) =
        PT.rec squash₁ withAnchor
          (joint H 1 1 1)
        where
        H : ℕ
        H = ℕ.max K L

        withAnchor :
          (Σ[ a ∈ ℚ ]
            Σ[ b ∈ ℚ ]
              (Real.ιℚ a Real.Base.≈ᶜ[ 1 ] x H) ×
              (Real.ιℚ b Real.Base.≈ᶜ[ 1 ] y H) ×
              (Real.ιℚ (rationalMultiplication a b)
                Real.Base.≈ᶜ[ 1 ] z H)) →
          ∥ Real.Base.CauchyTail z ε ∥₁
        withAnchor (a , b , ιa∼xH , ιb∼yH , _) =
          PT.rec squash₁ withFineLeft (gx ρ)
          where
          B₁ : ℚ₊
          B₁ = anchorBound a

          B₂ : ℚ₊
          B₂ = anchorBound b

          C : ℚ₊
          C = B₂ +₊ B₁

          ρ : ℚ₊
          ρ = inputRadius C ε

          ρ<1 : ρ <₊ 1
          ρ<1 = inputRadius<one C ε

          withFineLeft : Real.Base.CauchyTail x ρ →
            ∥ Real.Base.CauchyTail z ε ∥₁
          withFineLeft (K' , xc') =
            PT.map (withFineRight K' xc') (gy ρ)
            where
            withFineRight :
              (K' : ℕ) →
              (∀ m n → K' ℕO.≤ m → K' ℕO.≤ n →
                x m Real.Base.≈ᶜ[ ρ ] x n) →
              Real.Base.CauchyTail y ρ →
              Real.Base.CauchyTail z ε
            withFineRight K' xc' (L' , yc') =
              N , λ m n N≤m N≤n →
                PT.rec2 (Real.Base.isProp≈ᶜ (z m) ε (z n))
                  (close m n N≤m N≤n)
                  (joint m ρ ρ (ε /4₊))
                  (joint n ρ ρ (ε /4₊))
              where
              N : ℕ
              N = ℕ.max H (ℕ.max K' L')

              H≤N : H ℕO.≤ N
              H≤N = ℕO.left-≤-max

              K≤H : K ℕO.≤ H
              K≤H = ℕO.left-≤-max {m = K} {n = L}

              L≤H : L ℕO.≤ H
              L≤H = ℕO.right-≤-max {n = L} {m = K}

              K'≤N : K' ℕO.≤ N
              K'≤N = ℕO.≤-trans
                (ℕO.left-≤-max {m = K'} {n = L'})
                (ℕO.right-≤-max
                  {n = ℕ.max K' L'} {m = H})

              L'≤N : L' ℕO.≤ N
              L'≤N = ℕO.≤-trans
                (ℕO.right-≤-max {n = L'} {m = K'})
                (ℕO.right-≤-max
                  {n = ℕ.max K' L'} {m = H})

              close :
                ∀ m n → N ℕO.≤ m → N ℕO.≤ n →
                (Σ[ p ∈ ℚ ]
                  Σ[ q ∈ ℚ ]
                    (Real.ιℚ p Real.Base.≈ᶜ[ ρ ] x m) ×
                    (Real.ιℚ q Real.Base.≈ᶜ[ ρ ] y m) ×
                    (Real.ιℚ (rationalMultiplication p q)
                      Real.Base.≈ᶜ[ ε /4₊ ] z m)) →
                (Σ[ p ∈ ℚ ]
                  Σ[ q ∈ ℚ ]
                    (Real.ιℚ p Real.Base.≈ᶜ[ ρ ] x n) ×
                    (Real.ιℚ q Real.Base.≈ᶜ[ ρ ] y n) ×
                    (Real.ιℚ (rationalMultiplication p q)
                      Real.Base.≈ᶜ[ ε /4₊ ] z n)) →
                z m Real.Base.≈ᶜ[ ε ] z n
              close m n N≤m N≤n
                  (p , q , ιp∼xm , ιq∼ym , ιpq∼zm)
                  (p' , q' , ιp'∼xn , ιq'∼yn , ιp'q'∼zn) =
                Real.Base.isMonotone≈ᶜ< (z m) (z n)
                  ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) ε
                  (tripleQuarter< ε)
                  (Real.Premetric.tri≈ᶜ (z m)
                    (Real.ιℚ (rationalMultiplication p' q')) (z n)
                    (ε /4₊ +₊ ε /4₊) (ε /4₊)
                    (Real.Premetric.tri≈ᶜ (z m)
                      (Real.ιℚ (rationalMultiplication p q))
                      (Real.ιℚ (rationalMultiplication p' q'))
                      (ε /4₊) (ε /4₊)
                      (Real.Base.sym≈ᶜ _ _ (ε /4₊) ιpq∼zm)
                      productsClose)
                    ιp'q'∼zn)
                where
                K≤m : K ℕO.≤ m
                K≤m = ℕO.≤-trans K≤H
                  (ℕO.≤-trans H≤N N≤m)

                K≤n : K ℕO.≤ n
                K≤n = ℕO.≤-trans K≤H
                  (ℕO.≤-trans H≤N N≤n)

                L≤m : L ℕO.≤ m
                L≤m = ℕO.≤-trans L≤H
                  (ℕO.≤-trans H≤N N≤m)

                L≤n : L ℕO.≤ n
                L≤n = ℕO.≤-trans L≤H
                  (ℕO.≤-trans H≤N N≤n)

                K'≤m : K' ℕO.≤ m
                K'≤m = ℕO.≤-trans K'≤N N≤m

                K'≤n : K' ℕO.≤ n
                K'≤n = ℕO.≤-trans K'≤N N≤n

                L'≤m : L' ℕO.≤ m
                L'≤m = ℕO.≤-trans L'≤N N≤m

                L'≤n : L' ℕO.≤ n
                L'≤n = ℕO.≤-trans L'≤N N≤n

                absq≤B₂ : abs q ℚ.≤ fst B₂
                absq≤B₂ = approximation-bounded b y L yc H m
                  L≤H L≤m ρ ρ<1 ιb∼yH q ιq∼ym

                absp'≤B₁ : abs p' ℚ.≤ fst B₁
                absp'≤B₁ = approximation-bounded a x K xc H n
                  K≤H K≤n ρ ρ<1 ιa∼xH p' ιp'∼xn

                ιp∼p' :
                  Real.ιℚ p Real.Base.≈ᶜ[ inputTriple C ε ] Real.ιℚ p'
                ιp∼p' = Real.Premetric.tri≈ᶜ (Real.ιℚ p) (x n) (Real.ιℚ p')
                  (ρ +₊ ρ) ρ
                  (Real.Premetric.tri≈ᶜ (Real.ιℚ p) (x m) (x n) ρ ρ
                    ιp∼xm (xc' m n K'≤m K'≤n))
                  (Real.Base.sym≈ᶜ _ _ ρ ιp'∼xn)

                ιq∼q' :
                  Real.ιℚ q Real.Base.≈ᶜ[ inputTriple C ε ] Real.ιℚ q'
                ιq∼q' = Real.Premetric.tri≈ᶜ (Real.ιℚ q) (y n) (Real.ιℚ q')
                  (ρ +₊ ρ) ρ
                  (Real.Premetric.tri≈ᶜ (Real.ιℚ q) (y m) (y n) ρ ρ
                    ιq∼ym (yc' m n L'≤m L'≤n))
                  (Real.Base.sym≈ᶜ _ _ ρ ιq'∼yn)

                productsDistance :
                  abs (rationalMultiplication p q ℚR.-
                    rationalMultiplication p' q')
                    ℚ.< fst (ε /4₊)
                productsDistance =
                  ℚ.isTrans< _ (fst (C ·₊ inputTriple C ε)) _
                    (rationalMultiplication-bounded B₁ B₂ p q p' q'
                      (inputTriple C ε) absq≤B₂ absp'≤B₁
                      (Real.Approximation.ι-ι→≈ p p' (inputTriple C ε) ιp∼p')
                      (Real.Approximation.ι-ι→≈ q q' (inputTriple C ε) ιq∼q'))
                    (scaledInputTriple<quarter C ε)

                productsClose :
                  Real.ιℚ (rationalMultiplication p q)
                    Real.Base.≈ᶜ[ ε /4₊ ]
                  Real.ιℚ (rationalMultiplication p' q')
                productsClose = Real.Base.ι-ι _ _ (ε /4₊) productsDistance


rationalMultiplication-preservesCauchyGraphs :
  B.PreservesBaseCauchyGraphs rationalMultiplication
rationalMultiplication-preservesCauchyGraphs =
  B.preservesCauchyGraphs rationalMultiplication-presCauchyGraphs


multiplication : Real.ℝ → Real.ℝ → Real.ℝ
multiplication = B.extendBase
  rationalMultiplication rationalMultiplication-preservesCauchyGraphs

infixl 7 _·_

_·_ : Real.ℝ → Real.ℝ → Real.ℝ
_·_ = multiplication


mul-diagonalIsCauchySequence : ∀ {x y} →
  Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y →
  Real.Base.IsCauchySequence (λ n → x n · y n)
mul-diagonalIsCauchySequence {x} {y} =
  B.extend-preservesDiagonalCauchy
    (λ p q → Real.ιℚ (rationalMultiplication p q))
    rationalMultiplication-preservesCauchyGraphs x y


multiplication-joint : ∀ x y →
  B.BaseGraphClosure rationalMultiplication x y (x · y)
multiplication-joint =
  B.extend-graph
    (λ p q → Real.ιℚ (rationalMultiplication p q))
    rationalMultiplication-preservesCauchyGraphs


mul-ι-ι : ∀ p q →
  Real.ιℚ p · Real.ιℚ q ≡ Real.ιℚ (p ℚR.· q)
mul-ι-ι p q = refl


mul-ι-lim : ∀ p y gy →
  Real.ιℚ p · Real.Base.lim y gy ≡
  Real.Base.lim (λ n → Real.ιℚ p · y n) _
mul-ι-lim p y gy = refl


mul-lim-ι : ∀ x gx q →
  Real.Base.lim x gx · Real.ιℚ q ≡
  Real.Base.lim (λ n → x n · Real.ιℚ q) _
mul-lim-ι x gx q = refl


mul-lim-lim : ∀ x gx y gy →
  Real.Base.lim x gx · Real.Base.lim y gy ≡
  Real.Base.lim (λ n → x n · y n)
    (mul-diagonalIsCauchySequence gx gy)
mul-lim-lim x gx y gy =
  B.extend-lim-lim
    (λ p q → Real.ιℚ (rationalMultiplication p q))
    rationalMultiplication-preservesCauchyGraphs x gx y gy
