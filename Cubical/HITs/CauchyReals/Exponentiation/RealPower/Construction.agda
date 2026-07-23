module Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Data.Int.Fast.Properties as ℤP
import Cubical.Data.Int.Base as ℤStd
import Cubical.Data.Int.Properties as ℤStdP
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (invℚ)

import Cubical.Algebra.OrderedCommRing.Properties as OCRP
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using (ℚOrderedCommRing)

private
  module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order
open import Cubical.HITs.CauchyReals.Analysis.Order.Functions
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse hiding
  (≤ContWP; ≤ContWP＃≤; ≤ContWP＃≤')
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeq-one; lnSeqCont; stepℚ₊; fromSucℚ₊
  ; posStepWidth; negStepWidth)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Limit

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR

open import Cubical.Algebra.Group.DirProd
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Infrastructure public

module BDL (z : ℝ₊) (Z : ℕ)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
           where

 opaque
  unfolding _+ᵣ_
  bdl' : (z : ℝ₊) (Z : ℕ)
           (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
           (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
           → 1 ≤ᵣ fst z → boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
  bdl' z Z z≤Z 1/Z≤z 1≤z n = ℚ.elimBy≡⊎<'
   {A = λ x y →
     abs x ℚ.≤ fromNat (suc n) →
     abs y ℚ.≤ fromNat (suc n) →
     absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)) ≤ᵣ
       rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))}
   (λ x y X y∈ x∈ → subst2 _≤ᵣ_
        (minusComm-absᵣ (fst (z ^ℚ y)) (fst (z ^ℚ x)))
        (cong (rat ∘ (fst (slUpBd Z n) ℚ.·_))
          (ℚO.abs-Comm y x))
        (X x∈ y∈)  )
   (λ x _ _ → subst2 _≤ᵣ_
      (cong absᵣ (sym (+-ᵣ (fst (z ^ℚ x)))))
      (cong rat (sym (Rℚ.0RightAnnihilates'
        (fst (slUpBd Z n)) (abs (x ℚ.- x))
        (cong abs (ℚ.+InvR x)))))
      (≡ᵣWeaken≤ᵣ (absᵣ (rat 0)) (rat 0) (absᵣ-rat 0)))
   λ y₀ h₊ y₀∈ y₁∈ →
    let
      y₁ : ℚ
      y₁ = y₀ ℚ.+ fst h₊
      y₀<y₁ : y₀ ℚ.< y₁
      y₀<y₁ = ℚ≤→<+₊ y₀ y₀ h₊ (ℚ.isRefl≤ y₀)
      step₊ : ℝ₊
      step₊ = ℚ₊→ℝ₊ (ℚ.<→ℚ₊ y₀ y₁ y₀<y₁)
      slope : ℝ
      slope = fst (z ^ℚ fst (fromSucℚ₊ n)) ·ᵣ (fst z -ᵣ 1)
      slopeBound : ℝ
      slopeBound =
        fst ((ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) ^ℚ fst (fromSucℚ₊ n))
          ·ᵣ (fromNat (suc (suc Z)) +ᵣ rat [ ℤ.negsuc 0 / 1 ])
    in isTrans≡≤ᵣ
      (absᵣ (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀)))
      (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
      (rat (fst (slUpBd Z n) ℚ.· abs (y₁ ℚ.- y₀)))
      (absᵣNonNeg (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
        (x≤y→0≤y-x (fst (z ^ℚ y₀)) (fst (z ^ℚ y₁))
          (^ℚ-MonotoneR {x = z} y₀ y₁
            (ℚ.<Weaken≤ y₀ y₁ y₀<y₁) 1≤z )))
      (isTrans≤≡ᵣ
       (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
       (fst step₊ ·ᵣ slopeBound)
       (rat (fst (slUpBd Z n) ℚ.· abs (y₁ ℚ.- y₀)))
       (isTrans≤ᵣ
       (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
       (fst step₊ ·ᵣ slope)
       (fst step₊ ·ᵣ slopeBound) (
     (fst (z/y≤x₊≃z≤y₊·x
       (fst (z ^ℚ fst (fromSucℚ₊ n)) ·ᵣ (fst z -ᵣ 1))
       (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
       step₊)
       (slope-upper-bound z (fromSucℚ₊ n)
     y₀ y₁ y₀<y₁
      (absTo≤×≤ (fst (fromSucℚ₊ n)) y₀ y₀∈)
      (absTo≤×≤ (fst (fromSucℚ₊ n)) y₁ y₁∈))))
       (≤ᵣ-o· slope slopeBound (y₁ ℚ.- y₀)
        (ℚ.<Weaken≤ 0 (y₁ ℚ.- y₀) (ℚ.-< y₀ y₁ y₀<y₁))
        (≤ᵣ₊Monotone·ᵣ
          (fst (z ^ℚ fst (fromSucℚ₊ n)))
          (fst ((ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) ^ℚ fst (fromSucℚ₊ n)))
          (fst z -ᵣ 1)
          (fromNat (suc (suc Z)) +ᵣ rat [ ℤ.negsuc 0 / 1 ])
          (<ᵣWeaken≤ᵣ 0
            (fst ((ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) ^ℚ fst (fromSucℚ₊ n)))
            (snd ((ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) ^ℚ fst (fromSucℚ₊ n))))
          (x≤y→0≤y-x 1 (fst z) 1≤z)
          (^ℚ-Monotone {x = z}
           {y = ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))}
           (fromSucℚ₊ n) z≤Z)
          (isTrans≡≤ᵣ
            (fst z -ᵣ 1)
            (fst z +ᵣ rat [ ℤ.negsuc 0 / 1 ])
            (fromNat (suc (suc Z)) +ᵣ rat [ ℤ.negsuc 0 / 1 ])
            (cong (fst z +ᵣ_) (-ᵣ-rat 1))
            (≤ᵣ-+o (fst z) (fromNat (suc (suc Z)))
              (rat [ ℤ.negsuc 0 / 1 ]) z≤Z)))))
       (·ᵣComm _ _ ∙
        cong₂ (_·ᵣ_)
          (cong₂ (_·ᵣ_) (^ⁿ-ℚ^ⁿ (suc n) [ pos (suc (suc Z)) / 1 ])
            (+ᵣ-rat
              [ pos (suc (suc Z)) / 1 ]
              [ ℤ.negsuc 0 / 1 ]
             ∙ cong rat
               (ℚ.ℤ+→ℚ+
                 (pos (suc (suc Z))) (ℤ.negsuc 0)))
           ∙ sym (rat·ᵣrat
             ([ pos (suc (suc Z)) / 1 ] ℚ.^ⁿ (suc n))
             [ pos (suc Z) / 1 ]) )
          (cong rat (sym (ℚO.0<→abs≡id (y₁ ℚ.- y₀)
            (ℚ.-< y₀ y₁ y₀<y₁))))
         ∙ sym (rat·ᵣrat
           (fst (slUpBd Z n)) (abs (y₁ ℚ.- y₀)))))


  bdl : boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
  bdl n x y x< y< = isTrans≡≤ᵣ _ _ _
     (cong (λ z → absᵣ
       (fst (z ^ℚ  y) -ᵣ fst (z ^ℚ x)))
       (ℝ₊≡ refl))
   (continuousClosedIntervalComparison {x₀ = [ 1 / fromNat (suc (suc Z)) ]}
        {x₁ = fromNat (suc (suc Z)) }
         (ℚ.isTrans≤ [ 1 / (fromNat (suc (suc Z))) ] 1 (fromNat (suc (suc Z)))
          (ℚ.invℚ₊≤invℚ₊ (fromNat (suc (suc Z))) 1
            ((≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos 1 (suc (suc Z))
            (ℕ.suc-≤-suc (ℕ.zero-≤ {suc Z})))))  )
           ((≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos 1 (suc (suc Z))
            (ℕ.suc-≤-suc (ℕ.zero-≤ {suc Z}))))))
         {f₀ = λ x₁ z₁ →
             let 0<x₁ =
                   isTrans<≤ᵣ (rat [ pos 0 / 1 ])
                     (rat [ 1 / fromNat (suc (suc Z)) ]) x₁
                     (<ℚ→<ᵣ [ pos 0 / 1 ]
                       [ 1 / fromNat (suc (suc Z)) ]
                       (0<pos 0 (fromNat (suc (suc Z)))))
                     (fst z₁)
             in absᵣ (fst ((x₁ , 0<x₁) ^ℚ  y) -ᵣ fst ((x₁ , 0<x₁) ^ℚ x))}
         {f₁ = λ _ _ → rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))}
         (IsContinuousWP∘'
          (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
            (rat (fromNat (suc (suc Z)))))
          absᵣ
          (λ x₁ z₁ →
            let 0<x₁ =
                  isTrans<≤ᵣ (rat [ pos 0 / 1 ])
                    (rat [ 1 / fromNat (suc (suc Z)) ]) x₁
                    (<ℚ→<ᵣ [ pos 0 / 1 ]
                      [ 1 / fromNat (suc (suc Z)) ]
                      (0<pos 0 (fromNat (suc (suc Z)))))
                    (fst z₁)
            in fst ((x₁ , 0<x₁) ^ℚ y) -ᵣ fst ((x₁ , 0<x₁) ^ℚ x))
          IsContinuousAbsᵣ (IsContinuousWithPred⊆ pred0<
          (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
            (rat (fromNat (suc (suc Z)))))
          (λ u 0<u →
            fst ((u , 0<u) ^ℚ y) -ᵣ fst ((u , 0<u) ^ℚ x))
          (λ z z∈ → isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _))
           (fst z∈))
          ((contDiagNE₂WP sumR pred0<
         (curry (fst ∘ (_^ℚ y)))
         (λ u 0<u → -ᵣ fst ((u , 0<u) ^ℚ x))
         (IsContinuous^ℚ y)
            (IsContinuousWP∘' pred0< (-ᵣ_)
              (curry (fst ∘ (_^ℚ x))) IsContinuous-ᵣ
              (IsContinuous^ℚ x))))))
         ((AsContinuousWithPred
           (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
             (rat (fromNat (suc (suc Z)))))
           (λ _ → rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x)))
           (IsContinuousConst
             (rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))))))
           www
         (fst z) (1/Z≤z , z≤Z))

      where
      www : (u : ℚ)
             (x₀<u<x₁
              : rat u ∈
                intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
                (rat (fromNat (suc (suc Z))))) →
             absᵣ
             (fst
              ((rat u ,
                isTrans<≤ᵣ (rat [ pos 0 / 1 ]) (rat [ 1 / fromNat (suc (suc Z)) ])
                (rat u)
                (<ℚ→<ᵣ [ pos 0 / 1 ] [ 1 / fromNat (suc (suc Z)) ]
                 (0<pos 0 (fromNat (suc (suc Z)))))
                (fst x₀<u<x₁))
               ^ℚ y)
              -ᵣ
              fst
              ((rat u ,
                isTrans<≤ᵣ (rat [ pos 0 / 1 ]) (rat [ 1 / fromNat (suc (suc Z)) ])
                (rat u)
                (<ℚ→<ᵣ [ pos 0 / 1 ] [ 1 / fromNat (suc (suc Z)) ]
                 (0<pos 0 (fromNat (suc (suc Z)))))
                (fst x₀<u<x₁))
               ^ℚ x))
             ≤ᵣ rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))
      www u (≤u , u≤) =
        ⊎.rec
          wwwL
          wwwR
          (ℚ.≤cases 1 u)
       where
       u₊ : ℝ₊
       u₊ = (rat u ,
                  isTrans<≤ᵣ (rat [ pos 0 / 1 ]) (rat [ 1 / fromNat (suc (suc Z)) ])
                  (rat u)
                  (<ℚ→<ᵣ [ pos 0 / 1 ] [ 1 / fromNat (suc (suc Z)) ]
                   (0<pos 0 (fromNat (suc (suc Z)))))
                  ≤u)
       wwwL : 1 ℚ.≤ u →
               absᵣ (fst (u₊ ^ℚ y) -ᵣ fst (u₊ ^ℚ x))
               ≤ᵣ rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))
       wwwL 1≤u = bdl' u₊
          Z u≤ ≤u (≤ℚ→≤ᵣ 1 u 1≤u) n x y x< y<

       wwwR : u ℚ.≤ 1 →
                absᵣ (fst (u₊ ^ℚ y) -ᵣ fst (u₊ ^ℚ x))
               ≤ᵣ rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))
       wwwR u≤1 = subst2 _≤ᵣ_
              (cong absᵣ
                (cong₂ _-ᵣ_
                  (cong fst (sym (^ℚ-minus u₊ y)))
                  (cong fst (sym (^ℚ-minus u₊ x)))))
               (cong (λ uu → rat (fst (slUpBd Z n) ℚ.· uu))
                 (cong abs negDifference ∙ ℚO.abs-Comm x y))
            wwwR'
        where
         negDifference :
           (ℚ.- y) ℚ.- (ℚ.- x) ≡ x ℚ.- y
         negDifference = ℚ!

         wwwR' : absᵣ (fst ((invℝ₊ u₊) ^ℚ (ℚ.- y)) -ᵣ fst ((invℝ₊ u₊) ^ℚ (ℚ.- x)))
                ≤ᵣ rat (fst (slUpBd Z n) ℚ.· abs ((ℚ.- y) ℚ.- (ℚ.- x)))
         wwwR' = bdl' (invℝ₊ u₊) Z
          (isTrans≤≡ᵣ _ _ _
            (invEq (invℝ₊-≤-invℝ₊ u₊ (ℚ₊→ℝ₊ (stepℚ₊ Z))) ≤u)
            (invℝ₊-rat (stepℚ₊ Z))  )
          (isTrans≡≤ᵣ _ _ _
            (sym (invℝ₊-rat (fromSucℚ₊ (suc Z))))
            (invEq (invℝ₊-≤-invℝ₊ (ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) u₊) u≤))
          (isTrans≡≤ᵣ _ _ _ (sym (invℝ₊-rat 1))
            (invEq (invℝ₊-≤-invℝ₊ 1 u₊)
              (≤ℚ→≤ᵣ u 1 u≤1)))

          n (ℚ.- x) (ℚ.- y)
           (subst (ℚ._≤ (fromNat (suc n))) (ℚ.-abs x) x<)
           (subst (ℚ._≤ (fromNat (suc n))) (ℚ.-abs y) y<)

 open BoundedLipsch (fst ∘ z ^ℚ_) (slUpBd Z) bdl public
 module BL = BoundedLipsch (fst ∘ z ^ℚ_) (slUpBd Z) bdl

 private
  zeroℚ : ℚ
  zeroℚ = 0

  rat-zeroℚ : rat zeroℚ ≡ 0
  rat-zeroℚ = refl

 opaque
  𝒇-zero-rat :
    BL.𝒇 (rat zeroℚ) ≡ (fst ∘ z ^ℚ_) zeroℚ
  𝒇-zero-rat = BL.𝒇-rat zeroℚ

  𝒇-zero : BL.𝒇 (rat zeroℚ) ≡ 1
  𝒇-zero = _∙_
    {x = BL.𝒇 (rat zeroℚ)} {y = fst (z ^ℚ zeroℚ)} {z = 1}
    𝒇-zero-rat (cong fst (^ℚ-zero z))

  𝒇-zero-real : BL.𝒇 0 ≡ 1
  𝒇-zero-real = cong BL.𝒇 (sym rat-zeroℚ) ∙ 𝒇-zero

 mid-𝒇 : ∀ q q' q'' → q ℚ.≤ q' → q' ℚ.≤ q'' →
    minᵣ (BL.𝒇 (rat q))
         (BL.𝒇 (rat q'')) ≤ᵣ BL.𝒇 (rat q')
 mid-𝒇 q q' q'' q≤q' q'≤q'' =
   subst2 _≤ᵣ_
     (cong₂ minᵣ (sym (BL.𝒇-rat q)) (sym (BL.𝒇-rat q'')))
     (sym (BL.𝒇-rat q'))
     (monotone^ℚ q q' q'' q≤q' q'≤q'' z)

 opaque
  unfolding minᵣ maxᵣ
  0<𝒇 : ∀ x → 0 <ᵣ BL.𝒇 x
  0<𝒇 x = PT.rec (isProp<ᵣ _ _)
   (λ ((q , q') , q'-q<1 , q<x , x<q') →
     let q⊓q' = (minᵣ₊ (z ^ℚ q) (z ^ℚ q'))
     in PT.rec (isProp<ᵣ _ _)
        (λ (ε , 0<ε , ε<q⊓q') →
          PT.rec (isProp<ᵣ _ _)
          (λ (δ , X) →
           PT.rec (isProp<ᵣ _ _)
             (λ (r , r-x≤δ , x≤r) →
                let r' = ℚ.clamp q q' r
                    r'-x≤δ = isTrans≤ᵣ _ _ _
                              (≤ᵣ-+o _ _ (-ᵣ x)
                                (≤ℚ→≤ᵣ _ _
                             (ℚ.clamped≤ q q' r
                               (ℚ.<Weaken≤ _ _
                                 (<ᵣ→<ℚ _ _ (isTrans<≤ᵣ _ _ _ q<x x≤r))))) ) r-x≤δ
                    x≤r' = isTrans≤≡ᵣ _ _ _
                             (≤min-lem _ (rat (ℚ.max q r)) (rat q')
                               (isTrans≤ᵣ _ _ _ x≤r
                                (≤ℚ→≤ᵣ _ _ (ℚ.≤max' q r)))
                               (<ᵣWeaken≤ᵣ _ _ x<q'))
                             (minᵣ-rat (ℚ.max q r) q')
                    |fx-fr|<ε = fst (∼≃abs<ε _ _ _)
                        (sym∼ _ _ _ (X (rat r') (sym∼ _ _ _
                          ((invEq (∼≃abs<ε _ _ _)
                         (isTrans≡<ᵣ _ _ _
                           (absᵣNonNeg _ (x≤y→0≤y-x _ _ x≤r'))
                            (isTrans≤<ᵣ _ _ _
                                r'-x≤δ (<ℚ→<ᵣ _ _ (/2₊<id δ))))))) ))
                    zzz =
                         mid-𝒇 q r' q'
                          (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                           (<ᵣWeaken≤ᵣ _ _ q<x) x≤r'))
                          (ℚ.clamp≤ q q' r)
                    zzz' = isTrans<≤ᵣ _ _ _
                             (isTrans<≡ᵣ _ _ _ ε<q⊓q'
                               (cong₂ minᵣ
                                 (sym (BL.𝒇-rat q)) (sym (BL.𝒇-rat q'))))
                              zzz
                in isTrans≡<ᵣ _ _ _ (sym (Rℝ.+InvR _)) (a-b<c⇒a-c<b _ _ _
                      (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                     (isTrans<ᵣ _ _ _ |fx-fr|<ε zzz')))
               ) (∃rationalApprox≤ x (δ /2₊)))

          (BL.𝒇-cont x (ε , <ᵣ→<ℚ _ _ 0<ε))
          )
       (denseℚinℝ 0 _ (snd q⊓q')) )
    (∃rationalApprox x 1)

 𝒇₊ : ℝ → ℝ₊
 𝒇₊ x = (BL.𝒇 x , 0<𝒇 x)

 opaque
  unfolding minᵣ maxᵣ
  flₙ≡𝒇 : ∀ x n → (x ∈ intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
            →  fst (fst (BL.flₙ n)) x ≡ BL.𝒇 x
  flₙ≡𝒇 x n x∈ =
    let
      lower : ℝ
      lower = rat (BL.clampL n)
      upper : ℝ
      upper = rat (BL.clampU n)

      fₙ : ℝ → ℝ
      fₙ = fst (fst (BL.flₙ n))

      clamped : ℝ
      clamped = clampᵣ lower upper x

      agreement-rat : ∀ r →
        fₙ (rat r) ≡ BL.𝒇 (clampᵣ lower upper (rat r))
      agreement-rat r =
        let
          qclamp : ℚ
          qclamp = ℚ.clamp (BL.clampL n) (BL.clampU n) r

          fl-path : fₙ (rat r) ≡ (fst ∘ z ^ℚ_) qclamp
          fl-path = BL.flₙ-rat n r

          rat-path : (fst ∘ z ^ℚ_) qclamp ≡ BL.𝒇 (rat qclamp)
          rat-path = sym (BL.𝒇-rat qclamp)

          clamp-path :
            BL.𝒇 (rat qclamp) ≡ BL.𝒇 (clampᵣ lower upper (rat r))
          clamp-path = cong BL.𝒇
            (sym (clampᵣ-rat (BL.clampL n) (BL.clampU n) r))
        in fl-path ∙ rat-path ∙ clamp-path

      agreement : fₙ x ≡ BL.𝒇 clamped
      agreement = ≡Continuous fₙ (BL.𝒇 ∘ clampᵣ lower upper)
        (snd (BL.flₙ n))
        (IsContinuous∘ BL.𝒇 (clampᵣ lower upper)
          BL.𝒇-cont (IsContinuousClamp lower upper))
        agreement-rat x

      unclamp : BL.𝒇 clamped ≡ BL.𝒇 x
      unclamp = cong BL.𝒇
        (sym (∈ℚintervalℙ→clampᵣ≡ lower upper x x∈))
    in agreement ∙ unclamp


  𝒇-monotone : 1 ≤ᵣ fst z → ∀ x y → x ≤ᵣ y → BL.𝒇 x ≤ᵣ BL.𝒇 y
  𝒇-monotone 1≤z x y x≤y =
   ≡→≤ᵣ ((≡Cont₂ (cont₂∘ (contNE₂ maxR) BL.𝒇-cont BL.𝒇-cont)
     (cont∘₂ BL.𝒇-cont (contNE₂ maxR) )
     (ℚ.elimBy≤
        (λ u u' X → maxᵣComm _ _ ∙∙ X ∙∙
          cong BL.𝒇 (maxᵣComm (rat u) (rat u')))
        λ u u' u≤u' →
          cong₂ maxᵣ (BL.𝒇-rat u) (BL.𝒇-rat u')
           ∙∙ ≤ᵣ→≡ (^ℚ-MonotoneR u u' u≤u' 1≤z) ∙
            cong (fst ∘ (z ^ℚ_)) (sym (ℚ.≤→max u u' u≤u')) ∙∙
           (sym (BL.𝒇-rat (ℚ.max u u')) ∙
             cong BL.𝒇 (sym (maxᵣ-rat u u'))))
         x y)
    ∙ cong BL.𝒇 (≤ᵣ→≡ x≤y))


 opaque
  unfolding _<ᵣ_
  𝒇-monotone-str : 1 <ᵣ fst z → ∀ x y → x <ᵣ y → BL.𝒇 x <ᵣ BL.𝒇 y
  𝒇-monotone-str 1<z x y = PT.rec (isProp<ᵣ _ _)
     λ ((q , q') , (≤q , q<q' , q'≤)) →
       isTrans≤<ᵣ _ _ _ (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) x (rat q) ≤q)
         (isTrans<≤ᵣ _ _ _ (
            subst2 _<ᵣ_ (sym (BL.𝒇-rat q)) (sym (BL.𝒇-rat q'))
             (^ℚ-StrictMonotoneR 1<z q q' q<q'))
           (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) (rat q') y q'≤))

 module _ (n : ℕ) where


  incr^ : 1 <ᵣ fst z → IsStrictlyIncreasingOn
            (intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
            (λ x _ → fst (fst (BL.flₙ n)) x)
  incr^ 1<z x x∈ y y∈ x<y =
    subst2 _<ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone-str 1<z  x y x<y)


  nondecr^ : 1 ≤ᵣ fst z → IsNondecreasingOn
      (intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
      (λ x _ → fst (fst (BL.flₙ n)) x)
  nondecr^ 1≤z x x∈ y y∈ x≤y =
    subst2 _≤ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone 1≤z x y x≤y)



 open expPreDer Z public
 open expPreDer' z z≤Z 1/Z≤z public

 opaque
  unfolding _+ᵣ_

  𝒇-diffQuot : ∀ r → 0 ＃ r → ℝ
  𝒇-diffQuot r r＃0 = (BL.𝒇 r -ᵣ BL.𝒇 0) ／ᵣ[ r , r＃0 ]

  𝒇-diffQuot-cont : IsContinuousWithPred 0＃ₚ 𝒇-diffQuot
  𝒇-diffQuot-cont =
    cont₂·ᵣWP 0＃ₚ
      (λ r _ → BL.𝒇 r -ᵣ BL.𝒇 0)
      invℝ
      (AsContinuousWithPred 0＃ₚ
        (λ r → BL.𝒇 r -ᵣ BL.𝒇 0)
        (IsContinuous∘
          (λ u → u +ᵣ (-ᵣ BL.𝒇 0)) BL.𝒇
          (IsContinuous+ᵣR (-ᵣ BL.𝒇 0)) BL.𝒇-cont))
      IsContinuousWithPredInvℝ

 opaque
  unfolding _+ᵣ_ 𝒇-diffQuot

  𝒇-diffQuot-formula : ∀ r (r＃0 : 0 ＃ r) →
    𝒇-diffQuot r r＃0 ≡
      (BL.𝒇 r -ᵣ BL.𝒇 (rat zeroℚ)) ·ᵣ invℝ r r＃0
  𝒇-diffQuot-formula r r＃0 =
    cong₂ _·ᵣ_
      (cong₂ _-ᵣ_ refl (cong BL.𝒇 (sym rat-zeroℚ))) refl

 opaque
  unfolding _+ᵣ_

  𝒇-diffQuot≤lnSeq : ∀ n r (0＃r : 0 ＃ r)
    → r ≤ᵣ rat [ 1 / 2+ n ]
    → 𝒇-diffQuot r 0＃r ≤ᵣ lnSeq z n
  𝒇-diffQuot≤lnSeq n =
    ≤ContWP＃≤ [ 1 / 2+ n ] (0<pos 0 (2+ n))
      𝒇-diffQuot-cont
      (AsContinuousWithPred 0＃ₚ (λ _ → lnSeq z n)
        (IsContinuousConst (lnSeq z n)))
      (λ u u∈ u≤ →
        let
          leftSlope : ℝ
          leftSlope =
            (fst (z ^ℚ u) -ᵣ fst (z ^ℚ zeroℚ))
              ／ᵣ[ rat u -ᵣ rat zeroℚ , invEq (＃Δ _ _) u∈ ]

          rightSlope : ℝ
          rightSlope =
            (fst (z ^ℚ [ 1 / 2+ n ]) -ᵣ fst (z ^ℚ zeroℚ))
              ／ᵣ₊ ℚ₊→ℝ₊ (posStepWidth n)

          slopeDifference : ℝ
          slopeDifference = fst (z ^ℚ u) -ᵣ fst (z ^ℚ zeroℚ)

          functionDifference : ℝ
          functionDifference =
            BL.𝒇 (rat u) -ᵣ BL.𝒇 (rat zeroℚ)

          differencePath : slopeDifference ≡ functionDifference
          differencePath = cong₂ _-ᵣ_
            (sym (BL.𝒇-rat u))
            (sym (BL.𝒇-rat zeroℚ))

          denominator : ℝ
          denominator = rat u -ᵣ rat zeroℚ

          denominator＃0 : 0 ＃ denominator
          denominator＃0 = invEq (＃Δ (rat u) (rat zeroℚ)) u∈

          inversePath :
            invℝ denominator denominator＃0 ≡ invℝ (rat u) u∈
          inversePath = cong₂ invℝ
            (Rℝ.+IdR' (rat u) (-ᵣ rat zeroℚ) (-ᵣ-rat zeroℚ))
            (toPathP (isProp＃ _ _ _ _))

          expandedDiffQuot : ℝ
          expandedDiffQuot =
            functionDifference ·ᵣ invℝ (rat u) u∈

          expandedPath : leftSlope ≡ expandedDiffQuot
          expandedPath = cong₂ _·ᵣ_ differencePath inversePath

          foldDiffQuot : expandedDiffQuot ≡ 𝒇-diffQuot (rat u) u∈
          foldDiffQuot = sym (𝒇-diffQuot-formula (rat u) u∈)

          leftPath : leftSlope ≡ 𝒇-diffQuot (rat u) u∈
          leftPath = expandedPath ∙ foldDiffQuot

          rightPath : rightSlope ≡ lnSeq z n
          rightPath = cong₂ _·ᵣ_
            refl
            (invℝ₊-rat (posStepWidth n)
              ∙ cong rat
                  (cong (fst ∘ invℚ₊)
                    (ℚ₊≡ {x = posStepWidth n}
                      {y = stepℚ₊ n}
                      (ℚ.+IdR [ 1 / 2+ n ]))))

          slope≤ : leftSlope ≤ᵣ rightSlope
          slope≤ = slope-monotone＃ z zeroℚ u
            zeroℚ [ 1 / 2+ n ]
            u∈ (0<pos 0 (2+ n)) (ℚ.isRefl≤ zeroℚ) u≤
        in subst2 _≤ᵣ_ leftPath rightPath slope≤)

  lnSeq'≤𝒇-diffQuot : ∀ n r (0＃r : 0 ＃ r)
    → rat (ℚ.- [ 1 / 2+ n ]) ≤ᵣ r
    → lnSeq' z n ≤ᵣ 𝒇-diffQuot r 0＃r
  lnSeq'≤𝒇-diffQuot n =
    ≤ContWP＃≤' (ℚ.- [ 1 / 2+ n ])
      (ℚ.minus-< 0 [ 1 / 2+ n ] (0<pos 0 (2+ n)))
      (AsContinuousWithPred 0＃ₚ (λ _ → lnSeq' z n)
        (IsContinuousConst (lnSeq' z n)))
      𝒇-diffQuot-cont
      (λ u u∈ u≤ →
        subst2 _≤ᵣ_
          (cong₂ _·ᵣ_
            refl
            (invℝ₊-rat (negStepWidth n)
              ∙ cong rat
                  (cong (fst ∘ invℚ₊)
                    (ℚ₊≡
                      {x = negStepWidth n}
                      {y = stepℚ₊ n}
                      (ℚ.+IdL (ℚ.- (ℚ.- [ 1 / 2+ n ]))
                        ∙ ℚ.-Invol [ 1 / 2+ n ])))))
          (sym (-ᵣ·-ᵣ _ _)
            ∙ cong₂ _·ᵣ_
                (-[x-y]≡y-x _ _
                  ∙ cong₂ _-ᵣ_
                      (sym (BL.𝒇-rat u))
                      (sym (BL.𝒇-rat zeroℚ)))
                (-invℝ _ _
                  ∙ cong₂ invℝ
                      (cong -ᵣ_ (+IdL _) ∙ -ᵣInvol _)
                      (toPathP (isProp＃ _ _ _ _)))
            ∙ sym (𝒇-diffQuot-formula (rat u) u∈))
          (slope-monotone＃' z
            (ℚ.- [ 1 / 2+ n ]) zeroℚ u zeroℚ
            (ℚ.minus-< 0 [ 1 / 2+ n ] (0<pos 0 (2+ n)))
            (isSym＃ _ _ u∈) u≤ (ℚ.isRefl≤ 0)))


  opaque
    𝒇· : ∀ x y → BL.𝒇 x ·ᵣ BL.𝒇 y ≡ BL.𝒇 (x +ᵣ y)
    𝒇· = ≡Cont₂
         (cont₂∘ IsContinuous₂·ᵣ BL.𝒇-cont BL.𝒇-cont )
         (cont∘₂ BL.𝒇-cont (contNE₂ sumR))
         λ u u' → cong₂ _·ᵣ_ (BL.𝒇-rat u) (BL.𝒇-rat u')
            ∙ cong fst (^ℚ-+ z u u')
            ∙ sym (BL.𝒇-rat (u ℚ.+ u'))
            ∙ cong BL.𝒇 (sym (+ᵣ-rat u u'))

opaque
 BDL-fun₊-cont : ∀ (z : ℝ₊) Z
   (z≤ : fst z ≤ᵣ fromNat (suc (suc Z)))
   (≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z) →
   IsContinuous (fst ∘ BDL.𝒇₊ z Z z≤ ≤z)
 BDL-fun₊-cont z Z z≤ ≤z = BDL.𝒇-cont z Z z≤ ≤z

opaque
 BDL-preLn-positive-path : ∀ x (p q : 0 <ᵣ x) Z
   (x≤ : x ≤ᵣ fromNat (suc (suc Z)))
   (≤x : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ x) →
   BDL.preLn (x , p) Z x≤ ≤x ≡ BDL.preLn (x , q) Z x≤ ≤x
 BDL-preLn-positive-path x p q Z x≤ ≤x i =
   fromCauchySequence'-≡-lem (lnSeq (x , positivity-path i))
     (left-cauchy-path i) (right-cauchy-path i) i
  where
  positivity-path : p ≡ q
  positivity-path = isProp<ᵣ 0 x p q

  module F = BDL (x , p) Z x≤ ≤x
  module F' = BDL (x , q) Z x≤ ≤x

  left-cauchy-path : PathP
    (λ i → IsCauchySequence' (lnSeq (x , positivity-path i)))
    F.ca-lnSeq
    (transport
      (λ i → IsCauchySequence' (lnSeq (x , positivity-path i)))
      F.ca-lnSeq)
  left-cauchy-path = toPathP refl

  right-cauchy-path : PathP
    (λ i → IsCauchySequence' (lnSeq (x , positivity-path i)))
    (transport
      (λ i → IsCauchySequence' (lnSeq (x , positivity-path (~ i))))
      F'.ca-lnSeq)
    F'.ca-lnSeq
  right-cauchy-path = symP (toPathP refl)

opaque
 BDL-preLn-η : ∀ (z : ℝ₊) Z
   (z≤ : fst z ≤ᵣ fromNat (suc (suc Z)))
   (≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z) →
   BDL.preLn (fst z , snd z) Z z≤ ≤z ≡ BDL.preLn z Z z≤ ≤z
 BDL-preLn-η z Z z≤ ≤z = refl

opaque
 BDL-preLn-inv-components : ∀ (z : ℝ₊) Z
   (z≤ : fst z ≤ᵣ fromNat (suc (suc Z)))
   (≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
   (z⁻¹≤ : fst (invℝ₊ z) ≤ᵣ fromNat (suc (suc Z)))
   (≤z⁻¹ : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst (invℝ₊ z)) →
   BDL.preLn (fst (invℝ₊ z) , snd (invℝ₊ z)) Z z⁻¹≤ ≤z⁻¹ ≡
     -ᵣ BDL.preLn (fst z , snd z) Z z≤ ≤z
 BDL-preLn-inv-components z Z z≤ ≤z z⁻¹≤ ≤z⁻¹ =
   expPreDer.preLn-inv Z z z≤ ≤z z⁻¹≤ ≤z⁻¹

opaque
 BDL-preLn-inv-components-with : ∀ x (p : 0 <ᵣ x) Z
   (x≤ : x ≤ᵣ fromNat (suc (suc Z)))
   (≤x : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ x)
   (x⁻¹≤ : fst (invℝ₊ (x , p)) ≤ᵣ fromNat (suc (suc Z)))
   (≤x⁻¹ : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ
     fst (invℝ₊ (x , p))) →
   BDL.preLn
       (fst (invℝ₊ (x , p)) , snd (invℝ₊ (x , p)))
       Z x⁻¹≤ ≤x⁻¹ ≡
     -ᵣ BDL.preLn (x , p) Z x≤ ≤x
 BDL-preLn-inv-components-with x p Z x≤ ≤x x⁻¹≤ ≤x⁻¹ =
   expPreDer.preLn-inv Z (x , p) x≤ ≤x x⁻¹≤ ≤x⁻¹

opaque
 BDL-preLn-one : ∀ Z →
   let one₊ : ℝ₊
       one₊ = fromNat 1
   in (p : 0 <ᵣ fst one₊) →
      (one≤ : fst one₊ ≤ᵣ fromNat (suc (suc Z))) →
      (≤one : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst one₊) →
      BDL.preLn (fst one₊ , p) Z one≤ ≤one ≡ 0
 BDL-preLn-one Z p one≤ ≤one i =
   (preLn-path ∙ zero-path) i
  where
  module F = BDL (fst (fromNat 1) , p) Z one≤ ≤one
  module G = BDL 1 Z one≤ ≤one

  one-path : Path ℝ₊ (fst (fromNat 1) , p) 1
  one-path = ℝ₊≡ refl

  left-cauchy-path : PathP
    (λ i → IsCauchySequence' (lnSeq (one-path i)))
    F.ca-lnSeq
    (transport
      (λ i → IsCauchySequence' (lnSeq (one-path i)))
      F.ca-lnSeq)
  left-cauchy-path = toPathP refl

  right-cauchy-path : PathP
    (λ i → IsCauchySequence' (lnSeq (one-path i)))
    (transport
      (λ i → IsCauchySequence' (lnSeq (one-path (~ i))))
      G.ca-lnSeq)
    G.ca-lnSeq
  right-cauchy-path = symP (toPathP refl)

  preLn-path : F.preLn ≡ G.preLn
  preLn-path i = fromCauchySequence'-≡-lem (lnSeq (one-path i))
    (left-cauchy-path i) (right-cauchy-path i) i

  zero-path : G.preLn ≡ 0
  zero-path = sym (expPreDer.0=preLn Z one≤ ≤one)



seq-^-intervals : Seq⊆
seq-^-intervals .Seq⊆.𝕡 Z = intervalℙ (rat [ 1 / (fromNat (suc (suc Z))) ]) (fromNat (suc (suc Z)))

seq-^-intervals .Seq⊆.𝕡⊆ Z x (≤x , x≤) =
  isTrans≤ᵣ _ _ _  (≤ℚ→≤ᵣ _ _
    (ℚ.invℚ₊≤invℚ₊
      (fromNat (suc (suc (suc Z))))
      (fromNat (suc (suc Z)))
      w)) ≤x
  , isTrans≤ᵣ _ _ _ x≤ (≤ℚ→≤ᵣ _ _ w)

 where
 w = (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc (ℕ.≤-refl {suc (suc Z)}))))

seq-^-intervals∈Pos : seq-^-intervals Seq⊆.s⊇ pred0<
seq-^-intervals∈Pos x 0<x =
  PT.map2 (λ (1+ n , N) (1+ n' , N') →
        ℕ.max n n'
            ,
              fst (invℝ₊-≤-invℝ₊ (x , 0<x) (_ , <ℚ→<ᵣ _ _ (0<pos _ _)))
              (isTrans≤ᵣ _ _ _
               (isTrans≤ᵣ _ _ _                 (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ N'))
               (isTrans≤≡ᵣ _ _ _
                 (((≤ℚ→≤ᵣ (fromNat (suc n')) (fromNat (suc (suc (ℕ.max n n'))))
                      ((≤ℤ→≤ℚ _ _
                       (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.suc-≤-suc (ℕ.≤-suc (ℕ.right-≤-max {n'} {n})))))))))
                        (sym (invℝ₊-rat _))))

              ,
                isTrans≤ᵣ _ _ _
             (isTrans≤ᵣ _ _ _
                 (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ N))

                 (((≤ℚ→≤ᵣ (fromNat (suc n)) _
                      (≤ℤ→≤ℚ _ _ (ℤ.ℕ≤→pos-≤-pos _ _ (ℕ.≤-suc $ ℕ.suc-≤-suc (ℕ.left-≤-max {n} {n'})))))))

               )
    (getClamps x) (getClamps (fst (invℝ₊ (x , 0<x))))



-- -- -- -- -- -- -- FnWith

private
 opaque
  seq-^-fun : (x : ℝ) (0<x : 0 <ᵣ x) (Z : ℕ)
    → x ≤ᵣ fromNat (suc (suc Z))
    → rat [ 1 / (fromNat (suc (suc Z))) ] ≤ᵣ x
    → (ℝ → ℝ₊) × ℝ
  seq-^-fun x 0<x Z x≤ ≤x = F.𝒇₊ , F.preLn
   where
   module F = BDL (x , 0<x) Z x≤ ≤x

 opaque
  unfolding seq-^-fun
  seq-^-fun-formula : ∀ x 0<x Z x≤ ≤x →
    seq-^-fun x 0<x Z x≤ ≤x ≡
      (let module F = BDL (x , 0<x) Z x≤ ≤x
       in F.𝒇₊ , F.preLn)
  seq-^-fun-formula x 0<x Z x≤ ≤x = refl

 seq-^-raw : ∀ x Z → x ∈ Seq⊆.𝕡 seq-^-intervals Z
   → (ℝ → ℝ₊) × ℝ
 seq-^-raw x Z (≤x , x≤) =
  seq-^-fun x
    (isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x)
    Z x≤ ≤x

 seq-^-raw⊆ : ∀ x n m
   (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals n)
   (x∈' : x ∈ Seq⊆.𝕡 seq-^-intervals m)
   → n ℕ.< m → seq-^-raw x n x∈ ≡ seq-^-raw x m x∈'
 seq-^-raw⊆ x n m (≤x , x≤) (≤x' , x≤') n<m =
  pair-path

  where
  0<x : 0 <ᵣ x
  0<x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x
  0<x' : 0 <ᵣ x
  0<x' = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x'
  xp : 0<x ≡ 0<x'
  xp = isProp<ᵣ 0 x 0<x 0<x'

  module F = BDL (x , 0<x) n x≤ ≤x
  module F' = BDL (x , 0<x') m x≤' ≤x'

  rat-agreement : ∀ r → F.BL.𝒇 (rat r) ≡ F'.BL.𝒇 (rat r)
  rat-agreement r =
    F.BL.𝒇-rat r
    ∙ cong (λ base → fst (base ^ℚ r))
        (ℝ₊≡ {x = (x , 0<x)} {y = (x , 0<x')} refl)
    ∙ sym (F'.BL.𝒇-rat r)

  function-agreement : ∀ t → F.BL.𝒇 t ≡ F'.BL.𝒇 t
  function-agreement = ≡Continuous F.BL.𝒇 F'.BL.𝒇
    F.BL.𝒇-cont F'.BL.𝒇-cont rat-agreement

  positive-function-path : F.𝒇₊ ≡ F'.𝒇₊
  positive-function-path = funExt λ t → ℝ₊≡ (function-agreement t)

  icP : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i)))
          F.ca-lnSeq
          (transport (λ i → IsCauchySequence' (lnSeq (x , xp i))) F.ca-lnSeq)
  icP = toPathP refl

  icP' : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i)))
           (transport (λ i → IsCauchySequence' (lnSeq (x , xp (~ i)))) F'.ca-lnSeq)
           F'.ca-lnSeq
  icP' = symP (toPathP refl)

  preLn-path : F.preLn ≡ F'.preLn
  preLn-path i = fromCauchySequence'-≡-lem (lnSeq (x , xp i))
    (icP i) (icP' i) i

  component-path : Path ((ℝ → ℝ₊) × ℝ)
    (F.𝒇₊ , F.preLn) (F'.𝒇₊ , F'.preLn)
  component-path i = positive-function-path i , preLn-path i

  pair-path : Path ((ℝ → ℝ₊) × ℝ)
    (seq-^-fun x 0<x n x≤ ≤x)
    (seq-^-fun x 0<x' m x≤' ≤x')
  pair-path = seq-^-fun-formula x 0<x n x≤ ≤x
    ∙ component-path
    ∙ sym (seq-^-fun-formula x 0<x' m x≤' ≤x')

Seq-^ : Seq⊆→ ((ℝ → ℝ₊) × ℝ) seq-^-intervals
Seq-^ .Seq⊆→.fun = seq-^-raw
Seq-^ .Seq⊆→.fun⊆ = seq-^-raw⊆

opaque
 Seq-^-fun≡BDL : ∀ x Z
   (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z) →
   Seq⊆→.fun Seq-^ x Z x∈ ≡
     (BDL.𝒇₊
        (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
        Z (snd x∈) (fst x∈)
     , BDL.preLn
        (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
        Z (snd x∈) (fst x∈))
 Seq-^-fun≡BDL x Z (≤x , x≤) =
   seq-^-fun-formula x
     (isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x)
     Z x≤ ≤x

 Seq-^-fun-fst≡BDL : ∀ x Z
   (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z) →
   Seq⊆→.fun Seq-^ x Z x∈ .fst ≡
     BDL.𝒇₊
       (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
       Z (snd x∈) (fst x∈)
 Seq-^-fun-fst≡BDL x Z x∈ = cong
   (λ (g : (ℝ → ℝ₊) × ℝ) → fst g)
   (Seq-^-fun≡BDL x Z x∈)

 Seq-^-fun-snd≡BDL : ∀ x Z
   (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z) →
   Seq⊆→.fun Seq-^ x Z x∈ .snd ≡
     BDL.preLn
       (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
       Z (snd x∈) (fst x∈)
 Seq-^-fun-snd≡BDL x Z x∈ = cong
   (λ (g : (ℝ → ℝ₊) × ℝ) → snd g)
   (Seq-^-fun≡BDL x Z x∈)

 Seq-^-fun-snd≡BDL-with : ∀ x Z
   (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z)
   (p : 0 <ᵣ x) →
   Seq⊆→.fun Seq-^ x Z x∈ .snd ≡
     BDL.preLn (x , p) Z (snd x∈) (fst x∈)
 Seq-^-fun-snd≡BDL-with x Z x∈ p =
   Seq-^-fun-snd≡BDL x Z x∈
   ∙ BDL-preLn-positive-path x
       (isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
       p Z (snd x∈) (fst x∈)

opaque
 Seq-^-fun-snd≡preLn-with : ∀ x Z
   (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z)
   (p : 0 <ᵣ x) →
   Seq⊆→.fun Seq-^ x Z x∈ .snd ≡
     expPreDer.expPreDer'.preLn Z
       (x , p) (snd x∈) (fst x∈)
 Seq-^-fun-snd≡preLn-with x Z x∈ p =
   Seq-^-fun-snd≡BDL-with x Z x∈ p

opaque
 Seq-^-fun-snd≡BDL-at : ∀ (z : ℝ₊) Z
   (z∈ : fst z ∈ Seq⊆.𝕡 seq-^-intervals Z) →
   Seq⊆→.fun Seq-^ (fst z) Z z∈ .snd ≡
     BDL.preLn z Z (snd z∈) (fst z∈)
 Seq-^-fun-snd≡BDL-at (x , p) Z x∈ =
   Seq-^-fun-snd≡BDL-with x Z x∈ p

module Seq-^-FI = Seq⊆→.FromIntersection Seq-^
   (isSet× (isSet→ isSetℝ₊) isSetℝ) pred0< seq-^-intervals∈Pos
