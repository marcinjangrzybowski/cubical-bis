{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.RealPower where

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


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisection
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceElementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; stepℚ₊; fromSucℚ₊
  ; posStepWidth; negStepWidth)
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequence

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
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerBase public

module BDL (z : ℝ₊) (Z : ℕ)
          (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
          (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
          -- (1+1/Z<z : rat (1 ℚ.+ [ 1 / 1+ (suc Z) ]) ≤ᵣ fst z )
           where

 opaque
  unfolding _+ᵣ_
  bdl' : (z : ℝ₊) (Z : ℕ)
           (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
           (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
           → 1 ≤ᵣ fst z → boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
  bdl' z Z z≤Z 1/Z≤z 1≤z n = ℚ.elimBy≡⊎<'
   (λ x y X y∈ x∈ → subst2 _≤ᵣ_
        (minusComm-absᵣ _ _)
        (cong (rat ∘ (fst (slUpBd Z n) ℚ.·_)) (ℚO.abs-Comm _ _))
        (X x∈ y∈)  )
   (λ x _ _ → subst2 _≤ᵣ_
      (cong absᵣ (sym (+-ᵣ _)))
      (cong rat (sym (Rℚ.0RightAnnihilates' _ _ (cong abs (ℚ.+InvR x)))))
      (≡ᵣWeaken≤ᵣ _ _ (absᵣ-rat 0))) -- (≤ᵣ-refl 0)
   λ y₀ h₊ y₀∈ y₁∈ →
    let
      y₁ = y₀ ℚ.+ fst h₊
      y₀<y₁ = ℚ≤→<+₊ y₀ y₀ h₊ (ℚ.isRefl≤ y₀)
    in isTrans≡≤ᵣ _ _ _ (absᵣNonNeg _ (x≤y→0≤y-x _ _
          (^ℚ-MonotoneR {z} y₀ y₁ (ℚ.<Weaken≤ y₀ y₁ y₀<y₁) 1≤z )))
      (isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _ (
     (fst (z/y≤x₊≃z≤y₊·x _ _ _) (slope-upper-bound z (fromSucℚ₊ n)
     y₀ y₁ y₀<y₁
      (absTo≤×≤ (fst (fromSucℚ₊ n)) y₀ y₀∈)
      (absTo≤×≤ (fst (fromSucℚ₊ n)) y₁ y₁∈))))
       (≤ᵣ-o· _ _ _ (ℚ.<Weaken≤ 0 _ (ℚ.-< _ _ y₀<y₁))
        (≤ᵣ₊Monotone·ᵣ _ _ _ _
          (<ᵣWeaken≤ᵣ _ _ $ snd (ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z)) ^ℚ fst (fromSucℚ₊ n)))
          (x≤y→0≤y-x _ _ 1≤z)
          (^ℚ-Monotone {y = ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))}
           (fromSucℚ₊ n) z≤Z)
          (isTrans≡≤ᵣ _ _ _ (cong (fst z +ᵣ_) (-ᵣ-rat 1)) (≤ᵣ-+o _ _ (-1) z≤Z)))))
       (·ᵣComm _ _ ∙
        cong₂ (_·ᵣ_)
          (cong₂ (_·ᵣ_) (^ⁿ-ℚ^ⁿ (suc n) [ pos (suc (suc Z)) / 1 ])
            (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℤ+→ℚ+ _ _))
           ∙ sym (rat·ᵣrat _ _) )
          (cong rat (sym (ℚO.0<→abs≡id _ (ℚ.-< _ _ y₀<y₁))))
         ∙ sym (rat·ᵣrat _ _)))


  bdl : boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
  bdl n x y x< y< = isTrans≡≤ᵣ _ _ _
     (cong (λ z → absᵣ
       (fst (z ^ℚ  y) -ᵣ fst (z ^ℚ x)))
       (ℝ₊≡ refl))
   (∈interval→≤ContPos'pred {x₀ = [ 1 / fromNat (suc (suc Z)) ]}
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
         (IsContinuousWP∘' _ _ _ IsContinuousAbsᵣ (IsContinuousWithPred⊆ pred0< _ _
          (λ z z∈ → isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _))
           (fst z∈))
          ((contDiagNE₂WP sumR _ _ _
         (⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ y))
            (IsContinuousWP∘' _ _ _ IsContinuous-ᵣ
              ((⊆IsContinuousWithPred _ _ (λ x 0<x → 0<x) _
           (IsContinuous^ℚ x))))))))
         ((AsContinuousWithPred _ _ (IsContinuousConst
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
          Z u≤ ≤u (≤ℚ→≤ᵣ _ _ 1≤u) n x y x< y<

       wwwR : u ℚ.≤ 1 →
                absᵣ (fst (u₊ ^ℚ y) -ᵣ fst (u₊ ^ℚ x))
               ≤ᵣ rat (fst (slUpBd Z n) ℚ.· abs (y ℚ.- x))
       wwwR u≤1 = subst2 _≤ᵣ_
              (cong absᵣ (cong₂ _-ᵣ_ (cong fst (sym (^ℚ-minus _ _)))
                                     (cong fst (sym (^ℚ-minus _ _)))))
               (cong (λ uu → rat (fst (slUpBd Z n) ℚ.· uu))
                 (cong abs (sym ℚ!) ∙ ℚO.abs-Comm _ _))
            wwwR'
        where
         wwwR' : absᵣ (fst ((invℝ₊ u₊) ^ℚ (ℚ.- y)) -ᵣ fst ((invℝ₊ u₊) ^ℚ (ℚ.- x)))
                ≤ᵣ rat (fst (slUpBd Z n) ℚ.· abs ((ℚ.- y) ℚ.- (ℚ.- x)))
         wwwR' = bdl' (invℝ₊ u₊) Z
          (isTrans≤≡ᵣ _ _ _
            (invEq (invℝ₊-≤-invℝ₊ u₊ (ℚ₊→ℝ₊ (stepℚ₊ Z))) ≤u)
            (invℝ₊-rat (stepℚ₊ Z))  )
          (isTrans≡≤ᵣ _ _ _
            (sym (invℝ₊-rat (fromSucℚ₊ (suc Z))))
            (invEq (invℝ₊-≤-invℝ₊ (ℚ₊→ℝ₊ (fromSucℚ₊ (suc Z))) u₊) u≤))
          (isTrans≡≤ᵣ _ _ _ (sym (invℝ₊-rat _)) (invEq (invℝ₊-≤-invℝ₊ 1 u₊)
            (≤ℚ→≤ᵣ _ _ u≤1)))

          n (ℚ.- x) (ℚ.- y)
           (subst (ℚ._≤ (fromNat (suc n))) (ℚ.-abs x) x<)
           (subst (ℚ._≤ (fromNat (suc n))) (ℚ.-abs y) y<)

 open BoundedLipsch (fst ∘ z ^ℚ_) (slUpBd Z) bdl public

-- --  bdlInv-lem : ( fst (fromNat (suc (suc Z))
-- --                    ^ℚ -2)) ≤ᵣ ((fst z -ᵣ 1) ／ᵣ₊ z)
-- --  bdlInv-lem = isTrans≡≤ᵣ _ _ _
-- --    (cong fst (^ℚ-minus' _ 2 ∙ sym (^ℚ-+ _ 1 1)) ∙
-- --     cong₂ _·ᵣ_ (
-- --         cong fst (^ℚ-1 (invℝ₊ (fromNat (suc (suc Z)))))
-- --       ∙ cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)
-- --      ∙ invℝ₊-rat (fromNat (suc (suc Z))))
-- --         (cong fst (^ℚ-1 (invℝ₊ (fromNat (suc (suc Z)))))
-- --       ∙ cong (fst ∘ invℝ₊) (fromNatℝ≡fromNatℚ _)) )
-- --    (≤ᵣ₊Monotone·ᵣ (rat _) _ _ _
-- --     (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))
-- --     (<ᵣWeaken≤ᵣ _ _ $
-- --      snd (invℝ₊ (ℚ₊→ℝ₊ ([ pos (suc (suc Z)) , 1 ] , tt)))) (
-- --     <ᵣWeaken≤ᵣ _ _
-- --      (a+c<b⇒a<b-c _ _ _
-- --        (isTrans≡<ᵣ _ _ _ (+ᵣComm (rat [ 1 / 1+ (suc Z) ]) 1) 1+1/Z<z)))
-- --      (invEq (invℝ₊-≤-invℝ₊ (ℚ₊→ℝ₊ _) _) (<ᵣWeaken≤ᵣ _ _ z<Z)))

-- --  bdlInv : boundedInvLipschitz slUpBdInv
-- --  bdlInv n = ℚ.elimBy≡⊎<
-- --   (λ x y X y∈ x∈ → subst2 _≤ᵣ_
-- --        (cong rat (ℚO.abs-Comm _ _))
-- --        (cong (rat (fst (slUpBdInv n)) ·ᵣ_) (minusComm-absᵣ _ _))
-- --        (X x∈ y∈)  )
-- --   ((λ x _ _ → subst2 _≤ᵣ_
-- --      (cong rat (sym (cong ℚ.abs (ℚ.+InvR x))))
-- --      (sym (Rℝ.0RightAnnihilates' _ _ (cong absᵣ (+-ᵣ _))))
-- --      (≤ᵣ-refl 0)))
-- --   λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
-- --    subst2 _≤ᵣ_
-- --      (cong rat (sym (ℚO.0<→abs≡id _ (ℚ.-< _ _ y₀<y₁))))
-- --      (cong (rat (fst (slUpBdInv n)) ·ᵣ_)
-- --       (sym (absᵣNonNeg _ (x≤y→0≤y-x _ _
-- --          (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) (<ᵣWeaken≤ᵣ _ _ 1<z) )))))
-- --      (isTrans≡≤ᵣ _ _ _ (sym (·IdR _))
-- --       (fst (z/y'≤x/y≃y₊·z≤y'₊·x _ _ (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _ y₀<y₁))
-- --             (ℚ₊→ℝ₊ (slUpBdInv n)))
-- --         (isTrans≡≤ᵣ _ _ _ (·IdL _)
-- --          (isTrans≤ᵣ _ _ _
-- --            (isTrans≡≤ᵣ _ _ _
-- --              (invℝ₊-rat _ ∙ cong fst (
-- --                ( (sym (^ℤ-rat (fromNat (suc (suc Z)))
-- --                    (ℤ.negsuc (1 ℕ.+ suc n)))
-- --                    ∙ cong (_^ℚ [ ℤ.negsuc (1 ℕ.+ suc n) / 1 ])
-- --                     (ℝ₊≡ refl))
-- --            ∙ cong (fromNat (suc (suc Z)) ^ℚ_)
-- --             (cong [_/ 1 ] (ℤ.negsuc+ _ _) ∙ sym (ℚ.ℤ+→ℚ+ _ _)))
-- --                ∙ sym (^ℚ-+ _ _ _)) ∙ ·ᵣComm _ _)
-- --              (≤ᵣ₊Monotone·ᵣ
-- --                (fst (fromNat (suc (suc Z))
-- --                    ^ℚ (ℚ.- [ pos (suc n) , (1+ 0) ])))
-- --                _
-- --                _
-- --                _
-- --                (<ᵣWeaken≤ᵣ _ _
-- --                  $ snd (z ^ℚ (ℚ.- [ pos (suc n) , (1+ 0) ])))
-- --                (<ᵣWeaken≤ᵣ _ _
-- --                  $ snd (fromNat (fromNat (suc (suc Z))) ^ℚ -2))
-- --                (subst2 _≤ᵣ_
-- --                  (cong fst (sym (^ℚ-minus' _ _)))
-- --                  (cong fst (sym (^ℚ-minus' _ _)))
-- --                  (^ℚ-Monotone (fromNat (suc n))
-- --                   (invEq (invℝ₊-≤-invℝ₊ _ _)
-- --                    (<ᵣWeaken≤ᵣ _ _ z<Z))))
-- --                bdlInv-lem))
-- --           (<ᵣWeaken≤ᵣ _ _
-- --            (slope-lower-bound z (fromNat (suc n)) 1<z
-- --             _ _ y₀<y₁
-- --             (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
-- --             (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))
-- --      )))))

-- --  open BoundedInvLipsch slUpBdInv bdlInv public

 mid-𝒇 : ∀ q q' q'' → q ℚ.≤ q' → q' ℚ.≤ q'' →
    minᵣ (𝒇 (rat q))
         (𝒇 (rat q'')) ≤ᵣ 𝒇 (rat q')
 mid-𝒇 q q' q'' q≤q' q'≤q'' =
   subst2 _≤ᵣ_
     (cong₂ minᵣ (sym (𝒇-rat q)) (sym (𝒇-rat q'')))
     (sym (𝒇-rat q'))
     (monotone^ℚ q q' q'' q≤q' q'≤q'' _)

 opaque
  unfolding minᵣ maxᵣ
  0<𝒇 : ∀ x → 0 <ᵣ 𝒇 x
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
                                 (sym (𝒇-rat _)) (sym (𝒇-rat _))))
                              zzz
                in isTrans≡<ᵣ _ _ _ (sym (Rℝ.+InvR _)) (a-b<c⇒a-c<b _ _ _
                      (isTrans≤<ᵣ _ _ _ (≤absᵣ _)
                     (isTrans<ᵣ _ _ _ |fx-fr|<ε zzz')))
               ) (∃rationalApprox≤ x (δ /2₊)))

          (𝒇-cont x (ε , <ᵣ→<ℚ _ _ 0<ε))
          )
       (denseℚinℝ 0 _ (snd q⊓q')) )
    (∃rationalApprox x 1)

 𝒇₊ : ℝ → ℝ₊
 𝒇₊ x = 𝒇 x , 0<𝒇 x

 opaque
  unfolding minᵣ maxᵣ
  flₙ≡𝒇 : ∀ x n → (x ∈ intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
            →  fst (fst (flₙ n)) x ≡ 𝒇 x
  flₙ≡𝒇 x n x∈ = ≡Continuous (fst (fst (flₙ n)))
            (𝒇 ∘ clampᵣ (fromNeg (suc n)) (fromNat (suc n)))
      (snd (flₙ n)) (IsContinuous∘ _ _ 𝒇-cont
           (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n))))
        (λ r → flₙ-rat n r
          ∙ sym (𝒇-rat (ℚ.clamp (clampL n) (clampU n) r))
          ∙ cong 𝒇 (sym (clampᵣ-rat (clampL n) (clampU n) r)))
        x
    ∙ cong 𝒇 (sym (∈ℚintervalℙ→clampᵣ≡ _ _ x x∈))


  𝒇-monotone : 1 ≤ᵣ fst z → ∀ x y → x ≤ᵣ y → 𝒇 x ≤ᵣ 𝒇 y
  𝒇-monotone 1≤z x y x≤y =
   ≡→≤ᵣ ((≡Cont₂ (cont₂∘ (contNE₂ maxR) 𝒇-cont 𝒇-cont)
     (cont∘₂ 𝒇-cont (contNE₂ maxR) )
     (ℚ.elimBy≤
        (λ u u' X → maxᵣComm _ _ ∙∙ X ∙∙ cong 𝒇 (maxᵣComm (rat u) (rat u')))
        λ u u' u≤u' →
          cong₂ maxᵣ (𝒇-rat u) (𝒇-rat u')
           ∙∙ ≤ᵣ→≡ (^ℚ-MonotoneR u u' u≤u' 1≤z) ∙
            cong (fst ∘ (z ^ℚ_)) (sym (ℚ.≤→max u u' u≤u')) ∙∙
           (sym (𝒇-rat (ℚ.max u u')) ∙ cong 𝒇 (sym (maxᵣ-rat u u'))))
         x y)
    ∙ cong 𝒇 (≤ᵣ→≡ x≤y))


 opaque
  unfolding _<ᵣ_
  𝒇-monotone-str : 1 <ᵣ fst z → ∀ x y → x <ᵣ y → 𝒇 x <ᵣ 𝒇 y
  𝒇-monotone-str 1<z x y = PT.rec (isProp<ᵣ _ _)
     λ ((q , q') , (≤q , q<q' , q'≤)) →
       isTrans≤<ᵣ _ _ _ (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) x (rat q) ≤q)
         (isTrans<≤ᵣ _ _ _ (
            subst2 _<ᵣ_ (sym (𝒇-rat _)) (sym (𝒇-rat _))
             (^ℚ-StrictMonotoneR 1<z q q' q<q'))
           (𝒇-monotone (<ᵣWeaken≤ᵣ _ _ 1<z) (rat q') y q'≤))

 module _ (n : ℕ) where


  incr^ : 1 <ᵣ fst z → isIncrasingℙᵣ
            (intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
            (λ x _ → fst (fst (flₙ n)) x)
  incr^ 1<z x x∈ y y∈ x<y =
    subst2 _<ᵣ_
      (sym (flₙ≡𝒇 x n x∈))
      (sym (flₙ≡𝒇 y n y∈))
      (𝒇-monotone-str 1<z  x y x<y)


  nondecr^ : 1 ≤ᵣ fst z → isNondecrasingℙᵣ
      (intervalℙ (fromNeg (suc n)) (fromNat (suc n)))
      (λ x _ → fst (fst (flₙ n)) x)
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
  𝒇-diffQuot r r＃0 = (𝒇 r -ᵣ 𝒇 0) ／ᵣ[ r , r＃0 ]

  𝒇-diffQuot-cont : IsContinuousWithPred 0＃ₚ 𝒇-diffQuot
  𝒇-diffQuot-cont =
    cont₂·ᵣWP 0＃ₚ
      (λ r _ → 𝒇 r -ᵣ 𝒇 0)
      invℝ
      (AsContinuousWithPred 0＃ₚ
        (λ r → 𝒇 r -ᵣ 𝒇 0)
        (IsContinuous∘ _ _ (IsContinuous+ᵣR (-ᵣ 𝒇 0)) 𝒇-cont))
      IsContinuousWithPredInvℝ

  𝒇-diffQuot≤lnSeq : ∀ n r (0＃r : 0 ＃ r)
    → r ≤ᵣ rat [ 1 / 2+ n ]
    → 𝒇-diffQuot r 0＃r ≤ᵣ lnSeq z n
  𝒇-diffQuot≤lnSeq n =
    ≤ContWP＃≤ [ 1 / 2+ n ] (0<pos 0 (2+ n))
      𝒇-diffQuot-cont
      (AsContinuousWithPred _ _ (IsContinuousConst (lnSeq z n)))
      (λ u u∈ u≤ →
        subst2 _≤ᵣ_
          (cong₂ _·ᵣ_
            (cong₂ _-ᵣ_
              (sym (𝒇-rat u))
              (sym (𝒇-rat 0)))
            (cong₂ invℝ
              (Rℝ.+IdR' _ _ (-ᵣ-rat 0))
              (toPathP (isProp＃ _ _ _ _))))
          (cong₂ _·ᵣ_
            refl
            (invℝ₊-rat (posStepWidth n)
              ∙ cong rat
                  (cong (fst ∘ invℚ₊)
                    (ℚ₊≡ {x = posStepWidth n}
                      {y = stepℚ₊ n}
                      (ℚ.+IdR _)))))
          (slope-monotone＃ z 0 u
            0 [ 1 / 2+ n ]
            u∈ (0<pos 0 _) (ℚ.isRefl≤ 0) u≤))

  lnSeq'≤𝒇-diffQuot : ∀ n r (0＃r : 0 ＃ r)
    → rat (ℚ.- [ 1 / 2+ n ]) ≤ᵣ r
    → lnSeq' z n ≤ᵣ 𝒇-diffQuot r 0＃r
  lnSeq'≤𝒇-diffQuot n =
    ≤ContWP＃≤' (ℚ.- [ 1 / 2+ n ])
      (ℚ.minus-< 0 [ 1 / 2+ n ] (0<pos 0 (2+ n)))
      (AsContinuousWithPred _ _ (IsContinuousConst (lnSeq' z n)))
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
                      (ℚ.+IdL _ ∙ ℚ.-Invol _)))))
          (sym (-ᵣ·-ᵣ _ _)
            ∙ cong₂ _·ᵣ_
                (-[x-y]≡y-x _ _
                  ∙ cong₂ _-ᵣ_
                      (sym (𝒇-rat u))
                      (sym (𝒇-rat 0)))
                (-invℝ _ _
                  ∙ cong₂ invℝ
                      (cong -ᵣ_ (+IdL _) ∙ -ᵣInvol _)
                      (toPathP (isProp＃ _ _ _ _))))
          (slope-monotone＃' z
            (ℚ.- [ 1 / 2+ n ]) 0 u 0
            (ℚ.minus-< 0 [ 1 / 2+ n ] (0<pos 0 (2+ n)))
            (isSym＃ _ _ u∈) u≤ (ℚ.isRefl≤ 0)))

  {-
  Old quotient-slope derivative proof. Previous names:
  expDerAt0, differenceAt𝒇-Δ, expDerA.

  expDerAt0 : derivativeOf 𝒇 at 0 is preLn
  expDerAt0 ε =
   PT.rec
     squash₁
     (λ (ε' , 0<ε' , <ε) →
       let ε'₊ = (ε' , <ᵣ→<ℚ _ _ 0<ε')
           N = fst (seqΔ-δ Z ε'₊)
           X =  seqΔ ε'₊
      in  ∣ ℚ₊→ℝ₊ ([ 1 / 2+ (suc N) ] , 0<pos 0 (2+ (suc N))) ,
              (λ r 0＃r ∣r∣<1/N →
                let d≤lnSeq : differenceAt 𝒇 0 r 0＃r ≤ᵣ lnSeq z (suc N)
                    d≤lnSeq = ≤ContWP＃≤ [ 1 / 2+ suc N ] (0<pos 0 (2+ (suc N)))
                              (IsContinuousWithPred-differenceAt 0 _ 𝒇-cont)
                              ((AsContinuousWithPred _ _
                               (IsContinuousConst (lnSeq z (suc N)))))
                              (λ u u∈ u≤ →
                                subst2 _≤ᵣ_
                                 ((cong₂ _·ᵣ_ (cong₂ _-ᵣ_
                              (cong (fst ∘ (z ^ℚ_)) (sym (ℚ.+IdL u))
                                ∙ sym (𝒇-rat (0 ℚ.+ u))
                                ∙ cong 𝒇 (sym (+ᵣ-rat 0 u)))
                              (sym (𝒇-rat _)))
                                 ((cong₂ invℝ (Rℝ.+IdR' _ _ (-ᵣ-rat 0)) (toPathP (isProp＃ _ _ _ _))))))
                                 (cong₂ _·ᵣ_
                                   refl ((invℝ₊-rat (posStepWidth (suc N)) ∙ cong rat
                               (cong (fst ∘ invℚ₊)
                                 (ℚ₊≡ {x = posStepWidth (suc N)}
                                   {y = stepℚ₊ (suc N)}
                                   (ℚ.+IdR _))))))
                                 ( (slope-monotone＃ ((z)) 0 u
                                   0 [ 1 / 2+ (suc N) ]
                                   u∈ (0<pos 0 _) (ℚ.isRefl≤ 0) u≤))

                                   )
                              r 0＃r
                              (isTrans≤ᵣ _ _ _ (≤absᵣ r)
                                 (isTrans≡≤ᵣ _ _ _ (cong absᵣ (sym (Rℝ.+IdR' _ _ (-ᵣ-rat 0)))
                                  ∙ minusComm-absᵣ _ _) (<ᵣWeaken≤ᵣ (absᵣ (0 -ᵣ r)) _ ∣r∣<1/N)))


                    lnSeq'≤d : lnSeq' z (suc N) ≤ᵣ differenceAt 𝒇 0 r 0＃r
                    lnSeq'≤d = ≤ContWP＃≤' (ℚ.- [ 1 / 2+ suc N ])
                                   ((ℚ.minus-< 0 [ 1 / 2+ suc N ] (0<pos 0 (2+ (suc N)))))
                               ((AsContinuousWithPred _ _
                               (IsContinuousConst (lnSeq' z (suc N)))))
                               (IsContinuousWithPred-differenceAt 0 _ 𝒇-cont)
                                (λ u u∈ u≤ → subst2 _≤ᵣ_
                                   ((cong₂ _·ᵣ_ refl ((invℝ₊-rat (negStepWidth (suc N)) ∙ cong rat
                                     (cong (fst ∘ invℚ₊)
                                       (ℚ₊≡
                                         {x = negStepWidth (suc N)}
                                         {y = stepℚ₊ (suc N)}
                                         (ℚ.+IdL _ ∙ ℚ.-Invol _)))))))
                                   (sym (-ᵣ·-ᵣ _ _) ∙ cong₂ _·ᵣ_
                                     (-[x-y]≡y-x _ _ ∙
                                       cong₂ _-ᵣ_ (sym (𝒇-rat _) ∙ cong 𝒇 (sym (+IdL _)))
                                         (sym (𝒇-rat _)))
                                     (-invℝ _ _ ∙ cong₂ invℝ (cong -ᵣ_ (+IdL _) ∙ -ᵣInvol _)
                                       (toPathP (isProp＃ _ _ _ _))))

                                   (slope-monotone＃' z
                                     (ℚ.- [ 1 / 2+ (suc N) ]) 0 u 0
                                     ((ℚ.minus-< 0 [ 1 / 2+ suc N ] (0<pos 0 (2+ (suc N)))))
                                     (isSym＃ _ _ u∈) u≤ (ℚ.isRefl≤ 0))
                                     )
                                r 0＃r
                              (isTrans≤ᵣ _ _ _
                                (isTrans≡≤ᵣ _ _ _
                                 (sym (-ᵣ-rat _))
                                 (-ᵣ≤ᵣ _ _ (<ᵣWeaken≤ᵣ (absᵣ (0 -ᵣ r)) _ ∣r∣<1/N)))
                                (≤ᵣ-ᵣ _ _ (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ r))
                                  (cong absᵣ (sym (+IdL _)) ∙ sym (-ᵣInvol _)))))


                in isTrans≤<ᵣ _ _ _
                     (intervalℙ→dist< _ _ _ _
                        ((lnSeq'≤preLn _) , (preLn≤lnSeq _))
                        (lnSeq'≤d , d≤lnSeq))
                     (isTrans<ᵣ _ _ _ (X (suc N) ℕ.≤-refl) <ε)

                 ) ∣₁ )
     (denseℚinℝ 0 _ (snd ε))
  -}

  𝒇· : ∀ x y → 𝒇 x ·ᵣ 𝒇 y ≡ 𝒇 (x +ᵣ y)
  𝒇· = ≡Cont₂
       (cont₂∘ IsContinuous₂·ᵣ 𝒇-cont 𝒇-cont )
       (cont∘₂ 𝒇-cont (contNE₂ sumR))
       λ u u' → cong₂ _·ᵣ_ (𝒇-rat u) (𝒇-rat u')
          ∙ cong fst (^ℚ-+ _ _ _)
          ∙ sym (𝒇-rat (u ℚ.+ u'))
          ∙ cong 𝒇 (sym (+ᵣ-rat u u'))

 {-
 Previous names: differenceAt𝒇-Δ, expDerA.

 differenceAt𝒇-Δ : ∀ x r 0＃r → 𝒇 x ·ᵣ differenceAt 𝒇 0 r 0＃r ≡ (differenceAt 𝒇 x r 0＃r)
 differenceAt𝒇-Δ x r 0＃r = ·ᵣAssoc _ _ _ ∙
   cong (_／ᵣ[ r , 0＃r ]) (Rℝ.·DistR- _ _ _ ∙
     cong₂ _-ᵣ_
       (𝒇· _ (0 +ᵣ r) ∙ cong 𝒇 (cong (x +ᵣ_) (+IdL r)))
       (𝒇· _ _ ∙ cong 𝒇 (+IdR x)))


 expDerA : ∀ x → derivativeOf 𝒇 at x is (𝒇 x ·ᵣ preLn)
 expDerA x =
 subst (at (rat [ pos zero / 1+ zero ]) limitOf_is (𝒇 x ·ᵣ preLn))
   (funExt₂ λ r 0＃r → differenceAt𝒇-Δ _ _ _ )
   (·-lim _ _ _ _ _ (const-lim (𝒇 x) 0) expDerAt0)
 -}


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


Seq-^ : Seq⊆→ ((ℝ → ℝ₊) × ℝ) seq-^-intervals
Seq-^ .Seq⊆→.fun x Z (≤x , x≤) = F.𝒇₊ , F.preLn
 where
 module F = BDL (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x) Z x≤ ≤x
Seq-^ .Seq⊆→.fun⊆ x n m (≤x , x≤) (≤x' , x≤') n<m = cong₂ _,_
  (funExt (ℝ₊≡ ∘ (≡Continuous _ _ F.𝒇-cont F'.𝒇-cont
       λ r → F.𝒇-rat r ∙∙ cong (fst ∘ (_^ℚ r)) (ℝ₊≡ refl) ∙∙ sym (F'.𝒇-rat r))))
        λ i → fromCauchySequence'-≡-lem (lnSeq (x , xp i))
              (icP i) (icP' i) i

 where
 module F = BDL _ n x≤ ≤x
 module F' = BDL _ m x≤' ≤x'

 0<x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x
 0<x' = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x'
 xp : 0<x ≡ 0<x'
 xp = isProp<ᵣ 0 x 0<x 0<x'

 icP : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i)))
         F.ca-lnSeq
         (transport (λ i → IsCauchySequence' (lnSeq (x , xp i))) F.ca-lnSeq)
 icP = toPathP refl

 icP' : PathP (λ i → IsCauchySequence' (lnSeq (x , xp i)))
          (transport (λ i → IsCauchySequence' (lnSeq (x , xp (~ i)))) F'.ca-lnSeq)
          F'.ca-lnSeq
 icP' = symP (toPathP refl)








module Seq-^-FI = Seq⊆→.FromIntersection Seq-^
   (isSet× (isSet→ isSetℝ₊) isSetℝ) pred0< seq-^-intervals∈Pos
