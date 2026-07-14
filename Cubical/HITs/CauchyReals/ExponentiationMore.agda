module Cubical.HITs.CauchyReals.ExponentiationMore where

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

module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.InverseLipschitz.Base
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
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; fromSucℚ₊)
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
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower

module Pos^ where
 open Seq-^-FI


 ^-c : ∀ x → 0 <ᵣ x  → ℝ → ℝ₊
 ^-c x 0<x = fst (∩$ x 0<x)

 _^ᵣ_ : ℝ₊ → ℝ → ℝ₊
 (x , 0<x) ^ᵣ y = fst (∩$ x 0<x) y

 private
  opaque
   realPower≡intersection : ∀ x y →
     x ^ᵣ y ≡ fst (∩$ (fst x) (snd x)) y
   realPower≡intersection (x , 0<x) y = refl

  opaque
   rationalPower-stable : ℝ₊ → ℚ → ℝ
   rationalPower-stable x q = fst (x ^ℚ q)

  opaque
   unfolding rationalPower-stable
   rationalPower-stable≡rationalPower : ∀ x q →
     rationalPower-stable x q ≡ fst (x ^ℚ q)
   rationalPower-stable≡rationalPower x q = refl


 ^ᵣ-mon-str : ∀ x
   → 1 <ᵣ fst x
   → ∀ y y'
   → y <ᵣ y'
   → fst (x ^ᵣ y) <ᵣ fst (x ^ᵣ y')
 ^ᵣ-mon-str x 1<x y y'  y<y' =
  ∩$-elimProp (fst x) (snd x)
    {λ (f , _) → fst (f y) <ᵣ fst (f y')}
    (λ _ → isProp<ᵣ _ _)
    (λ n x∈ₙ →
      let 0<x = isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc n)) ]) (fst x)
            (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc n)) ]
              (0<pos 0 (fromNat (suc (suc n)))))
            (fst x∈ₙ)
          fun-path = Seq-^-fun≡BDL (fst x) n x∈ₙ
      in subst2 _<ᵣ_
          (sym (cong (λ (g : (ℝ → ℝ₊) × ℝ) → fst (fst g y)) fun-path))
          (sym (cong (λ (g : (ℝ → ℝ₊) × ℝ) → fst (fst g y')) fun-path))
          (BDL.𝒇-monotone-str (fst x , 0<x)
            n (snd x∈ₙ) (fst x∈ₙ) 1<x y y' y<y'))

 ln-c : ∀ x → 0 <ᵣ x → ℝ
 ln-c x 0<x = snd (∩$ x 0<x)

 ln : ℝ₊ → ℝ
 ln (x , 0<x) = snd (∩$ x 0<x)

 private
  opaque
   ln-stable : ℝ₊ → ℝ
   ln-stable z = ln z

  opaque
   unfolding ln-stable
   ln-stable≡ln : ∀ z → ln-stable z ≡ ln z
   ln-stable≡ln z = refl

  opaque
   ln≡intersection : ∀ x (0<x : 0 <ᵣ x) →
     ln (x , 0<x) ≡ snd (∩$ x 0<x)
   ln≡intersection x 0<x = refl

 ln-1≡0 : ln 1 ≡ 0
 ln-1≡0 =
   let 1r : ℝ₊
       1r = fromNat 1
   in ∩$-elimProp (fst 1r) (snd 1r)
             {λ (_ , lnx) → lnx ≡ 0}
             (λ _ → isSetℝ _ _)
             λ Z x∈ →
               let 0<1 : 0 <ᵣ fst 1r
                   0<1 = isTrans<≤ᵣ _ _ _
                     (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈)
                   seq-path : Seq⊆→.fun Seq-^ (fst 1r) Z x∈ .snd ≡
                     BDL.preLn (fst 1r , 0<1) Z (snd x∈) (fst x∈)
                   seq-path = cong (λ (g : (ℝ → ℝ₊) × ℝ) → snd g)
                     (Seq-^-fun≡BDL (fst 1r) Z x∈)
                   zero-path :
                     BDL.preLn (fst 1r , 0<1) Z (snd x∈) (fst x∈) ≡ 0
                   zero-path = BDL-preLn-one Z 0<1 (snd x∈) (fst x∈)
               in seq-path ∙ zero-path

 ln-cont : IsContinuousWithPred pred0< (curry ln)
 ln-cont x ε 0<x = w
  where
  ww : (Z : ℕ) (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z) →
        ∃-syntax ℚ₊
        (λ δ →
           (v : ℝ) (v∈P : 0 <ᵣ v) →
           x ∼[ δ ] v →
           Seq⊆→.fun Seq-^ x Z x∈ .snd ∼[ ε ] curry ln-stable v v∈P)
  ww Z x∈ =
    let (N , X) = seqΔ-δ (suc Z) (ε /4₊)
        uuu = seq-^-intervals .Seq⊆.𝕡⊆ Z x x∈
        δZ : ℚ₊
        δZ = ℚ.<→ℚ₊ [ 1 / fromNat (suc (suc (suc Z))) ] [ 1 / fromNat (suc (suc Z)) ]
              (fst (ℚ.invℚ₊-<-invℚ₊ (fromNat (suc (suc Z))) (fromNat (suc (suc (suc Z)))))
                (<ℤ→<ℚ _ _ (ℤ.ℕ<→pos-<-pos _ _ ℕ.≤-refl)))
    in PT.map
        (λ (δ , D) →
          min₊ δ δZ ,
            (λ v v∈P x∼v →
                let ca' = expPreDer.expPreDer'.preLn∼ (suc Z)
                    uvu = isTrans≡≤ᵣ (rat [ pos 1 / 2+ suc Z ]) _ _
                           (cong rat ℚ! ∙
                              sym (-ᵣ-rat₂ [ 1 / fromNat (suc (suc Z)) ] (fst δZ)))
                           (≤ᵣMonotone+ᵣ _ _ _ _
                          (fst x∈) (-ᵣ≤ᵣ _ _ (isTrans≤ᵣ _ _ _ (isTrans≤ᵣ _ _ _
                            (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                                   x∼v))) (≤ℚ→≤ᵣ _ _
                                     (ℚ.min≤' (fst δ) (fst δZ))))))
                    uuuV : v ∈ seq-^-intervals .Seq⊆.𝕡 (suc Z)
                    uuuV = isTrans≤≡ᵣ _ _ _ uvu ℝ!
                        , (isTrans≤≡ᵣ _ _ _
                            (isTrans≤ᵣ _ _ _
                             (a-b≤c⇒a≤c+b _ _ _
                               (isTrans≤ᵣ _ _ _ (≤absᵣ _)
                                (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                                   (sym∼ _ _ _ x∼v)))
                                    (≤ℚ→≤ᵣ _ _
                                      (ℚ.isTrans≤ _ _ _
                                       (ℚ.min≤' (fst δ) (fst δZ))
                                       (≤-ℚ₊ [ 1 / fromNat (suc (suc Z)) ]
                                        1 ([ 1 / fromNat (suc (suc (suc Z))) ] ,
                                           0<pos 0 (fromNat (suc (suc (suc Z)))))
                                         (ℚ.invℚ₊≤invℚ₊ (fromNat (suc (suc Z))) 1
                                           (≤ℤ→≤ℚ _ _
                                              (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                                                (ℕ.suc-≤-suc ℕ.zero-≤))))))))))
                             (≤ᵣ-o+ _ _ 1 (snd x∈)))
                            (+ᵣ-rat _ _ ∙ cong rat
                              (ℚ.ℕ+→ℚ+ 1 (suc (suc Z)))))
                    ≡ε :
                      fst (((ε /4₊) +₊ (ε /2₊)) +₊ (ε /4₊)) ≡ fst ε
                    ≡ε = ℚ!
                    0<x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst uuu)
                    0<v = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst uuuV)
                    qqq : BDL.preLn (x , 0<x) (suc Z) (snd uuu) (fst uuu)
                           ∼[ ((ε /4₊) +₊ (ε /2₊)) +₊ (ε /4₊) ]
                           BDL.preLn (v , 0<v) (suc Z) (snd uuuV) (fst uuuV)
                    qqq = (triangle∼ (triangle∼ (sym∼ _ _ _
                              (ca' (x , 0<x) (snd uuu) (fst uuu)
                                (suc N) (ε /4₊) ℕ.≤-refl))
                          ((D v 0<v
                             (∼-monotone≤
                               (ℚ.min≤ (fst δ) (fst δZ)) x∼v))))
                           (ca' (v , 0<v) (snd uuuV) (fst uuuV)
                             (suc N) (ε /4₊) ℕ.≤-refl))
                    seq-x-path = Seq-^-fun-snd≡BDL-with x (suc Z) uuu 0<x
                    seq-v-path = Seq-^-fun-snd≡BDL-with v (suc Z) uuuV 0<v
                    qqq-seq =
                      ((sym seq-x-path) subst∼[ refl ] (sym seq-v-path)) qqq
                in ((cong snd (2c x (suc Z) Z uuu _))
                     subst∼[ ℚ₊≡ ≡ε ]
                       (cong snd (sym (∩$-∈ₙ v v∈P (suc Z) uuuV))
                         ∙ sym (ln-stable≡ln (v , v∈P)))
                       )
                       qqq-seq))
        (lnSeqCont (suc N) x (ε /2₊) _)

  w-intersection : ∃-syntax ℚ₊
        (λ δ → (v : ℝ) (v∈P : 0 <ᵣ v) →
          x ∼[ δ ] v →
          snd (∩$ x 0<x) ∼[ ε ] curry ln-stable v v∈P)
  w-intersection = ∩$-elimProp x 0<x
    {λ (_ , lnx) → ∃-syntax ℚ₊
      (λ δ → (v : ℝ) (v∈P : 0 <ᵣ v) →
        x ∼[ δ ] v → lnx ∼[ ε ] curry ln-stable v v∈P)}
    (λ _ → squash₁)
    ww

  w : ∃-syntax ℚ₊
        (λ δ → (v : ℝ) (v∈P : 0 <ᵣ v) →
          x ∼[ δ ] v → curry ln x 0<x ∼[ ε ] curry ln v v∈P)
  w = PT.map
    (λ (δ , D) → δ , λ v v∈P x∼v →
      ((sym (ln≡intersection x 0<x)) subst∼[ refl ]
        (ln-stable≡ln (v , v∈P)))
        (D v v∈P x∼v))
    w-intersection



 opaque
  ^-rat-intersection : ∀ x y →
    fst (fst (∩$ (fst x) (snd x)) (rat y)) ≡
      rationalPower-stable x y
  ^-rat-intersection x =
   ∩$-elimProp (fst x) (snd x)
     {λ (f , _) → ∀ y →
      fst (f (rat y)) ≡ rationalPower-stable x y}
     (λ _ → isPropΠ λ _ → isSetℝ _ _)
     (λ n x∈ q →
       let 0<x : 0 <ᵣ fst x
           0<x = isTrans<≤ᵣ _ _ _
             (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈)
           fun-path : Seq⊆→.fun Seq-^ (fst x) n x∈ .fst ≡
             BDL.𝒇₊ (fst x , 0<x) n (snd x∈) (fst x∈)
           fun-path = Seq-^-fun-fst≡BDL (fst x) n x∈
           seq-rat-path :
             fst (Seq⊆→.fun Seq-^ (fst x) n x∈ .fst (rat q)) ≡
             fst (BDL.𝒇₊ (fst x , 0<x) n
               (snd x∈) (fst x∈) (rat q))
           seq-rat-path = cong (λ (f : ℝ → ℝ₊) → fst (f (rat q))) fun-path
           bdl-rat-path :
             fst (BDL.𝒇₊ (fst x , 0<x) n
               (snd x∈) (fst x∈) (rat q)) ≡
             fst ((fst x , 0<x) ^ℚ q)
           bdl-rat-path =
             BDL.𝒇-rat (fst x , 0<x) n (snd x∈) (fst x∈) q
           base-path : fst ((fst x , 0<x) ^ℚ q) ≡ fst (x ^ℚ q)
           base-path = cong (λ z → fst (z ^ℚ q))
             (ℝ₊≡ {x = (fst x , 0<x)} {y = x} refl)
           stable-path : fst (x ^ℚ q) ≡ rationalPower-stable x q
           stable-path = sym (rationalPower-stable≡rationalPower x q)
       in seq-rat-path ∙ bdl-rat-path ∙ base-path ∙ stable-path)

 ^-rat : ∀ x y → fst (x ^ᵣ (rat y)) ≡ fst (x ^ℚ y)
 ^-rat x y =
   cong fst (realPower≡intersection x (rat y))
   ∙ ^-rat-intersection x y
   ∙ rationalPower-stable≡rationalPower x y


 opaque
  ln-inv-intersection : ∀ x (0<x : 0 <ᵣ x) →
    let x⁻¹ = invℝ₊ (x , 0<x)
    in snd (∩$ (fst x⁻¹) (snd x⁻¹)) ≡ -ᵣ snd (∩$ x 0<x)
  ln-inv-intersection x 0<x =
    ∩$-elimProp2
      (fst (invℝ₊ (x , 0<x))) (snd (invℝ₊ (x , 0<x))) x 0<x
      {λ (_ , ln-x⁻¹) (_ , ln-x) → ln-x⁻¹ ≡ -ᵣ ln-x}
      (λ _ _ → isSetℝ _ _)
      (λ Z x⁻¹∈ x∈ →
        let seq-inv-path = Seq-^-fun-snd≡BDL-at
              (invℝ₊ (x , 0<x)) Z x⁻¹∈
            preLn-path = BDL-preLn-inv-components-with x 0<x Z
              (snd x∈) (fst x∈) (snd x⁻¹∈) (fst x⁻¹∈)
            seq-x-path : Seq⊆→.fun Seq-^ x Z x∈ .snd ≡
              BDL.preLn (x , 0<x) Z (snd x∈) (fst x∈)
            seq-x-path = Seq-^-fun-snd≡BDL-at (x , 0<x) Z x∈
            end-path : -ᵣ BDL.preLn (x , 0<x) Z (snd x∈) (fst x∈) ≡
              -ᵣ Seq⊆→.fun Seq-^ x Z x∈ .snd
            end-path = cong (-ᵣ_) (sym seq-x-path)
        in subst2 _≡_ (sym seq-inv-path) end-path preLn-path)

 ln-inv : ∀ x → ln (invℝ₊ x) ≡ -ᵣ (ln x)
 ln-inv (x , 0<x) =
   let x⁻¹ = invℝ₊ (x , 0<x)
       left-path = ln≡intersection (fst x⁻¹) (snd x⁻¹)
       right-path = cong (-ᵣ_) (sym (ln≡intersection x 0<x))
   in subst2 _≡_ (sym left-path) right-path
        (ln-inv-intersection x 0<x)

 opaque
  cont-^-intersection : ∀ (x : ℝ₊) →
    IsContinuous (fst ∘ fst (∩$ (fst x) (snd x)))
  cont-^-intersection (x , 0<x) =
    ∩$-elimProp x 0<x  {λ (f , _) → IsContinuous (fst ∘ f)}
      (λ _ → isPropIsContinuous _)
      λ Z x∈ →
        let fun-path = Seq-^-fun-fst≡BDL x Z x∈
            real-fun-path = cong
              (λ (f : ℝ → ℝ₊) → fst ∘ f)
              fun-path
            bdl-cont = BDL-fun₊-cont
              (x , isTrans<≤ᵣ _ _ _
                (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
              Z (snd x∈) (fst x∈)
        in subst IsContinuous (sym real-fun-path) bdl-cont

 cont-^ : ∀ (x : ℝ₊) → IsContinuous (fst ∘ x ^ᵣ_)
 cont-^ x =
   let fun-path : (fst ∘ x ^ᵣ_) ≡
         (fst ∘ fst (∩$ (fst x) (snd x)))
       fun-path = funExt λ y → cong fst (realPower≡intersection x y)
   in subst IsContinuous (sym fun-path) (cont-^-intersection x)



 ^ᵣ0 : ∀ x → fst (x ^ᵣ 0) ≡ 1
 ^ᵣ0 x = ^-rat x 0

 ^ᵣ1 : ∀ x → fst (x ^ᵣ 1) ≡ fst x
 ^ᵣ1 x = ^-rat x 1 ∙ ^ⁿ-1 _

 ^ᵣ[1/n] : ∀ x n₊ → fst (x ^ᵣ rat [ 1 / n₊ ]) ≡ fst (root n₊ x)
 ^ᵣ[1/n] x n₊ =  ^-rat x [ 1 / n₊ ] ∙ ^ⁿ-1 _

 opaque
  positive-ln-intersection : ∀ a (0<a : 0 <ᵣ a) →
    1 <ᵣ a → 0 <ᵣ snd (∩$ a 0<a)
  positive-ln-intersection a 0<a 1<a =
    ∩$-elimProp a 0<a
             {λ (_ , lna) → 0 <ᵣ lna}
               (λ _ → isProp<ᵣ _ _)
               λ Z a∈ →
                 let stage-path = Seq-^-fun-snd≡BDL-at (a , 0<a) Z a∈
                     positive = BDL.0<preLn
                       (a , 0<a) Z (snd a∈) (fst a∈) 1<a
                 in subst (0 <ᵣ_) (sym stage-path) positive

 1<a→0<ln[a] : ∀ a → (1 <ᵣ fst a) → 0 <ᵣ ln a
 1<a→0<ln[a] (a , 0<a) 1<a =
   subst (0 <ᵣ_) (sym (ln≡intersection a 0<a))
     (positive-ln-intersection a 0<a 1<a)

 opaque
  ^ᵣ+-intersection : ∀ x (0<x : 0 <ᵣ x) y y' →
    fst (∩$ x 0<x) (y +ᵣ y') ≡
      fst (∩$ x 0<x) y ₊·ᵣ fst (∩$ x 0<x) y'
  ^ᵣ+-intersection x 0<x y y' =
    ∩$-elimProp x 0<x
      {λ (f , _) → f (y +ᵣ y') ≡ f y ₊·ᵣ f y'}
      (λ _ → isSetℝ₊ _ _)
      λ n x∈ →
        let
          fun-path = Seq-^-fun-fst≡BDL x n x∈
          bdl-path :
            BDL.𝒇₊
                (x , isTrans<≤ᵣ _ _ _
                  (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
                n (snd x∈) (fst x∈) (y +ᵣ y') ≡
              BDL.𝒇₊
                  (x , isTrans<≤ᵣ _ _ _
                    (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
                  n (snd x∈) (fst x∈) y
                ₊·ᵣ
              BDL.𝒇₊
                  (x , isTrans<≤ᵣ _ _ _
                    (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
                  n (snd x∈) (fst x∈) y'
          bdl-path = ℝ₊≡ (sym (BDL.𝒇·
            (x , isTrans<≤ᵣ _ _ _
              (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst x∈))
            n (snd x∈) (fst x∈) y y'))
          left-path = cong (λ (f : ℝ → ℝ₊) → f (y +ᵣ y'))
            (sym fun-path)
          right-path = cong₂ _₊·ᵣ_
            (cong (λ (f : ℝ → ℝ₊) → f y) (sym fun-path))
            (cong (λ (f : ℝ → ℝ₊) → f y') (sym fun-path))
        in subst2 _≡_ left-path right-path bdl-path

 ^ᵣ+ : ∀ x y y' → x ^ᵣ (y +ᵣ y') ≡ (x ^ᵣ y) ₊·ᵣ (x ^ᵣ y')
 ^ᵣ+ x y y' =
   let left-path = sym (realPower≡intersection x (y +ᵣ y'))
       right-path = cong₂ _₊·ᵣ_
         (sym (realPower≡intersection x y))
         (sym (realPower≡intersection x y'))
   in subst2 _≡_ left-path right-path
        (^ᵣ+-intersection (fst x) (snd x) y y')

open Pos^ public


rootₙ→1 : ∀ x (α : ℝ) → 1 <ᵣ α →
         ∃[ N ∈ ℕ ]
           (∀ n → N ℕ.< n → fst (root (1+ n) x) <ᵣ α)
rootₙ→1 x α 1<α =
  PT.rec squash₁ w
    (IsContinuousLim _ 0 (cont-^ x) (α -ᵣ 1 , x<y→0<y-x _ _ 1<α))
 where
 w : Σ ℝ₊
      (λ δ →
         (r : ℝ) (x＃r : 0 ＃ r) →
         absᵣ (0 -ᵣ r) <ᵣ fst δ →
         absᵣ (fst (x ^ᵣ 0) -ᵣ fst (x ^ᵣ r))
         <ᵣ α -ᵣ 1) →
      ∃ ℕ (λ N → (n : ℕ) → N ℕ.< n → fst (root (1+ n) x) <ᵣ α)
 w ((δᵣ , 0<δᵣ) , X) =
    PT.map
      (λ (δ , 0<δ , δ<δᵣ) →
        let 1/δ = (invℚ₊ (δ , <ᵣ→<ℚ _ _ 0<δ))
            ((1+ k) , Y) = ℚ.boundℕ (fst 1/δ)
        in suc k , λ n <n →
            <-+o-cancel _ _ (-ᵣ 1)
              (isTrans≤<ᵣ _ _ _
                (≤absᵣ _) (isTrans≡<ᵣ _ _ _
               (cong absᵣ (cong₂ _-ᵣ_
                (sym (^ᵣ[1/n] x (1+ n)))
                (sym (^ᵣ0 x)))
                ∙ minusComm-absᵣ _ _) (X (rat [ 1 / 1+ n ])
            (inl (<ℚ→<ᵣ _ _ (0<pos _ _)))
             (isTrans≡<ᵣ _ _ _ (
              cong absᵣ (+IdL _) ∙ sym (-absᵣ _)
                ∙ absᵣPos _ (<ℚ→<ᵣ _ _ (0<pos _ _))) (isTrans<ᵣ _ _ _
              (<ℚ→<ᵣ [ 1 / 1+ n ] δ
                (subst2 ℚ._<_
                  refl
                  (ℚ.invℚ₊-invol _)
                  (fst (ℚ.invℚ₊-<-invℚ₊ 1/δ (fromNat (suc n)) )
                   (ℚ.isTrans< _ _ _
                     (ℚ.isTrans≤< _ _ _ (≤abs (fst 1/δ)) Y)
                     (<ℤ→<ℚ _ _ (ℤ.ℕ<→pos-<-pos _ _ (ℕ.≤-suc <n))))))) δ<δᵣ)))))
        )
      (denseℚinℝ 0 δᵣ 0<δᵣ)

opaque
 unfolding maxᵣ
 ℚ-clamp-<-cases : ∀ L L' x y → L ℚ.< L' → x ℚ.< y →
                     (ℚ.clamp L L' x ≡ ℚ.clamp L L' y) ⊎
                        (ℚ.clamp L L' x ℚ.< ℚ.clamp L L' y)
 ℚ-clamp-<-cases L L' x y L<L' x<y =
   let clamp≤ = ℚ.≤MonotoneClamp L L' x y
         (ℚ.<Weaken≤ x y x<y)
   in ⊎.rec
        (λ reverse-clamp≤ → inl
          (ℚ.isAntisym≤
            (ℚ.clamp L L' x) (ℚ.clamp L L' y)
            clamp≤ reverse-clamp≤))
        inr
        (ℚ.Dichotomyℚ (ℚ.clamp L L' y) (ℚ.clamp L L' x))

 ℚ-clamp-<-casesᵣ : ∀ L L' x y → L ℚ.< L' →  x ℚ.< y →
                     (clampᵣ (rat L) (rat L') (rat x)
                       ≡ clampᵣ (rat L) (rat L') (rat y)) ⊎
                        (clampᵣ (rat L) (rat L') (rat x)
                         <ᵣ clampᵣ (rat L) (rat L') (rat y))
 ℚ-clamp-<-casesᵣ L L' x y L<L' x<y =
  (⊎.map
     (λ p → clampᵣ-rat L L' x ∙ cong rat p ∙ sym (clampᵣ-rat L L' y))
     (λ p → subst2 _<ᵣ_
       (sym (clampᵣ-rat L L' x))
       (sym (clampᵣ-rat L L' y))
       (<ℚ→<ᵣ _ _ p))
     (ℚ-clamp-<-cases L L' x y L<L' x<y))

eventually-lnSeq[x]<lnSeq'[x+Δ] : ∀ (x Δ : ℝ₊) → 1 <ᵣ fst x →
  ∃[ k ∈ ℕ ] lnSeq x k <ᵣ lnSeq' (x ₊+ᵣ Δ) k
eventually-lnSeq[x]<lnSeq'[x+Δ] x Δ 1<x =
   PT.map w
     (rootₙ→1 x α 1<α)

 where


 0<1-1/[x+Δ] = (isTrans<≡ᵣ _ _ _
          (invEq (invℝ₊-<-invℝ₊ _ 1)
            (isTrans≡<ᵣ _ _ _
              (sym (+IdR _))
              (<ᵣMonotone+ᵣ _ _ _ _ 1<x (snd Δ)))) (cong fst invℝ₊1) )


 0<1-1/x = (isTrans<≡ᵣ _ _ _
          (invEq (invℝ₊-<-invℝ₊ _ 1)
            (isTrans≡<ᵣ _ _ _
              (sym (+IdR _) ∙ (+ᵣ-rat _ _))
              1<x)) (cong fst invℝ₊1) )


 α : ℝ
 α = (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
      ／ᵣ₊ (_ , x<y→0<y-x _ _ 0<1-1/x)

 1<α : 1 <ᵣ α
 1<α = invEq (1<x/y≃y<x _ _)
   (<ᵣ-o+ _ _ 1
     (-ᵣ<ᵣ _ _ (invEq (invℝ₊-<-invℝ₊ _ _)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _))
         (<ᵣ-o+ _ _ (fst x) (snd Δ))))))



 w : Σ ℕ
      (λ N → (n : ℕ) → N ℕ.< n → fst (root (1+ n) x) <ᵣ α) →
      Σ ℕ (λ k → lnSeq x k <ᵣ lnSeq' (x ₊+ᵣ Δ) k)
 w (K , X) =
   K , <ᵣ-·ᵣo _ _ (_ , <ℚ→<ᵣ _ _ (0<pos _ _))
     (isTrans<≤ᵣ _ _ _
       (isTrans≡<ᵣ _ _ _
         (cong₂ _-ᵣ_
           (^ⁿ-1 (fst (root (1+ suc K) x))
             ∙ sym (·IdLᵣ (fst (root (1+ suc K) x))))
           (cong fst
             (sym (ₙ√1 (1+ suc K))
             ∙∙ cong (root (1+ suc K))
               (ℝ₊≡
                 (sym (x·invℝ₊[x] x)
                 ∙ ·ᵣComm (fst x) (fst (invℝ₊ x))))
             ∙∙ sym (·DistRoot (invℝ₊ x) x (1+ suc K))))
           ∙ sym (Rℝ.·DistL-
             1 (fst (root (1+ suc K) (invℝ₊ x)))
             (fst (root (1+ suc K) x))))
         (<ᵣ-o·ᵣ _ _
           (_ , x<y→0<y-x (fst (root (1+ (suc K)) (invℝ₊ x))) 1
              (isTrans<≡ᵣ _ _ _
               (ₙ√-StrictMonotone {invℝ₊ x} {1}  (1+ suc K)
                 (invEq (1/x<1≃1<x x) 1<x))
               (cong fst (ₙ√1 (1+ suc K)))))
           (X (suc K) (ℕ.≤-refl {suc K}))))
       from-concave)

  where

  from-concave :
    (1 -ᵣ fst (root (2+ K) (invℝ₊ x))) ·ᵣ α ≤ᵣ
     1 -ᵣ fst ((x ₊+ᵣ Δ) ^ℚ (ℚ.- [ 1 / 2+ K ]))
  from-concave = isTrans≡≤ᵣ (_ ·ᵣ α) _ _
        (cong₂ (_·ᵣ_)
           (cong₂ _-ᵣ_
             (cong fst (sym (ₙ√1 (1+ suc K)))) refl)
           (·ᵣComm
             (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
             (fst (invℝ₊
               (1 -ᵣ fst (invℝ₊ x) ,
                x<y→0<y-x _ _ 0<1-1/x))))
         ∙ ·ᵣAssoc
             (fst (root (1+ suc K) 1)
               -ᵣ fst (root (1+ suc K) (invℝ₊ x)))
             (fst (invℝ₊
               (1 -ᵣ fst (invℝ₊ x) ,
                x<y→0<y-x _ _ 0<1-1/x)))
             (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ)))
         ∙ ·ᵣComm
             ((fst (root (1+ suc K) 1)
                 -ᵣ fst (root (1+ suc K) (invℝ₊ x)))
               ·ᵣ fst (invℝ₊
                 (1 -ᵣ fst (invℝ₊ x) ,
                  x<y→0<y-x _ _ 0<1-1/x)))
             (1 -ᵣ fst (invℝ₊ (x ₊+ᵣ Δ))))
        (isTrans≤≡ᵣ _ _ _ (fst (z≤x/y₊≃y₊·z≤x _ _ _) (slope-monotone-ₙ√ (suc K)
         (invℝ₊ (x ₊+ᵣ Δ)) 1
         (invℝ₊ x) 1
         0<1-1/[x+Δ]
         0<1-1/x
         (invEq (invℝ₊-≤-invℝ₊ _ _)
           (isTrans≡≤ᵣ _ _ _ (sym (+IdR _))
            (≤ᵣ-o+ _ _ (fst x) (<ᵣWeaken≤ᵣ _ _ (snd Δ)))))
            (≤ᵣ-refl 1)))
            (cong₂ _-ᵣ_
              (cong fst (ₙ√1 (1+ suc K)))
              (sym (^ⁿ-1
                (fst (root (1+ suc K) (invℝ₊ (x ₊+ᵣ Δ)))))
              ∙ cong fst
                (sym (^ℚ-minus'
                  (x ₊+ᵣ Δ) [ 1 / 2+ K ])))))




monotoneStrictPreLn : ∀ Z → (z z' : ℝ₊) → 1 <ᵣ fst z →
         (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
         (1/Z≤z :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
         (z'≤Z : fst z' ≤ᵣ fromNat (suc (suc Z)))
         (1/Z≤z' :  rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z')
         → fst z <ᵣ fst z'
         → expPreDer.expPreDer'.preLn Z z z≤Z 1/Z≤z  <ᵣ
           expPreDer.expPreDer'.preLn Z z' z'≤Z 1/Z≤z'
monotoneStrictPreLn Z z z' 1<z z≤Z 1/Z≤z z'≤Z 1/Z≤z' z<z' =
  PT.rec (isProp<ᵣ _ _)
    (λ (K , X) →
       isTrans<≤ᵣ _ _ _
         (isTrans≤<ᵣ _ _ _
           (BDL.preLn≤lnSeq z Z z≤Z 1/Z≤z K) X)

         ((isTrans≡≤ᵣ _ _ _
          (cong (λ zz → lnSeq' zz K) (ℝ₊≡ ℝ!) )
          (BDL.lnSeq'≤preLn z' Z z'≤Z 1/Z≤z' K)))
          )
    (eventually-lnSeq[x]<lnSeq'[x+Δ]
      z (fst z' +ᵣ -ᵣ fst z , x<y→0<y-x _ _ z<z' )
      1<z)


ln-mon-str-1< :
   ∀ (y y' : ℝ₊)
   → 1 <ᵣ fst y
   → fst y <ᵣ fst y'
   → ln y <ᵣ ln y'
ln-mon-str-1< y y' 1<y y<y' =
  Seq-^-FI.∩$-elimProp2  (fst y) (snd y) (fst y') (snd y')
  {B = λ (_ , ln-y) (_ , ln-y') → ln-y <ᵣ ln-y'}
  (λ _ _ → isProp<ᵣ _ _)
  λ Z x∈ y∈ →
    let 0<y-stage =
          isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc Z)) ]) (fst y)
            (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst x∈)
        0<y'-stage =
          isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc Z)) ]) (fst y')
            (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst y∈)
        seq-y-path = Seq-^-fun-snd≡BDL-with
          (fst y) Z x∈ 0<y-stage
        seq-y'-path = Seq-^-fun-snd≡BDL-with
          (fst y') Z y∈ 0<y'-stage
        strict = monotoneStrictPreLn Z
          (fst y , 0<y-stage) (fst y' , 0<y'-stage)
          1<y (snd x∈) (fst x∈) (snd y∈) (fst y∈) y<y'
    in subst2 _<ᵣ_ (sym seq-y-path) (sym seq-y'-path) strict

private
 opaque
  rationalPower-after-realPower-cont : ∀ x q →
    IsContinuous (λ v → fst ((x ^ᵣ v) ^ℚ q))
  rationalPower-after-realPower-cont x q =
    let reconstructed : ℝ → ℝ
        reconstructed v =
          fst (((fst (x ^ᵣ v) , snd (x ^ᵣ v)) ^ℚ q))
        reconstructed-cont : IsContinuous reconstructed
        reconstructed-cont = IsContinuousWithPred∘IsContinuous
          pred0< (curry (fst ∘ (_^ℚ q))) (fst ∘ (x ^ᵣ_))
          (λ v → snd (x ^ᵣ v)) (IsContinuous^ℚ q) (cont-^ x)
        function-path : reconstructed ≡
          (λ v → fst ((x ^ᵣ v) ^ℚ q))
        function-path = funExt λ v → cong (λ z → fst (z ^ℚ q))
          (ℝ₊≡
            {x = (fst (x ^ᵣ v) , snd (x ^ᵣ v))}
            {y = x ^ᵣ v} refl)
    in subst IsContinuous function-path reconstructed-cont

realPowerMulExponent : (x : ℝ₊) (a b : ℝ) →
  fst ((x ^ᵣ a) ^ᵣ b) ≡ fst (x ^ᵣ (a ·ᵣ b))
realPowerMulExponent x a =
  ≡Continuous
    (fst ∘ ((x ^ᵣ a) ^ᵣ_))
    ((fst ∘ (x ^ᵣ_)) ∘ (a ·ᵣ_))
    (cont-^ (x ^ᵣ a))
    (IsContinuous∘ (fst ∘ (x ^ᵣ_)) (a ·ᵣ_)
      (cont-^ x) (IsContinuous·ᵣL a))
    λ b' →
      ^-rat (x ^ᵣ a) b'
      ∙ ≡Continuous
          (λ v → fst ((x ^ᵣ v) ^ℚ b'))
          ((fst ∘ (x ^ᵣ_)) ∘ (_·ᵣ rat b'))
          (rationalPower-after-realPower-cont x b')
          (IsContinuous∘ (fst ∘ (x ^ᵣ_)) (_·ᵣ rat b')
            (cont-^ x) (IsContinuous·ᵣR (rat b')))
          (λ a' →
            cong (λ z → fst (z ^ℚ b'))
              (ℝ₊≡ {x = x ^ᵣ rat a'} {y = x ^ℚ a'} (^-rat x a'))
            ∙ cong fst (^ℚ-· x a' b')
            ∙ sym (^-rat x (a' ℚ.· b'))
            ∙ cong (fst ∘ (x ^ᵣ_)) (rat·ᵣrat a' b'))
          a

opaque
  invLipPreLn : ∀ Z → ∃[ K ∈ ℚ₊ ]
                InverseLipschitz-ℝ→ℝℙ K
                 ((intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
                (fromNat (suc (suc Z)))))
                λ x (≤x , x≤) →
                  expPreDer.expPreDer'.preLn Z
                    (x , isTrans<≤ᵣ 0
                      (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
                      (<ℚ→<ᵣ [ pos 0 / 1 ]
                        [ pos 1 / fromNat (suc (suc Z)) ]
                        (0<pos 0 (fromNat (suc (suc Z))))) ≤x)
                   x≤ ≤x
  invLipPreLn Z =
     PT.map
       ww
       (denseℚinℝ _ _ (snd Kᵣ))

    where


     Z<SZ : fst (fromSucℚ₊ (suc Z)) ℚ.<
         fst (fromSucℚ₊ (suc (suc Z)))
     Z<SZ =
                  (<ℤ→<ℚ (pos (suc (suc Z))) (pos (suc (suc (suc Z))))
                  (ℤ.ℕ<→pos-<-pos _ _
                    (ℕ.≤-refl {(suc (suc (suc Z)))})))
     1<Z : [ pos 1 / 1+ 0 ] ℚ.< [ pos (suc (suc Z)) / 1+ 0 ]
     1<Z =
                  (<ℤ→<ℚ (pos (suc zero)) (pos (suc (suc Z)))
                  (ℤ.ℕ<→pos-<-pos _ _
                    (ℕ.suc-≤-suc (ℕ.suc-≤-suc ℕ.zero-≤))))

     [1/3+Z]≤[2+Z] : rat [ pos 1 / 2+ suc Z ] ≤ᵣ rat [ pos (suc (suc Z)) / 1+ 0 ]
     [1/3+Z]≤[2+Z] = isTrans≤ᵣ _ 1 _
       (≤ℚ→≤ᵣ _ _ (ℚ.invℚ₊≤invℚ₊ (fromSucℚ₊ (suc (suc Z))) 1
         ((ℚ.<Weaken≤ _ _
          (ℚ.isTrans< 1 (fst (fromSucℚ₊ (suc Z))) _ 1<Z (Z<SZ))))
         ))
       (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 1<Z))

     2+Z∈ : (fromNat (suc (suc Z))) ∈
              ((intervalℙ (rat [ 1 / fromNat (suc (suc (suc Z))) ])
                 (fromNat (suc (suc (suc Z))))))
     2+Z∈ = [1/3+Z]≤[2+Z] , (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ Z<SZ))


     3+Z∈ : rat ([ (pos (suc (suc (suc Z)))) / 1 ]) ∈
              ((intervalℙ (rat [ 1 / fromNat (suc (suc (suc Z))) ])
                 (fromNat (suc (suc (suc Z))))))
     3+Z∈ =
               (≤ℚ→≤ᵣ _ _
                  (ℚ.isTrans≤ _ 1 [ pos (suc (suc (suc Z))) / (1+ 0) ]
                    (ℚ.invℚ₊≤invℚ₊ (fromSucℚ₊ (suc (suc Z))) 1
                     ((≤ℤ→≤ℚ _ (pos _) (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                  (ℕ.suc-≤-suc ℕ.zero-≤)))))
                    ((≤ℤ→≤ℚ _ (pos (suc (suc (suc Z)))) (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                  (ℕ.suc-≤-suc ℕ.zero-≤)))))) , (≤ᵣ-refl _)



     SSSZℚ₊ SSZℚ₊ : ℚ₊
     SSSZℚ₊ = [ (pos (suc (suc (suc Z)))) / 1 ] , 0<pos (suc (suc Z)) 1
     SSZℚ₊ = [ (pos (suc (suc Z))) / 1 ] , 0<pos (suc Z) 1

     SSSZ₊ SSZ₊ : ℝ₊
     SSSZ₊ = ℚ₊→ℝ₊ SSSZℚ₊
     SSZ₊ = ℚ₊→ℝ₊ SSZℚ₊

     Kᵣ : ℝ₊
     Kᵣ =
           BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
            +ᵣ -ᵣ

            BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈)
            ,
            x<y→0<y-x
             (BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈))
             (BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈)
           (fst 3+Z∈))
             (monotoneStrictPreLn (suc Z)
               SSZ₊
               SSSZ₊
               (<ℚ→<ᵣ _ _ 1<Z)
               (snd 2+Z∈) (fst 2+Z∈)
               (snd 3+Z∈) (fst 3+Z∈)
               (<ℚ→<ᵣ _ _ Z<SZ))

     ww : Σ ℚ (λ q → (rat [ pos 0 / 1+ 0 ] <ᵣ rat q) × (rat q <ᵣ Kᵣ .fst)) →
           Σ ℚ₊
           (λ K →
              InverseLipschitz-ℝ→ℝℙ K
              (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
               (fromNat (suc (suc Z))))
              λ x (≤x , x≤) → expPreDer.expPreDer'.preLn Z
                    (x , isTrans<≤ᵣ 0
                      (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
                      (<ℚ→<ᵣ [ pos 0 / 1 ]
                        [ pos 1 / fromNat (suc (suc Z)) ]
                        (0<pos 0 (fromNat (suc (suc Z))))) ≤x)
                   x≤ ≤x)
     ww (K , 0<K , K<Kᵣ) = (invℚ₊ K₊) , zzz

      where
      K₊ : ℚ₊
      K₊ = (K , <ᵣ→<ℚ _ _ 0<K)
      zzz : InverseLipschitz-ℝ→ℝℙ (invℚ₊ K₊)
        (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
         (fromNat (suc (suc Z))))
        (λ x (≤x , x≤) → expPreDer.expPreDer'.preLn Z
          (x , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z))))) ≤x)
          x≤ ≤x)
      zzz u u∈ v v∈ ε lnU∼lnV =
        invEq (∼≃abs<ε u v (invℚ₊ K₊ ·₊ ε)) abs-bound-rat
       where
        u₊ v₊ : ℝ₊
        u₊ =
          u ,
          isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst u∈)
        v₊ =
          v ,
          isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst v∈)

        lnU lnV : ℝ
        lnU = expPreDer.expPreDer'.preLn Z
          (u , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst u∈))
          (snd u∈) (fst u∈)
        lnV = expPreDer.expPreDer'.preLn Z
          (v , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst v∈))
          (snd v∈) (fst v∈)




        clp : ℝ → ℝ
        clp = clampᵣ (rat [ 1 / (1+  (suc Z)) ])
                     (rat [ pos (suc (suc Z)) / 1 ])

        1/SSZ<SSZ : fst (invℚ₊ SSZℚ₊) ℚ.< fst SSZℚ₊
        1/SSZ<SSZ =
          ℚ.isTrans< _ 1 _
            (fst (ℚ.invℚ₊-<-invℚ₊ 1 SSZℚ₊) 1<Z)
            1<Z


        1/SSZ≤SSZ : rat (fst (invℚ₊ SSZℚ₊)) ≤ᵣ rat (fst SSZℚ₊)
        1/SSZ≤SSZ = ≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1/SSZ<SSZ)

        0<clp : ∀ x → 0 <ᵣ clp x
        0<clp x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _))
           (≤clampᵣ (rat [ 1 / (1+  (suc Z)) ]) _ x 1/SSZ≤SSZ)

        clpCount : IsContinuous clp
        clpCount = IsContinuousClamp
           (rat [ 1 / (1+  (suc Z)) ])
                     (rat [ pos (suc (suc Z)) / 1 ])

        lnX' : ℝ → ℝ
        lnX' x = ln (clp x , 0<clp x)

        lnX'ₙ : ∀ (x : ℝ₊) 0<x
                (x∈ : fst x ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                          (rat [ pos (suc (suc (suc Z))) / 1 ]))) →
                  ln x ≡ BDL.preLn
                           (fst x , 0<x) (suc Z) (snd x∈) (fst x∈)
        lnX'ₙ x 0<x x∈ =
          cong snd (Seq-^-FI.∩$-∈ₙ (fst x) (snd x) (suc Z) x∈)
          ∙ Seq-^-fun-snd≡BDL-with (fst x) (suc Z) x∈ 0<x

        clp≡ : ∀ u → u ∈ ((intervalℙ (rat [ 1 /  (1+ (suc Z)) ])
                 (rat [ pos (suc (suc Z)) / 1 ]))) → clp u ≡ u
        clp≡ u u∈ = sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)

        lnX'Cont : IsContinuous lnX'
        lnX'Cont = IsContinuousWithPred∘IsContinuous
         pred0< (curry ln) clp 0<clp
         ln-cont clpCount

        lnuv< : absᵣ (lnU -ᵣ lnV) <ᵣ rat (fst ε)
        lnuv< = fst (∼≃abs<ε lnU lnV ε) lnU∼lnV

        zzzz= : ∀ x y → clp (rat x) ≡ clp (rat y) →
         fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
         absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
        zzzz= x y p =
         ≡ᵣWeaken≤ᵣ
                   (fst Kᵣ ·ᵣ
                     absᵣ (clp (rat x) -ᵣ clp (rat y)))
                   (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
                   (Rℝ.0RightAnnihilates'
                     (fst Kᵣ)
                     (absᵣ (clp (rat x) -ᵣ clp (rat y)))
                     (cong absᵣ
                       (Rℝ.+InvR'
                         (clp (rat x)) (clp (rat y)) p)
                     ∙ absᵣ-rat 0)
                     ∙ sym (absᵣ-rat 0) ∙
                     cong absᵣ (sym (Rℝ.+InvR'
                       (lnX' (rat x)) (lnX' (rat y))
                       (ll))))

           where

           ll : ln (clp (rat x) , 0<clp (rat x))  ≡ ln (clp (rat y) , 0<clp (rat y))
           ll = cong ln
             (ℝ₊≡
               {x = (clp (rat x) , 0<clp (rat x))}
               {y = (clp (rat y) , 0<clp (rat y))} p)

        zzzz< : ∀ x y → clp (rat x) <ᵣ clp (rat y) →
         fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
         absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
        zzzz< x y x<y =
         isTrans≡≤ᵣ
           (fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)))
           (absᵣ (clp (rat x) -ᵣ clp (rat y)) ·ᵣ fst Kᵣ)
           (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
          (·ᵣComm
            (fst Kᵣ) (absᵣ (clp (rat x) -ᵣ clp (rat y))))
          (fst (z≤x/y₊≃y₊·z≤x
            (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
            (fst Kᵣ) abs-diff₊)
            (subst2 _≤ᵣ_
              fixed-slope-path log-slope-path zzWW))
           where

           hhA : pos (suc (suc Z)) ℤ.+negsuc Z ≡ pos 1
           hhA = sym (ℤStdP.pos- (suc (suc Z)) (suc Z)) ∙ hhNat Z
            where
            hhNat : ∀ Z → (suc (suc Z) ℤStd.ℕ- suc Z) ≡ pos 1
            hhNat zero = refl
            hhNat (suc Z) = hhNat Z

           hhhh : 1 ℤ.+ ℤ.predℤ (pos (suc (suc Z)) ℤ.+negsuc Z) ≡ pos 1
           hhhh = cong (1 ℤ.+_) (cong ℤ.predℤ hhA) ∙ refl

           SSZ≤SSSZ : [ pos (suc (suc Z)) / 1 ] ℚ.≤ [ pos (suc (suc (suc Z))) / 1 ]
           SSZ≤SSSZ = (ℚ.<Weaken≤ [ pos (suc (suc Z)) / 1 ] [ pos (suc (suc (suc Z))) / 1 ] Z<SZ)

           1/SSSZ≤1/SSZ : rat [ pos 1 / 2+ suc Z ] ≤ᵣ rat [ pos 1 / 2+ Z ]
           1/SSSZ≤1/SSZ = ≤ℚ→≤ᵣ _ _
            (ℚ.invℚ≤invℚ SSSZℚ₊ SSZℚ₊ SSZ≤SSSZ)

           x*∈ : clp (rat x) ∈  (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                          (rat [ pos (suc (suc (suc Z))) / 1 ]))
           x*∈ =
            let (≤x , x≤) = ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat x)))
            in isTrans≤ᵣ _ _ _ 1/SSSZ≤1/SSZ ≤x , isTrans≤ᵣ _ _ _ x≤
              (≤ℚ→≤ᵣ _ _ SSZ≤SSSZ)

           y*∈ : clp (rat y) ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                          (rat [ pos (suc (suc (suc Z))) / 1 ]))
           y*∈ =
            let (≤y , y≤) = ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat y)))
            in (isTrans≤ᵣ _ _ _ 1/SSSZ≤1/SSZ ≤y) ,
                 isTrans≤ᵣ _ _ _ y≤ ((≤ℚ→≤ᵣ _ _ SSZ≤SSSZ))



           zzWW :
             ((BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
               -ᵣ BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈))
               ／ᵣ₊ (fst SSSZ₊ -ᵣ fst SSZ₊ ,
                 x<y→0<y-x (fst SSZ₊) (fst SSSZ₊) (<ℚ→<ᵣ _ _ Z<SZ)))
             ≤ᵣ
             ((BDL.preLn (clp (rat y) , 0<clp (rat y)) (suc Z) (snd y*∈) (fst y*∈)
               -ᵣ BDL.preLn (clp (rat x) , 0<clp (rat x)) (suc Z) (snd x*∈) (fst x*∈))
               ／ᵣ₊ (clp (rat y) -ᵣ clp (rat x) ,
                 x<y→0<y-x (clp (rat x)) (clp (rat y)) x<y))
           zzWW =
            (expPreDer.slope-monotone-preLn
               (suc Z) (clp (rat x) , 0<clp (rat x)) (clp (rat y) , 0<clp (rat y))
                SSZ₊ SSSZ₊
                (snd x*∈) (fst x*∈)
                (snd y*∈) (fst y*∈)
                (snd 2+Z∈) (fst 2+Z∈)
                (snd 3+Z∈) (fst 3+Z∈)
                x<y (<ℚ→<ᵣ _ _ Z<SZ) (snd ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat x)))) (snd y*∈))

           positive-diff :
             0 <ᵣ clp (rat y) -ᵣ clp (rat x)
           positive-diff = x<y→0<y-x
             (clp (rat x)) (clp (rat y)) x<y

           abs-diff-positive :
             0 <ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y))
           abs-diff-positive = isTrans<≤ᵣ
             0 (clp (rat y) -ᵣ clp (rat x))
             (absᵣ (clp (rat x) -ᵣ clp (rat y)))
             positive-diff
             (isTrans≤≡ᵣ
               (clp (rat y) -ᵣ clp (rat x))
               (absᵣ (clp (rat y) -ᵣ clp (rat x)))
               (absᵣ (clp (rat x) -ᵣ clp (rat y)))
               (≤absᵣ (clp (rat y) -ᵣ clp (rat x)))
               (minusComm-absᵣ (clp (rat y)) (clp (rat x))))

           abs-diff₊ : ℝ₊
           abs-diff₊ =
             absᵣ (clp (rat x) -ᵣ clp (rat y)) , abs-diff-positive

           fixed-slope-path :
             ((BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
               -ᵣ BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈))
               ／ᵣ₊ (fst SSSZ₊ -ᵣ fst SSZ₊ ,
                 x<y→0<y-x (fst SSZ₊) (fst SSSZ₊)
                   (<ℚ→<ᵣ _ _ Z<SZ)))
             ≡ fst Kᵣ
           fixed-slope-path =
             cong₂ _·ᵣ_ refl
               (cong (fst ∘ invℝ₊)
                 (ℝ₊≡ {_ , _} {_ , isTrans<≡ᵣ _ _ _ decℚ<ᵣ?
                   (sym (cong (rat ∘ [_/ 1 ]) hhhh))}
                   (-ᵣ-rat₂
                     [ pos (suc (suc (suc Z))) / 1 ]
                     [ pos (suc (suc Z)) / 1 ]
                   ∙ cong rat (ℚ.ℤ-→ℚ-
                     (pos (suc (suc (suc Z))))
                     (pos (suc (suc Z)))
                   ∙ cong ([_/ 1 ])
                     (cong
                       (λ t → t ℤ.+ ℤ.- (pos (suc (suc Z))))
                       (ℤ.pos+ 1 (suc (suc Z)))
                     ∙ sym (ℤ.+Assoc (pos 1) (pos (suc (suc Z)))
                         (ℤ.- (pos (suc (suc Z)))))
                     ∙ 𝐙'.+IdR' (pos 1)
                         (pos (suc (suc Z)) ℤ.+
                           ℤ.- (pos (suc (suc Z))))
                         (ℤ.-Cancel (pos (suc (suc Z))))
                     ∙ sym hhhh))))
               ∙ cong (fst ∘ invℝ₊)
                   (ℝ₊≡ (cong rat (cong [_/ 1 ] hhhh)))
               ∙ cong fst invℝ₊1)
             ∙ ·IdR _

           log-slope-path :
             ((BDL.preLn (clp (rat y) , 0<clp (rat y))
                 (suc Z) (snd y*∈) (fst y*∈)
               -ᵣ BDL.preLn (clp (rat x) , 0<clp (rat x))
                 (suc Z) (snd x*∈) (fst x*∈))
               ／ᵣ₊ (clp (rat y) -ᵣ clp (rat x) , positive-diff))
             ≡ absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
                 ·ᵣ fst (invℝ₊ abs-diff₊)
           log-slope-path =
             cong₂ _·ᵣ_
               (sym (absᵣNonNeg
                 (BDL.preLn (clp (rat y) , 0<clp (rat y))
                    (suc Z) (snd y*∈) (fst y*∈)
                  -ᵣ BDL.preLn (clp (rat x) , 0<clp (rat x))
                    (suc Z) (snd x*∈) (fst x*∈))
                 (x≤y→0≤y-x _ _
                   (expPreDer.monotonePreLn (suc Z)
                     (clp (rat x) , 0<clp (rat x))
                     (clp (rat y) , 0<clp (rat y))
                     (snd x*∈) (fst x*∈) (snd y*∈) (fst y*∈)
                     (<ᵣWeaken≤ᵣ _ _ x<y))))
               ∙ cong absᵣ
                   (cong₂ (λ u v → u +ᵣ -ᵣ v)
                     (sym (lnX'ₙ
                       (clp (rat y) , 0<clp (rat y))
                       (0<clp (rat y)) y*∈))
                     (sym (lnX'ₙ
                       (clp (rat x) , 0<clp (rat x))
                       (0<clp (rat x)) x*∈)))
               ∙ minusComm-absᵣ (lnX' (rat y)) (lnX' (rat x)))
               (cong (fst ∘ invℝ₊)
                 (ℝ₊≡
                   {x = (clp (rat y) -ᵣ clp (rat x) , positive-diff)}
                   {y = abs-diff₊}
                   (sym (absᵣPos
                     (clp (rat y) -ᵣ clp (rat x)) positive-diff)
                   ∙ minusComm-absᵣ (clp (rat y)) (clp (rat x)))))

        opaque
         unfolding _+ᵣ_
         zzzz* : fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v) ≤ᵣ absᵣ (lnX' u -ᵣ lnX' v)
         zzzz* =
           ≤Cont₂
              {λ u v → fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v)}
              {λ u v → absᵣ (lnX' u -ᵣ lnX' v)}
              (cont∘₂ (IsContinuous∘ _ _
                 (IsContinuous·ᵣL (fst Kᵣ))
                 IsContinuousAbsᵣ)
                (cont₂∘  (contNE₂ sumR)
                  clpCount
                  (IsContinuous∘ _ _
                    IsContinuous-ᵣ clpCount)) )
              (cont∘₂ IsContinuousAbsᵣ
                (cont₂∘  (contNE₂ sumR)
                  lnX'Cont
                  (IsContinuous∘ _ _
                    IsContinuous-ᵣ lnX'Cont)
                  ))
              (ℚ.elimBy≡⊎<'
                 (λ x y X →
                   subst2 (_≤ᵣ_ ∘ (fst Kᵣ ·ᵣ_))
                     ((minusComm-absᵣ (clp (rat x)) (clp (rat y))))
                     (minusComm-absᵣ (lnX' (rat x)) (lnX' (rat y)))
                     X)
                 (λ x → ≡ᵣWeaken≤ᵣ _ _
                      (Rℝ.0RightAnnihilates' _ _ (cong absᵣ (+-ᵣ _)
                        ∙ absᵣ-rat 0)
                       ∙∙ sym (absᵣ-rat 0)
                       ∙∙ cong absᵣ ((sym (+-ᵣ (lnX' (rat x)))))))
                 λ x h₊ →
                   let
                     y = x ℚ.+ fst h₊
                     x<y = ℚ≤→<+₊ x x h₊ (ℚ.isRefl≤ x)
                   in
                    ⊎.rec
                     (zzzz= x y)
                     (zzzz< x y)
                     (ℚ-clamp-<-casesᵣ ([ 1 /  (1+ (suc Z)) ])
                            ([ pos (suc (suc Z)) / 1 ])
                            x y 1/SSZ<SSZ x<y))
              u v

        lnX'-u≡ln-u₊ : lnX' u ≡ ln u₊
        lnX'-u≡ln-u₊ =
          cong ln
            (ℝ₊≡
              {x = (clp u , 0<clp u)} {y = u₊}
              (sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)))

        ln-u₊≡seq-u : ln u₊ ≡ Seq⊆→.fun Seq-^ u Z u∈ .snd
        ln-u₊≡seq-u =
          cong snd (Seq-^-FI.∩$-∈ₙ u (snd u₊) Z u∈)

        seq-u≡preLn-u₊ :
          Seq⊆→.fun Seq-^ u Z u∈ .snd ≡
            expPreDer.expPreDer'.preLn Z
              (u , isTrans<≤ᵣ 0
                (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
                (<ℚ→<ᵣ [ pos 0 / 1 ]
                  [ pos 1 / fromNat (suc (suc Z)) ]
                  (0<pos 0 (fromNat (suc (suc Z)))))
                (fst u∈))
              (snd u∈) (fst u∈)
        seq-u≡preLn-u₊ =
          Seq-^-fun-snd≡preLn-with u Z u∈
            (isTrans<≤ᵣ 0
              (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
              (<ℚ→<ᵣ [ pos 0 / 1 ]
                [ pos 1 / fromNat (suc (suc Z)) ]
                (0<pos 0 (fromNat (suc (suc Z)))))
              (fst u∈))

        lnX'-u≡lnU : lnX' u ≡ lnU
        lnX'-u≡lnU =
          lnX'-u≡ln-u₊ ∙ ln-u₊≡seq-u ∙ seq-u≡preLn-u₊

        lnX'-v≡ln-v₊ : lnX' v ≡ ln v₊
        lnX'-v≡ln-v₊ =
          cong ln
            (ℝ₊≡
              {x = (clp v , 0<clp v)} {y = v₊}
              (sym (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈)))

        ln-v₊≡seq-v : ln v₊ ≡ Seq⊆→.fun Seq-^ v Z v∈ .snd
        ln-v₊≡seq-v =
          cong snd (Seq-^-FI.∩$-∈ₙ v (snd v₊) Z v∈)

        seq-v≡preLn-v₊ :
          Seq⊆→.fun Seq-^ v Z v∈ .snd ≡
            expPreDer.expPreDer'.preLn Z
              (v , isTrans<≤ᵣ 0
                (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
                (<ℚ→<ᵣ [ pos 0 / 1 ]
                  [ pos 1 / fromNat (suc (suc Z)) ]
                  (0<pos 0 (fromNat (suc (suc Z)))))
                (fst v∈))
              (snd v∈) (fst v∈)
        seq-v≡preLn-v₊ =
          Seq-^-fun-snd≡preLn-with v Z v∈
            (isTrans<≤ᵣ 0
              (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
              (<ℚ→<ᵣ [ pos 0 / 1 ]
                [ pos 1 / fromNat (suc (suc Z)) ]
                (0<pos 0 (fromNat (suc (suc Z)))))
              (fst v∈))

        lnX'-v≡lnV : lnX' v ≡ lnV
        lnX'-v≡lnV =
          lnX'-v≡ln-v₊ ∙ ln-v₊≡seq-v ∙ seq-v≡preLn-v₊

        weighted-clamp-path :
          fst Kᵣ ·ᵣ absᵣ (u -ᵣ v) ≡
            fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v)
        weighted-clamp-path = cong₂
          (λ u' v' → fst Kᵣ ·ᵣ absᵣ (u' -ᵣ v'))
          (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)
          (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈)

        log-abs-path :
          absᵣ (lnX' u -ᵣ lnX' v) ≡ absᵣ (lnU -ᵣ lnV)
        log-abs-path = cong absᵣ
          (cong₂ _-ᵣ_ lnX'-u≡lnU lnX'-v≡lnV)

        zzzz : absᵣ (u -ᵣ v) ≤ᵣ
               invℝ₊ Kᵣ .fst ·ᵣ absᵣ (lnU -ᵣ lnV)
        zzzz =
          let weighted-bound :
                fst Kᵣ ·ᵣ absᵣ (u -ᵣ v) ≤ᵣ absᵣ (lnU -ᵣ lnV)
              weighted-bound = isTrans≤≡ᵣ
                (fst Kᵣ ·ᵣ absᵣ (u -ᵣ v))
                (absᵣ (lnX' u -ᵣ lnX' v))
                (absᵣ (lnU -ᵣ lnV))
                (isTrans≡≤ᵣ
                  (fst Kᵣ ·ᵣ absᵣ (u -ᵣ v))
                  (fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v))
                  (absᵣ (lnX' u -ᵣ lnX' v))
                  weighted-clamp-path zzzz*)
                log-abs-path
              quotient-bound :
                absᵣ (u -ᵣ v) ≤ᵣ
                  absᵣ (lnU -ᵣ lnV) ·ᵣ fst (invℝ₊ Kᵣ)
              quotient-bound = invEq
                (z≤x/y₊≃y₊·z≤x
                  (absᵣ (lnU -ᵣ lnV)) (absᵣ (u -ᵣ v)) Kᵣ)
                weighted-bound
          in isTrans≤≡ᵣ
            (absᵣ (u -ᵣ v))
            (absᵣ (lnU -ᵣ lnV) ·ᵣ fst (invℝ₊ Kᵣ))
            (fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV))
            quotient-bound
            (·ᵣComm (absᵣ (lnU -ᵣ lnV)) (fst (invℝ₊ Kᵣ)))

        invKᵣ<invK :
          fst (invℝ₊ Kᵣ) <ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ K₊))
        invKᵣ<invK =
          invEq (invℝ₊-<-invℝ₊ Kᵣ (ℚ₊→ℝ₊ K₊)) K<Kᵣ

        product-bound :
          fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV) <ᵣ
            fst (invℝ₊ (ℚ₊→ℝ₊ K₊)) ·ᵣ rat (fst ε)
        product-bound =
          <ᵣ₊Monotone·ᵣ
            (fst (invℝ₊ Kᵣ))
            (fst (invℝ₊ (ℚ₊→ℝ₊ K₊)))
            (absᵣ (lnU -ᵣ lnV))
            (rat (fst ε))
            (<ᵣWeaken≤ᵣ 0 (fst (invℝ₊ Kᵣ)) (snd (invℝ₊ Kᵣ)))
            (0≤absᵣ (lnU -ᵣ lnV))
            invKᵣ<invK lnuv<

        product-rat-bound :
          fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV) <ᵣ
            rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε)
        product-rat-bound =
          isTrans<≡ᵣ
            (fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV))
            (fst (invℝ₊ (ℚ₊→ℝ₊ K₊)) ·ᵣ rat (fst ε))
            (rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε))
            product-bound
            (cong₂ _·ᵣ_ (invℝ₊-rat K₊) refl)

        abs-bound-product :
          absᵣ (u -ᵣ v) <ᵣ
            rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε)
        abs-bound-product =
          isTrans≤<ᵣ
            (absᵣ (u -ᵣ v))
            (fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV))
            (rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε))
            zzzz product-rat-bound

        abs-bound-rat :
          absᵣ (u -ᵣ v) <ᵣ rat (fst (invℚ₊ K₊ ·₊ ε))
        abs-bound-rat =
          isTrans<≡ᵣ
            (absᵣ (u -ᵣ v))
            (rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε))
            (rat (fst (invℚ₊ K₊ ·₊ ε)))
            abs-bound-product
            (sym (rat·ᵣrat (fst (invℚ₊ K₊)) (fst ε)))

inj-ln : ∀ x y → ln x ≡ ln y → x ≡ y
inj-ln (x , 0<x) (y , 0<y) =
  Seq-^-FI.∩$-elimProp2 x 0<x y 0<y
   {λ (_ , ln-x) (_ , ln-y) → ln-x ≡ ln-y → (x , 0<x) ≡ (y , 0<y) }
   (λ _ _ → isPropΠ λ _ → isSetℝ₊ _ _)
   λ Z x∈ y∈ p →
     let
       seq-x-path :
         Seq⊆→.fun Seq-^ x Z x∈ .snd ≡
           expPreDer.expPreDer'.preLn Z
             (x , isTrans<≤ᵣ 0
               (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
               (<ℚ→<ᵣ [ pos 0 / 1 ]
                 [ pos 1 / fromNat (suc (suc Z)) ]
                 (0<pos 0 (fromNat (suc (suc Z)))))
               (fst x∈))
             (snd x∈) (fst x∈)
       seq-x-path =
         Seq-^-fun-snd≡preLn-with x Z x∈
           (isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst x∈))

       seq-y-path :
         Seq⊆→.fun Seq-^ y Z y∈ .snd ≡
           expPreDer.expPreDer'.preLn Z
             (y , isTrans<≤ᵣ 0
               (rat [ pos 1 / fromNat (suc (suc Z)) ]) y
               (<ℚ→<ᵣ [ pos 0 / 1 ]
                 [ pos 1 / fromNat (suc (suc Z)) ]
                 (0<pos 0 (fromNat (suc (suc Z)))))
               (fst y∈))
             (snd y∈) (fst y∈)
       seq-y-path =
         Seq-^-fun-snd≡preLn-with y Z y∈
           (isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) y
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst y∈))

       preLn-path :
         expPreDer.expPreDer'.preLn Z
           (x , isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst x∈))
           (snd x∈) (fst x∈)
         ≡ expPreDer.expPreDer'.preLn Z
           (y , isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) y
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst y∈))
           (snd y∈) (fst y∈)
       preLn-path = sym seq-x-path ∙ p ∙ seq-y-path
     in PT.rec (isSetℝ₊ _ _)
       (λ (K , isLip) →
         ℝ₊≡
           (InverseLipschitz-ℝ→ℝℙ→injective K
             (Seq⊆.𝕡 seq-^-intervals Z)
             (λ z (≤z , z≤) → expPreDer.expPreDer'.preLn Z
               (z , isTrans<≤ᵣ 0
                 (rat [ pos 1 / fromNat (suc (suc Z)) ]) z
                 (<ℚ→<ᵣ [ pos 0 / 1 ]
                   [ pos 1 / fromNat (suc (suc Z)) ]
                   (0<pos 0 (fromNat (suc (suc Z)))))
                 ≤z)
               z≤ ≤z)
             isLip x x∈ y y∈ preLn-path))
       (invLipPreLn Z)
