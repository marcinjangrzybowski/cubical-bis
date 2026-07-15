module Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition where

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


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; fromSucℚ₊)
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
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction

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
