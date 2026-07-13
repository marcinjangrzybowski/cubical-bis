{-# OPTIONS --lossy-unification #-}

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
      BDL.𝒇-monotone-str
        (fst x ,
          isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc n)) ]) (fst x)
            (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc n)) ]
              (0<pos 0 (fromNat (suc (suc n)))))
            (fst x∈ₙ))
        n (snd x∈ₙ) (fst x∈ₙ)
         1<x y y' y<y')

 ln-c : ∀ x → 0 <ᵣ x → ℝ
 ln-c x 0<x = snd (∩$ x 0<x)

 ln : ℝ₊ → ℝ
 ln (x , 0<x) = snd (∩$ x 0<x)

 ln-1≡0 : ln 1 ≡ 0
 ln-1≡0 =
   let 1r : ℝ₊
       1r = fromNat 1
   in ∩$-elimProp (fst 1r) (snd 1r)
             {λ (_ , lnx) → lnx ≡ 0}
             (λ _ → isSetℝ _ _)
             λ Z x∈ →
                 congS (λ 0<1 → BDL.preLn (rat [ pos (suc zero) / 1+ zero ] , 0<1)
                        Z (snd x∈) (fst x∈))
                         (isProp<ᵣ _ _ _ _)
                ∙ sym (expPreDer.0=preLn Z (snd x∈) (fst x∈))

 ln-cont : IsContinuousWithPred pred0< (curry ln)
 ln-cont x ε 0<x = w
  where
  ww : (Z : ℕ) (x∈ : x ∈ Seq⊆.𝕡 seq-^-intervals Z) →
        ∃-syntax ℚ₊
        (λ δ →
           (v : ℝ) (v∈P : 0 <ᵣ v) →
           x ∼[ δ ] v → Seq⊆→.fun Seq-^ x Z x∈ .snd ∼[ ε ] curry ln v v∈P)
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
            (λ v 0<v x∼v →
                let ca' = expPreDer.expPreDer'.preLn∼ (suc Z)
                    uvu = isTrans≡≤ᵣ (rat [ pos 1 / 2+ suc Z ]) _ _
                           (cong rat ℚ! ∙
                              sym (-ᵣ-rat₂ [ 1 / fromNat (suc (suc Z)) ] (fst δZ)))
                           (≤ᵣMonotone+ᵣ _ _ _ _
                          (fst x∈) (-ᵣ≤ᵣ _ _ (isTrans≤ᵣ _ _ _ (isTrans≤ᵣ _ _ _
                            (≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                                   x∼v))) (≤ℚ→≤ᵣ _ _ (ℚ.min≤' _ _)))))
                    uuuV : v ∈ seq-^-intervals .Seq⊆.𝕡 (suc Z)
                    uuuV = isTrans≤≡ᵣ _ _ _ uvu ℝ!
                        , (isTrans≤≡ᵣ _ _ _
                            (isTrans≤ᵣ _ _ _
                             (a-b≤c⇒a≤c+b _ _ _
                               (isTrans≤ᵣ _ _ _ (≤absᵣ _)
                                (isTrans≤ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (fst (∼≃abs<ε _ _ _)
                                   (sym∼ _ _ _ x∼v)))
                                    (≤ℚ→≤ᵣ _ _
                                      (ℚ.isTrans≤ _ _ _ (ℚ.min≤' _ _)
                                       (≤-ℚ₊ [ 1 / fromNat (suc (suc Z)) ]
                                        1 ([ 1 / fromNat (suc (suc (suc Z))) ] ,
                                           0<pos 0 (fromNat (suc (suc (suc Z)))))
                                         (ℚ.invℚ₊≤invℚ₊ (fromNat (suc (suc Z))) 1
                                           (≤ℤ→≤ℚ _ _
                                              (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                                                (ℕ.suc-≤-suc ℕ.zero-≤))))))))))
                             (≤ᵣ-o+ _ _ 1 (snd x∈)))
                            (+ᵣ-rat _ _ ∙  cong rat (ℚ.ℕ+→ℚ+ _ _)))
                    ≡ε = ℚ!
                    0<x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst uuu)
                    0<v = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) (fst uuuV)
                    qqq : BDL.preLn (x , 0<x) (suc Z) (snd (Seq⊆.𝕡⊆ seq-^-intervals Z x x∈))
                           (fst (Seq⊆.𝕡⊆ seq-^-intervals Z x x∈))
                           ∼[ ((ε /4₊) +₊ (ε /2₊)) +₊ (ε /4₊) ]
                           BDL.preLn (v , 0<v) (suc Z) (snd uuuV) (fst uuuV)
                    qqq = (triangle∼ (triangle∼ (sym∼ _ _ _
                              (ca' (x , 0<x)
                               (snd uuu) (fst uuu) _ _ ℕ.≤-refl))
                          ((D v 0<v
                             (∼-monotone≤ (ℚ.min≤ _ _) x∼v))))
                           ((ca' (v , 0<v) (snd uuuV) (fst uuuV) _ _ ℕ.≤-refl)))
                in ((cong snd (2c x (suc Z) Z uuu _))
                     subst∼[ ℚ₊≡ ≡ε ]
                       (cong snd (sym (∩$-∈ₙ v _ (suc Z) uuuV)))
                       )
                       qqq))
        (lnSeqCont (suc N) x (ε /2₊) _)

  w : ∃-syntax ℚ₊
        (λ δ → (v : ℝ) (v∈P : 0 <ᵣ v) →
          x ∼[ δ ] v → curry ln x 0<x ∼[ ε ] curry ln v v∈P)
  w = ∩$-elimProp x 0<x
    {λ (_ , lnx) → ∃-syntax ℚ₊
      (λ δ → (v : ℝ) (v∈P : 0 <ᵣ v) →
        x ∼[ δ ] v → lnx ∼[ ε ] curry ln v v∈P)}
    (λ _ → squash₁)
    ww



 ^-rat : ∀ x y → fst (x ^ᵣ (rat y)) ≡ fst (x ^ℚ y)
 ^-rat x =
   ∩$-elimProp (fst x) (snd x)
    {λ (f , _) → ∀ y → fst (f (rat y)) ≡ fst (x ^ℚ y)}
     (λ _ → isPropΠ λ _ → isSetℝ _ _)
     (λ n (≤x , x≤) q →
          BDL.𝒇-rat _ n x≤ ≤x q ∙ cong (λ x → fst (x ^ℚ q)) (ℝ₊≡ refl))


 ln-inv : ∀ x → ln (invℝ₊ x) ≡ -ᵣ (ln x)
 ln-inv (x , 0<x) =
   let (1/x , 0<1/x) = invℝ₊ (x , 0<x)
   in ∩$-elimProp2 1/x 0<1/x x 0<x
        {λ (_ , ln1/x) (_ , lnx) → ln1/x ≡ -ᵣ lnx}
        (λ _ _ → isSetℝ _ _)
        λ Z x∈ y∈ →
          congS (λ zz → BDL.preLn (1/x , zz) Z (snd x∈) (fst x∈))
            (isProp<ᵣ 0 _ _ _)  ∙ expPreDer.preLn-inv Z _
            (snd y∈) (fst y∈) (snd x∈) (fst x∈)
           ∙ congS (λ zz → -ᵣ (BDL.preLn (x , zz) Z (snd y∈) (fst y∈)))
            (isProp<ᵣ 0 _ _ _)

 cont-^ : ∀ (x : ℝ₊) → IsContinuous (fst ∘ x ^ᵣ_)
 cont-^ (x , 0<x) =
    ∩$-elimProp x 0<x  {λ (f , _) → IsContinuous (fst ∘ f)}
      (λ _ → isPropIsContinuous _)
      λ Z (≤x , x≤) → BDL.𝒇-cont _ Z x≤ ≤x



 -- slope-monotone-^ᵣ :   (a b a' b' : ℝ₊)
 --  → (a<b : fst a <ᵣ fst b) → (a'<b' : fst a' <ᵣ fst b')
 --  → (a≤a' : fst a ≤ᵣ fst a') →  (b≤b' : fst b ≤ᵣ fst b') →
 --  ∀ y → 1 ≤ᵣ y →
 --  (((fst (b ^ᵣ y)) -ᵣ (fst (a ^ᵣ y)))
 --    ／ᵣ₊ (_ , x<y→0<y-x _ _ a<b ))
 --      ≤ᵣ
 --  (((fst (b' ^ᵣ y)) -ᵣ (fst (a' ^ᵣ y)))
 --    ／ᵣ₊ (_ , x<y→0<y-x _ _ a'<b' ))
 -- slope-monotone-^ᵣ a b a' b' a<b a'<b' a≤a' b≤b' =
 --   (≤ContPos' {1}
 --    (IsContinuous∘ _ _ (IsContinuous·ᵣR _)
 --      (cont₂+ᵣ _ _
 --        (cont-^ _)
 --        (IsContinuous∘ _ _
 --          IsContinuous-ᵣ
 --           (cont-^ _))))
 --    (IsContinuous∘ _ _ (IsContinuous·ᵣR _)
 --      (cont₂+ᵣ _ _
 --        (cont-^ _)
 --        (IsContinuous∘ _ _
 --          IsContinuous-ᵣ
 --           (cont-^ _))))
 --    λ q 1≤q →
 --      subst2 _≤ᵣ_
 --        (cong₂ (λ u v → ((u -ᵣ v) ／ᵣ₊
 --         (fst b +ᵣ -ᵣ fst a , x<y→0<y-x (fst a) (fst b) a<b)))
 --        (sym (^-rat _ _)) (sym (^-rat _ _)))
 --        ((cong₂ (λ u v → ((u -ᵣ v) ／ᵣ₊
 --         (fst b' +ᵣ -ᵣ fst a' , x<y→0<y-x (fst a') (fst b') a'<b')))
 --        (sym (^-rat _ _)) (sym (^-rat _ _))))
 --        (slope-monotone-^ℚ a b a' b' a<b a'<b' a≤a' b≤b' q 1≤q))

 -- ^-cont : ∀ (y : ℝ) → IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y)))
 -- ^-cont  y = {! !}

 -- factor-xᵃ-xᵇ'ᵣ : ∀ x a b → fst (x ^ᵣ a) -ᵣ fst (x ^ᵣ b) ≡
 --                         fst (x ^ᵣ a) ·ᵣ (1 -ᵣ fst (x ^ᵣ (b -ᵣ a)))
 -- factor-xᵃ-xᵇ'ᵣ x a b = {!!}

 -- ^-monotone-lemmaℚ : ∀ (x : ℚ₊) y (δ : ℚ₊) → fst ((ℚ₊→ℝ₊ x) ^ℚ y) ∈
 --                        intervalℙ (minᵣ (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ))))
 --                                      (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ)))))
 --                                  (maxᵣ (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ))))
 --                                      (fst ((ℚ₊→ℝ₊ x) ^ℚ (y ℚ.+ (fst δ)))))
 -- ^-monotone-lemmaℚ = {!!}

 -- ^-monotone-lemma : ∀ x y δ → fst (x ^ᵣ y) ∈
 --                        intervalℙ (minᵣ (fst (x ^ᵣ (y -ᵣ δ)))
 --                                      (fst (x ^ᵣ (y +ᵣ δ))))
 --                                  (maxᵣ (fst (x ^ᵣ (y -ᵣ δ)))
 --                                      (fst (x ^ᵣ (y +ᵣ δ))))
 -- ^-monotone-lemma = {!!}
 -- -- ^-strictMonotone : ∀ x x' y → 0 <ᵣ y → fst x <ᵣ fst x'
 -- --   → fst (x ^ᵣ y) <ᵣ fst (x' ^ᵣ y)
 -- -- ^-strictMonotone = {!!}

--  ^-cont : ∀ (y : ℝ) → IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y)))
--  ^-cont y u ε 0<u =
--    PT.rec
--      squash₁
--       (λ (δy , Xy) →
--         PT.rec2 squash₁
--           (λ (δy- , (<δy- , δy-< )) (δy+ , <δy+ , δy+< )
--              → PT.map2
--               (λ (δx- , Xx-) (δx+ , Xx+ ) →
--                 let δ₊ = ℚ.min₊ (ℚ.min₊ δx- δx+) δy
--                     Xy- = subst ((fst ((u , 0<u) ^ᵣ y))  ∼[ /4₊ ε ]_)
--                             (^-rat _ _)
--                              (Xy (rat δy-)
--                              {!!})
--                     Xy+ = subst ((fst ((u , 0<u) ^ᵣ y))  ∼[ /4₊ ε ]_)
--                             (^-rat _ _)
--                              (Xy (rat δy+) {!!})
--                 in δ₊ ,
--                   λ v 0<v u∼v →
--                    let Y : fst ((u , 0<u) ^ᵣ y) ∼[ _ ]
--                             fst ((v , 0<v) ^ᵣ rat δy-)
--                        Y = triangle∼ Xy-
--                           (subst ((fst ((u , 0<u) ^ℚ δy-))  ∼[ /4₊ ε ]_)
--                             (sym (^-rat _ _))
--                              ((Xx- v 0<v {!!})) )
--                    in {!!}
--                  )
--               (IsContinuous^ℚ δy- u (/4₊ ε) 0<u)
--               (IsContinuous^ℚ δy+ u (/4₊ ε) 0<u)
--              )
--           (denseℚinℝ (y -ᵣ rat (fst δy)) y {!!})
--           (denseℚinℝ y (y +ᵣ rat (fst δy)) {!!}))
--       (cont-^ (u , 0<u) y (/4₊ ε))
-- --     PT.map
-- --       {!!}
-- --       (denseℚinℝ 0 (fst δᵣ) (snd δᵣ))


   -- Seq⊆.elimProp-∩ Seq⊆-abs<N
   --    ⊤Pred y tt Seq⊆-abs<N-s⊇-⊤Pred
   --    (λ (y : ℝ) → IsContinuousWithPred pred0< (curry (fst ∘ (_^ᵣ y))))
   --    (λ _ → isPropΠ3 λ _ _ _ → squash₁)
   --    λ n y∈ u ε u∈P → PT.map2
   --     (λ (δ , X) (δ' , X') →
   --       ℚ.min₊ δ δ' ,
   --        λ v 0<v u∼v →
   --          let B  = fst (∼≃abs<ε _ _ _)
   --                     $ X  v 0<v (∼-monotone≤ (ℚ.min≤ _ _ ) u∼v)
   --              B' = fst (∼≃abs<ε _ _ _)
   --                     $ X' v 0<v (∼-monotone≤ (ℚ.min≤' _ _) u∼v)
   --          in invEq (∼≃abs<ε _ _ _)
   --               (isTrans≤<ᵣ _ _ _
   --                 (^B-δ-lemma n y (u , _) (v , 0<v)
   --                  (ointervalℙ⊆intervalℙ _ _ _ y∈))
   --                 (max<-lem _ _ _
   --                   B
   --                   B')))
   --     (IsContinuous^ℚ (fromNat (suc n)) u ε u∈P)
   --     (IsContinuous^ℚ (fromNeg (suc n)) u ε u∈P)


 {-
 Old quotient-slope derivative theorem. Previous name: ^-der.

 ^-der : ∀ x → ∀ y → derivativeOf (fst ∘ x ^ᵣ_) at y
               is (fst (x ^ᵣ y) ·ᵣ ln x)
 ^-der (x , 0<x) = ∩$-elimProp x 0<x
       {λ (g , d) → (y : ℝ) →
         derivativeOf (fst ∘ g) at y is (fst (g y) ·ᵣ d)}
      (λ _ → isPropΠ2 λ _ _ → squash₁)
       (λ n (a , b) →
         BDL.expDerA
           (x ,
            isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc n)) ]) x
              (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc n)) ]
                (0<pos 0 (fromNat (suc (suc n)))))
              a)
           n b a)
 -}

 ^ᵣ0 : ∀ x → fst (x ^ᵣ 0) ≡ 1
 ^ᵣ0 x = ^-rat x 0

 ^ᵣ1 : ∀ x → fst (x ^ᵣ 1) ≡ fst x
 ^ᵣ1 x = ^-rat x 1 ∙ ^ⁿ-1 _

 ^ᵣ[1/n] : ∀ x n₊ → fst (x ^ᵣ rat [ 1 / n₊ ]) ≡ fst (root n₊ x)
 ^ᵣ[1/n] x n₊ =  ^-rat x [ 1 / n₊ ] ∙ ^ⁿ-1 _

 1<a→0<ln[a] : ∀ a → (1 <ᵣ fst a) → 0 <ᵣ ln a
 1<a→0<ln[a] (a , 0<a) 1<a =
    ∩$-elimProp a 0<a
             {λ (_ , lna) → 0 <ᵣ lna}
               (λ _ → isProp<ᵣ _ _)
               λ _ _ → BDL.0<preLn _ _ _ _ 1<a

 ^ᵣ+ : ∀ x y y' → x ^ᵣ (y +ᵣ y') ≡ (x ^ᵣ y) ₊·ᵣ (x ^ᵣ y')
 ^ᵣ+ (x , 0<x) y y' =
   ∩$-elimProp x 0<x
    {λ (f , _) → f (y +ᵣ y') ≡ f y ₊·ᵣ f y'}
    (λ _ → isSetℝ₊ _ _ )
    λ n x∈ → ℝ₊≡ (sym (BDL.𝒇· _ _ _  _ y y'))

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

-- clamp : ℚ → ℚ → ℚ → ℚ
-- clamp d u x = ℚ.min (ℚ.max d x) u


opaque
 unfolding maxᵣ
 ℚ-clamp-<-cases : ∀ L L' x y → L ℚ.< L' → x ℚ.< y →
                     (ℚ.clamp L L' x ≡ ℚ.clamp L L' y) ⊎
                        (ℚ.clamp L L' x ℚ.< ℚ.clamp L L' y)
 ℚ-clamp-<-cases L L' x y L<L' x<y =
   w (ℚ.Dichotomyℚ y L) (ℚ.Dichotomyℚ L' x)
  where
  w : (y ℚ.≤ L) ⊎ (L ℚ.< y) → (L' ℚ.≤ x) ⊎ (x ℚ.< L') → (ℚ.clamp L L' x ≡ ℚ.clamp L L' y) ⊎
                        (ℚ.clamp L L' x ℚ.< ℚ.clamp L L' y)
  w _ (inl L'≤x) = inl (ℚ.minComm _ _ ∙ ℚ.≤→min _ _ (ℚ.isTrans≤ _ _ _ L'≤x (ℚ.≤max' _ _))
       ∙ sym ((ℚ.minComm _ _ ∙ ℚ.≤→min _ _
        (ℚ.isTrans≤ _ _ _ (ℚ.isTrans≤ _ _ _ L'≤x (ℚ.<Weaken≤ _ _ x<y)) (ℚ.≤max' _ _)))))
  w (inl y≤L) _ = inl
    (cong (flip ℚ.min _) (ℚ.maxComm _ _ ∙
     (ℚ.≤→max _ _ (ℚ.isTrans≤ _ _ _  (ℚ.<Weaken≤ _ _ x<y) y≤L)))
      ∙ cong (flip ℚ.min _) (sym (ℚ.≤→max _ _ y≤L) ∙ ℚ.maxComm _ _))

  w (inr L<y) (inr x<L') = inr
   (ℚ.isTrans≤< _ _ _
     (ℚ.min≤ _ _)
       (ℚ.isTrans<≤ (ℚ.max L x) (ℚ.min y L') _
         (<ᵣ→<ℚ _ _
           (subst2 _<ᵣ_ (maxᵣ-rat L x) (minᵣ-rat y L')
             (<min-lem (rat y) (rat L') (maxᵣ (rat L) (rat x))
              (max<-lem _ _ _ (<ℚ→<ᵣ _ _ L<y) (<ℚ→<ᵣ _ _ x<y))
              (max<-lem _ _ _ ((<ℚ→<ᵣ _ _ L<L')) (<ℚ→<ᵣ _ _ x<L')))))
         (ℚ.≡Weaken≤ _ _ (cong (flip ℚ.min L') (sym (ℚ.≤→max L y (ℚ.<Weaken≤ _ _ L<y)))))))

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
           (^ⁿ-1 _ ∙ sym (·IdLᵣ _))
           (cong fst (sym (ₙ√1 _) ∙∙
             cong (root _) (ℝ₊≡ (sym (x·invℝ₊[x] _) ∙ ·ᵣComm _ _))
              ∙∙ sym (·DistRoot _ _ _)))
           ∙ sym (Rℝ.·DistL- _ _ _))
         (<ᵣ-o·ᵣ _ _
           (_ , x<y→0<y-x (fst (root (1+ (suc K)) (invℝ₊ x))) 1
              (isTrans<≡ᵣ _ _ _
               (ₙ√-StrictMonotone {invℝ₊ x} {1}  (1+ suc K)
                 (invEq (1/x<1≃1<x x) 1<x))
               (cong fst (ₙ√1 _))))
           (X (suc K) (ℕ.≤-refl {suc K}))))
       from-concave)

  where

  from-concave :
    (1 -ᵣ fst (root (2+ K) (invℝ₊ x))) ·ᵣ α ≤ᵣ
     1 -ᵣ fst ((x ₊+ᵣ Δ) ^ℚ (ℚ.- [ 1 / 2+ K ]))
  from-concave = isTrans≡≤ᵣ (_ ·ᵣ α) _ _
        (cong₂ (_·ᵣ_) (cong₂ _-ᵣ_ (cong fst (sym (ₙ√1 _)))
         refl) (·ᵣComm _ _) ∙ ·ᵣAssoc _ _ _ ∙ ·ᵣComm _ _ )
        (isTrans≤≡ᵣ _ _ _ (fst (z≤x/y₊≃y₊·z≤x _ _ _) (slope-monotone-ₙ√ (suc K)
         (invℝ₊ (x ₊+ᵣ Δ)) 1
         (invℝ₊ x) 1
         0<1-1/[x+Δ]
         0<1-1/x
         (invEq (invℝ₊-≤-invℝ₊ _ _)
           (isTrans≡≤ᵣ _ _ _ (sym (+IdR _))
            (≤ᵣ-o+ _ _ (fst x) (<ᵣWeaken≤ᵣ _ _ (snd Δ)))))
            (≤ᵣ-refl 1)))
            (cong₂ _-ᵣ_ (cong fst (ₙ√1 _))
            (sym (^ⁿ-1 _) ∙
             cong fst (sym (^ℚ-minus' _ _)))))




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
  λ Z x∈ y∈ → monotoneStrictPreLn Z
    (fst y ,
      isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc Z)) ]) (fst y)
        (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc Z)) ]
          (0<pos 0 (fromNat (suc (suc Z)))))
        (fst x∈))
    (fst y' ,
      isTrans<≤ᵣ 0 (rat [ pos 1 / fromNat (suc (suc Z)) ]) (fst y')
        (<ℚ→<ᵣ [ pos 0 / 1 ] [ pos 1 / fromNat (suc (suc Z)) ]
          (0<pos 0 (fromNat (suc (suc Z)))))
        (fst y∈))
    1<y (snd x∈) (fst x∈) (snd y∈) (fst y∈) y<y'


-- opaque
--  unfolding _+ᵣ_
invLipPreLn : ∀ Z → ∃[ K ∈ ℚ₊ ]
              Invlipschitz-ℝ→ℝℙ K
               ((intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
              (fromNat (suc (suc Z)))))
              λ x (≤x , x≤) →
                expPreDer.expPreDer'.preLn Z
                  (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) ≤x)
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
            Invlipschitz-ℝ→ℝℙ K
            (intervalℙ (rat [ pos 1 / 2+ Z ])
             (rat [ pos (suc (suc Z)) / 1+ 0 ]))
            λ x (x≤ , ≤x) → expPreDer.expPreDer'.preLn Z
                  (x , isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _)) x≤)
                 ≤x x≤)
   ww (K , 0<K , K<Kᵣ) =  (invℚ₊ K₊) , zzz

    where
    K₊ : ℚ₊
    K₊ = (K , <ᵣ→<ℚ _ _ 0<K)
    zzz : Invlipschitz-ℝ→ℝℙ (invℚ₊ K₊)
      (intervalℙ (rat [ pos 1 / 2+ Z ])
       (rat [ pos (suc (suc Z)) / 1+ 0 ]))
      (λ x (≤x , x≤) →
         BDL.preLn
         (x ,
          isTrans<≤ᵣ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 2+ Z ]) x
          (<ℚ→<ᵣ [ pos 0 / 1+ 0 ] [ pos 1 / 2+ Z ] (0<pos 0 (2+ Z)))
          ≤x)
         Z x≤ ≤x )
    zzz u u∈ v v∈ ε lnU∼lnV =
     invEq (∼≃abs<ε _ _ _)
              (isTrans<≡ᵣ _ _ _
               (isTrans≤<ᵣ _ _ _
                 zzzz
                 (isTrans<≡ᵣ _ _ _
                  (<ᵣ₊Monotone·ᵣ _ _ _ _
                  (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ Kᵣ)))
                  (0≤absᵣ _)
                  (invEq (invℝ₊-<-invℝ₊ Kᵣ _)
                    K<Kᵣ) lnuv<)
                     (cong₂ _·ᵣ_
                      (invℝ₊-rat _)
                      refl))
                 )
               (sym (rat·ᵣrat _ _)))
     where
      u₊ v₊ : ℝ₊
      u₊ =
        u ,
        isTrans<≤ᵣ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 2+ Z ]) u
          (<ℚ→<ᵣ [ pos 0 / 1+ 0 ] [ pos 1 / 2+ Z ] (0<pos 0 (2+ Z)))
          (fst u∈)
      v₊ =
        v ,
        isTrans<≤ᵣ (rat [ pos 0 / 1+ 0 ]) (rat [ pos 1 / 2+ Z ]) v
          (<ℚ→<ᵣ [ pos 0 / 1+ 0 ] [ pos 1 / 2+ Z ] (0<pos 0 (2+ Z)))
          (fst v∈)

      lnU = BDL.preLn u₊ Z (snd u∈) (fst u∈)
      lnV = BDL.preLn v₊ Z (snd v∈) (fst v∈)




      clp : ℝ → ℝ
      clp = clampᵣ (rat [ 1 / (1+  (suc Z)) ])
                   (rat [ pos (suc (suc Z)) / 1 ])

      1/SSZ<SSZ =
        ℚ.isTrans< _ 1 _
          (fst (ℚ.invℚ₊-<-invℚ₊ 1 SSZℚ₊) 1<Z)
          1<Z


      1/SSZ≤SSZ = ≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1/SSZ<SSZ)

      0<clp : ∀ x → 0 <ᵣ clp x
      0<clp x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _))
         (≤clampᵣ (rat [ 1 / (1+  (suc Z)) ]) _ x 1/SSZ≤SSZ)

      clpCount : IsContinuous clp
      clpCount = IsContinuousClamp
         (rat [ 1 / (1+  (suc Z)) ])
                   (rat [ pos (suc (suc Z)) / 1 ])

      -- lnX : ℝ → ℝ
      -- lnX x = BDL.preLn (clp x , 0<clp x) Z
      --    (clamp≤ᵣ (rat [ 1 / fromNat (suc (suc Z)) ]) _ x)

      --    (≤clampᵣ (rat [ 1 / fromNat (suc (suc Z)) ]) _ x
      --       (isTrans≤ᵣ _ 1 _
      --           (≤ℚ→≤ᵣ _ _ (fst (ℚ.invℚ₊-≤-invℚ₊ 1 (fromNat (suc (suc Z))))
      --             (ℚ.<Weaken≤ _ _ 1<Z)))
      --           (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 1<Z))))

      lnX' : ℝ → ℝ
      lnX' x = ln (clp x , 0<clp x)

      lnX'ₙ : ∀ (x : ℝ₊) 0<x
              (x∈ : fst x ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                        (rat [ pos (suc (suc (suc Z))) / 1 ]))) →
                ln x ≡ BDL.preLn
                         (fst x , 0<x) (suc Z) (snd x∈) (fst x∈)
      lnX'ₙ x 0<x x∈ =
        cong snd (Seq-^-FI.∩$-∈ₙ (fst x) (snd x) (suc Z) x∈)
        ∙ cong (λ 0<x → BDL.preLn
                         (fst x , 0<x) (suc Z) (snd x∈) (fst x∈))
                         (isProp<ᵣ _ _ _ _)

      clp≡ : ∀ u → u ∈ ((intervalℙ (rat [ 1 /  (1+ (suc Z)) ])
               (rat [ pos (suc (suc Z)) / 1 ]))) → clp u ≡ u
      clp≡ u u∈ = sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)

      lnX'Cont : IsContinuous lnX'
      lnX'Cont = IsContinuousWithPred∘IsContinuous
       _ _ _ 0<clp
       ln-cont clpCount

      lnuv< = fst (∼≃abs<ε _ _ _) lnU∼lnV

      zzzz= : ∀ x y → clampᵣ (rat [ pos 1 / 2+ Z ])
       (rat [ pos (suc (suc Z)) / 1+ 0 ]) (rat x)
       ≡
       clampᵣ (rat [ pos 1 / 2+ Z ]) (rat [ pos (suc (suc Z)) / 1+ 0 ])
       (rat y) →
       fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
       absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
      zzzz= x y p =
       ≡ᵣWeaken≤ᵣ _ _
                 (Rℝ.0RightAnnihilates' _ _
                   (cong absᵣ (Rℝ.+InvR' _ _ p) ∙ absᵣ-rat 0)
                   ∙ sym (absᵣ-rat 0) ∙
                   cong absᵣ (sym (Rℝ.+InvR' _ _
                     (ll))))

         where

         ll : ln (clp (rat x) , 0<clp (rat x))  ≡ ln (clp (rat y) , 0<clp (rat y))
         ll = cong ln (ℝ₊≡ p)

      zzzz< : ∀ x y → clampᵣ (rat [ pos 1 / 2+ Z ])
       (rat [ pos (suc (suc Z)) / 1+ 0 ]) (rat x)
       <ᵣ
       clampᵣ (rat [ pos 1 / 2+ Z ]) (rat [ pos (suc (suc Z)) / 1+ 0 ])
       (rat y) →
       fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
       absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
      zzzz< x y x<y =
       isTrans≡≤ᵣ
         (fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)))
         (absᵣ (clp (rat x) -ᵣ clp (rat y)) ·ᵣ fst Kᵣ)
         (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
        (·ᵣComm _ _) (fst (z≤x/y₊≃y₊·z≤x _ _ _)
          (subst2  _≤ᵣ_
           (cong₂ _·ᵣ_ refl
             (cong (fst ∘ invℝ₊)
              (ℝ₊≡ {_ , _} {_ , isTrans<≡ᵣ _ _ _ decℚ<ᵣ?
               (sym (cong (rat ∘ [_/ 1 ]) hhhh))} (-ᵣ-rat₂ _ _ ∙ cong rat (ℚ.ℤ-→ℚ- _ _
               ∙ cong ([_/ 1 ]) (cong₂ ℤ._+_ (ℤ.pos+ _ _) refl ∙ sym (ℤ.+Assoc 1 (pos ((suc (suc Z))))
                    (ℤ.- (pos (suc (suc Z)))))
                ∙ 𝐙'.+IdR' _ _ (ℤ.-Cancel (pos (suc (suc Z)))) ∙ sym hhhh )) ))
             ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ (cong rat (cong [_/ 1 ] hhhh))) ∙ cong fst invℝ₊1 )
             ∙ (·IdR _) )
           (cong₂ {y = absᵣ (lnX' (rat x) +ᵣ -ᵣ lnX' (rat y))} _·ᵣ_
             ( sym (absᵣNonNeg _ (x≤y→0≤y-x _ _
              (expPreDer.monotonePreLn (suc Z)
               (clp (rat x) , 0<clp (rat x))
               (clp (rat y) , 0<clp (rat y))
                (snd x*∈) (fst x*∈) (snd y*∈) (fst y*∈) (<ᵣWeaken≤ᵣ _ _ x<y))))
               ∙ cong absᵣ (cong₂ (λ u v → u +ᵣ -ᵣ v)
               (sym (lnX'ₙ ((clp (rat y)) , 0<clp (rat y)) _ _)) --(sym (lnX'ₙ _ _ _))
               ((sym (lnX'ₙ (clp (rat x) , 0<clp (rat x)) _ _))) --
                )
                 ∙ minusComm-absᵣ (lnX' (rat y)) (lnX' (rat x)))

             (cong (fst ∘ invℝ₊)
               (ℝ₊≡ {_} {_ , isTrans<≤ᵣ _ _ _ (x<y→0<y-x _ _ x<y)
                     (isTrans≤≡ᵣ _ _ _ (≤absᵣ _) (minusComm-absᵣ _ _))}
                  (sym (absᵣPos _ (x<y→0<y-x _ _ x<y))
                 ∙ minusComm-absᵣ _ _))))
           zzWW)) --
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

      zzzz : absᵣ (u -ᵣ v) ≤ᵣ
             invℝ₊ Kᵣ .fst ·ᵣ absᵣ (lnU -ᵣ lnV)
      zzzz =
        isTrans≤≡ᵣ _ _ _
          (invEq (z≤x/y₊≃y₊·z≤x _ _ _)
            (isTrans≤≡ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (cong₂ (λ u v → fst Kᵣ ·ᵣ absᵣ (u -ᵣ v))
                  (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)
                  (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈))
                zzzz*)
              (cong absᵣ
                (cong₂ _-ᵣ_
                  (cong ln
                      ((ℝ₊≡
                         {clp u , 0<clp u} {u , snd u₊}
                        (sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈))))
         ∙∙ cong snd (Seq-^-FI.∩$-∈ₙ u (snd u₊) Z u∈)
         ∙∙ cong (λ 0<u → BDL.preLn (u , 0<u) Z (snd u∈) (fst u∈))
               (isProp<ᵣ 0 u _ _))

                  (cong ln
                      ((ℝ₊≡
                         {clp v , 0<clp v} {v , snd v₊}
                        (sym (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈))))
         ∙∙ cong snd (Seq-^-FI.∩$-∈ₙ v (snd v₊) Z v∈)
         ∙∙ cong (λ 0<v → BDL.preLn (v , 0<v) Z (snd v∈) (fst v∈))
               (isProp<ᵣ 0 v _ _))
                  ))))
          (·ᵣComm _ _)

^ᵣ· : (x : ℝ₊) (a b : ℝ) →
      fst ((x ^ᵣ a) ^ᵣ b) ≡ fst (x ^ᵣ (a ·ᵣ b))
^ᵣ· x a  =
   ≡Continuous _ _
      (cont-^ _)
       (IsContinuous∘ _ _ (cont-^ x)
         (IsContinuous·ᵣL a))
     λ b' →
      ^-rat _ _ ∙
         ≡Continuous _ _
           (IsContinuousWithPred∘IsContinuous _ _
             _ (λ v → snd (x ^ᵣ v)) (IsContinuous^ℚ b') (cont-^ x))
           (IsContinuous∘ _ _ (cont-^ x)
         (IsContinuous·ᵣR (rat b')))
           (λ a' →
           (cong (fst ∘ _^ℚ b') (ℝ₊≡ (^-rat x a')))
             ∙ cong fst (^ℚ-· x a' b') ∙
             sym (^-rat _ _) ∙ cong (fst ∘ (x ^ᵣ_)) (rat·ᵣrat _ _))
           a

inj-ln : ∀ x y → ln x ≡ ln y → x ≡ y
inj-ln (x , 0<x) (y , 0<y) =
  Seq-^-FI.∩$-elimProp2 x 0<x y 0<y
   {λ (_ , ln-x) (_ , ln-y) → ln-x ≡ ln-y → (x , 0<x) ≡ (y , 0<y) }
   (λ _ _ → isPropΠ λ _ → isSetℝ₊ _ _)
   λ Z x∈ y∈ p →
     PT.rec (isSetℝ₊ _ _)
       (λ (_ , isLip) →
         ℝ₊≡ (Invlipschitz-ℝ→ℝ→injective-interval _ _ _ _ isLip x x∈ y y∈
          p))
      (invLipPreLn Z)

{-
Old proof used quotient-slope derivative uniqueness through ^-der.
Previous names: ln[a^b₊]≡b₊·ln[a], ln[a^b]≡b·ln[a].

ln[a^b₊]≡b₊·ln[a] : ∀ a (b : ℝ₊) → ln (a ^ᵣ (fst b)) ≡ fst b ·ᵣ ln a
ln[a^b₊]≡b₊·ln[a] a (b , 0<b) =
   limitUniq _ _ _ _ (zz b) (zz' b 0<b) ∙ ·ᵣComm _ _
  where
  zz : ∀ b → derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_)) at 0 is
        (ln (a ^ᵣ b))
  zz b = substDer
     (λ r → ^ᵣ· _ _ _)
     (subst (derivativeOf (fst ∘ (a ^ᵣ b) ^ᵣ_ ) at 0 is_)
     ((Rℝ.·IdL' _ _ (^ᵣ0 _))) (^-der (a ^ᵣ b) 0))

  zz'' : ∀ b (0<b : 0 <ᵣ b) → derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_))
                at 0 ／ᵣ₊ (b , 0<b) is (b ·ᵣ (fst (a ^ᵣ 0) ·ᵣ ln a))
  zz'' b 0<b = derivative-∘· _ _ _ (b , 0<b) (^-der a 0)

  zz' : ∀ b (0<b : 0 <ᵣ b) → derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_)) at 0 is (ln a ·ᵣ b)
  zz' b 0<b = subst2 (derivativeOf (fst ∘ a ^ᵣ_  ∘ (b ·ᵣ_)) at_is_)
         (Rℝ.0LeftAnnihilates _) (cong (b ·ᵣ_) (Rℝ.·IdL' _ _ (^ᵣ0 a)) ∙ ·ᵣComm _ _) (zz'' b 0<b)

ln[a^b]≡b·ln[a] : ∀ a b → ln (a ^ᵣ b) ≡ b ·ᵣ ln a
ln[a^b]≡b·ln[a] a =
  ≡Continuous _ _
    (IsContinuousWithPred∘IsContinuous
     _ _ _
      (λ x → snd (a ^ᵣ x))
      ln-cont
      (cont-^ a)) (IsContinuous·ᵣR _)
    (ℚ.byTrichotomy 0 ww)

  where
  ww : ℚ.TrichotomyRec 0 (λ z → ln (a ^ᵣ rat z) ≡ rat z ·ᵣ ln a)
  ww .ℚ.TrichotomyRec.lt-case b b<0 =
    cong ln (ℝ₊≡ (^-rat _ _ ∙∙ cong fst (^ℚ-minus _ _) ∙∙ sym (^-rat _ _)))
     ∙∙ ln[a^b₊]≡b₊·ln[a] (invℝ₊ a) (rat (ℚ.- b) ,
      <ℚ→<ᵣ _ _ (ℚ.minus-< _ _ b<0) ) ∙∙
       (cong₂ _·ᵣ_ (sym (-ᵣ-rat b)) (ln-inv a) ∙  -ᵣ·-ᵣ _ _)
  ww .ℚ.TrichotomyRec.eq-case = (cong ln (ℝ₊≡ (^ᵣ0 _)) ∙ ln-1≡0)
    ∙ sym (Rℝ.0LeftAnnihilates (ln a))
  ww .ℚ.TrichotomyRec.gt-case b 0<b =
    ln[a^b₊]≡b₊·ln[a] a (rat b , <ℚ→<ᵣ _ _ 0<b)
-}
