module Cubical.HITs.CauchyReals.Dirty.ExpLog where

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
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerBase using
  ( +Groupℝ
  ; ·₊Groupℝ
  ; ℝ₋₊
  ; Aut[_]ᵣ
  ; module +GrAutomorphism
  )

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR

open import Cubical.Algebra.Group.DirProd


ln-mon-str-<1 :
   ∀ (y y' : ℝ₊)
   → fst y' <ᵣ 1
   → fst y <ᵣ fst y'
   → ln y <ᵣ ln y'
ln-mon-str-<1 y y' y'<1 y<y' =
  <ᵣ-ᵣ _ _ $ subst2 _<ᵣ_
   (ln-inv y')
   (ln-inv y)
   (ln-mon-str-1< (invℝ₊ y') (invℝ₊ y)
   (fst (1/x<1≃1<x (invℝ₊ y'))
    (isTrans≡<ᵣ _ _ _ (cong fst (invℝ₊Invol y')) y'<1))
       (invEq (invℝ₊-<-invℝ₊ _ _) y<y'))


{-
Legacy exp/log isomorphism and logarithm derivative block. It depended on
the old quotient-slope derivative API through ln[a^b]≡b·ln[a],
𝒆'^-der, and invDerivativeℙ. Previous exported names in this block include
𝒆-number, ln-der, exp-log-group-hom, exp-log-group-iso, and 𝒆-≡.


module 𝒆-number a (1<a : 1 <ᵣ fst a) where
  𝒆' : ℝ₊
  𝒆' = a ^ᵣ (fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a)))

  ln-𝒆'≡1 : ln 𝒆' ≡ 1
  ln-𝒆'≡1 = ln[a^b₊]≡b₊·ln[a] _ (invℝ₊ _) ∙ ·ᵣComm _ _ ∙ x·invℝ₊[x] (ln a , 1<a→0<ln[a] a 1<a)

  ln[𝒆'^x]≡x : ∀ (x : ℝ) → (ln (𝒆' ^ᵣ x)) ≡  x
  ln[𝒆'^x]≡x x = ln[a^b]≡b·ln[a] _ x ∙ Rℝ.·IdR' _ _  ln-𝒆'≡1

  𝒆'^ln[x]≡x : ∀ (x : ℝ₊) → (𝒆' ^ᵣ (ln x)) ≡  x
  𝒆'^ln[x]≡x x = inj-ln (𝒆' ^ᵣ ln x) x (ln[𝒆'^x]≡x (ln x))

  exp-ln-Iso : Iso ℝ ℝ₊
  exp-ln-Iso .Iso.fun = 𝒆' ^ᵣ_
  exp-ln-Iso .Iso.inv = ln
  exp-ln-Iso .Iso.sec = 𝒆'^ln[x]≡x
  exp-ln-Iso .Iso.ret = ln[𝒆'^x]≡x

  ln-+ : ∀ x x' → ln x +ᵣ ln x' ≡ ln (x ₊·ᵣ x')
  ln-+ x x' =
     sym (ln[𝒆'^x]≡x _) ∙  cong ln (^ᵣ+  𝒆' (ln x) (ln x') ∙
       cong₂ _₊·ᵣ_ (𝒆'^ln[x]≡x x) (𝒆'^ln[x]≡x x'))

  ln-mon-str : ∀ (y y' : ℝ₊)
   → fst y <ᵣ fst y'
   → ln y <ᵣ ln y'
  ln-mon-str y y' y<y' =
    <-o+-cancel _ _ _ $ subst2 _<ᵣ_
     (sym (ln-+ (2 ₊·ᵣ invℝ₊ y) y))
     (sym (ln-+ (2 ₊·ᵣ invℝ₊ y) y'))
      $ ln-mon-str-1<
       ((2 ₊·ᵣ (invℝ₊ y)) ₊·ᵣ y)
       ((2 ₊·ᵣ (invℝ₊ y)) ₊·ᵣ y')
       (isTrans<≡ᵣ 1 2 (fst ((2 ₊·ᵣ invℝ₊ y) ₊·ᵣ y)) decℚ<ᵣ? (sym ([x/₊y]·yᵣ 2 y)) )
       (<ᵣ-o·ᵣ _ _ (2 ₊·ᵣ (invℝ₊ y)) y<y')

  𝒆'^-der : ∀ y → derivativeOf (fst ∘ 𝒆' ^ᵣ_) at y is (fst (𝒆' ^ᵣ y))
  𝒆'^-der y = subst (derivativeOf (λ r → fst r) ∘ _^ᵣ_ 𝒆' at y is_)
     (Rℝ.·IdR' _ _ ln-𝒆'≡1) (^-der 𝒆' y)


  1<𝒆' : 1 <ᵣ fst 𝒆'
  1<𝒆' =
    isTrans≡<ᵣ _ _ _
      (sym (^ᵣ0 _)) (^ᵣ-mon-str a 1<a 0
     (fst (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a)))
      (snd (invℝ₊ (ln a , 1<a→0<ln[a] a 1<a))))

  ln-der : ∀ x₀ → derivativeOfℙ pred0< , curry ln at x₀ is fst (invℝ₊ x₀)
  ln-der x₀ =
    subst (λ x → derivativeOfℙ pred0< , curry ln at x is (fst (invℝ₊ x)))
      (𝒆'^ln[x]≡x x₀)
      w
   where
   w : derivativeOfℙ pred0< , curry ln at (𝒆' ^ᵣ (ln x₀))
           is fst (invℝ₊ ((𝒆' ^ᵣ (ln x₀))))
   w = invDerivativeℙ
     (ln x₀)
     _ (fst (𝒆' ^ᵣ (ln x₀)))
     (snd (𝒆' ^ᵣ (ln x₀)))
     (snd ∘ (𝒆' ^ᵣ_))
     (snd (isoToEquiv exp-ln-Iso))
     ln-mon-str
     (^ᵣ-mon-str 𝒆' 1<𝒆' )
     (cont-^ 𝒆')
     ln-cont
     (𝒆'^-der (ln x₀))

  exp-log-group-hom : GroupHom +Groupℝ ·₊Groupℝ
  exp-log-group-hom .fst = 𝒆' ^ᵣ_
  exp-log-group-hom .snd = makeIsGroupHom (^ᵣ+ 𝒆')

  exp-log-group-iso : GroupIso +Groupℝ ·₊Groupℝ
  exp-log-group-iso = exp-ln-Iso , snd (exp-log-group-hom)


𝒆-≡ : ∀ a 1<a a' 1<a' → 𝒆-number.𝒆' a 1<a ≡ 𝒆-number.𝒆' a' 1<a'
𝒆-≡ a 1<a a' 1<a' = inj-ln _ _ (A.ln-𝒆'≡1 ∙ sym A'.ln-𝒆'≡1)

 where
 module A  = 𝒆-number a  1<a
 module A' = 𝒆-number a' 1<a'
-}


·-+grpIso : ℝ₋₊ → Aut[ snd +Groupℝ ]ᵣ .fst
·-+grpIso (α , 0＃α) =
  (i , makeIsGroupHom λ x y → ·DistR+ x y α) ,
   (IsContinuous·ᵣR α) , (IsContinuous·ᵣR (invℝ α 0＃α))
 where
  i : Iso _ _
  i .Iso.fun = _·ᵣ α
  i .Iso.inv = _·ᵣ invℝ α 0＃α
  i .Iso.sec _ = [x/y]·yᵣ _ _ _
  i .Iso.ret _ = [x·y]/yᵣ _ _ _

grpIso→α : Aut[ snd +Groupℝ ]ᵣ .fst → ℝ
grpIso→α x = Iso.fun (fst (fst x)) 1


hhzzz : (a : Aut[ snd +Groupℝ ]ᵣ .fst) →
  ∀ x → x ·ᵣ Iso.fun (fst (fst a)) 1 ≡ Iso.fun (fst (fst a)) x
hhzzz a = ≡Continuous _ _
 (IsContinuous·ᵣR _)
 (fst (snd a))
 (sym ∘ +GrAutomorphism.fun-rat (fst a))

-- hhzz-iso : Iso ℝ₋₊ (Aut[ snd +Groupℝ ]ᵣ .fst)
-- hhzz-iso .Iso.fun = ·-+grpIso
-- hhzz-iso .Iso.inv x = grpIso→α x , {!!}
-- hhzz-iso .Iso.rightInv a =
--  AutCont.i≡ (snd +Groupℝ)
--   (funExt (hhzzz a))
-- hhzz-iso .Iso.leftInv α =
--  ℝ₋₊≡ (·IdL _)

-- hhzz : GroupIso ·Groupℝ Aut[ snd +Groupℝ ]ᵣ
-- hhzz .fst = hhzz-iso
-- hhzz .snd = makeIsGroupHom λ x y → AutCont.i≡ (snd +Groupℝ)
--   (funExt λ _ → ·ᵣAssoc _ _ _)
