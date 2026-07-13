{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.RealPowerBase where

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

opaque
 unfolding fromLipschitz'
 fromLipschitz'-rat : ∀ f isL q →
   fst (fromLipschitz' (f ∘S rat) isL) (rat q) ≡ f (rat q)
 fromLipschitz'-rat f = PT.elim
  (λ _ → isPropΠ λ _ → isSetℝ _ _)
  λ (L , lip) q → fromLipschitz-rat {L = L} {lf = (f ∘S rat , lip)} {q = q}

absTo≤×≤ : ∀ ε q → abs q ℚ.≤ ε → (ℚ.- ε ℚ.≤ q) × (q ℚ.≤ ε)
absTo≤×≤ ε q abs[q]≤ε .fst =
 subst (ℚ.- ε ℚ.≤_) (ℚ.-Invol q)
  (ℚ.minus-≤ _ _ (ℚ.isTrans≤ _ _ _ (-≤abs q) abs[q]≤ε))
absTo≤×≤ ε q abs[q]≤ε .snd =
 ℚ.isTrans≤ _ _ _ (≤abs q) abs[q]≤ε

≤-ℚ₊ : ∀ x y (ε : ℚ₊) → x ℚ.≤ y → (x ℚ.- fst ε) ℚ.≤ y
≤-ℚ₊ x y ε x≤y =
 subst ((x ℚ.- fst ε) ℚ.≤_)
   (ℚ.+IdR y)
   (ℚ.≤Monotone+ x y (ℚ.- fst ε) 0 x≤y (ℚ.-ℚ₊≤0 ε))

x+n·x≡sn·x : ∀ n x → x +ᵣ fromNat n ·ᵣ x ≡ fromNat (suc n) ·ᵣ x
x+n·x≡sn·x n x = cong₂ _+ᵣ_
  (sym (·IdLᵣ _)) refl ∙ sym (·DistR+ _ _ _)
   ∙ cong (_·ᵣ x) (fromNat+ᵣ 1 n)


+Groupℝ : Group₀
+Groupℝ = Ring→Group Rℝ.ℝRing

Is·₊Groupℝ : IsGroup 1 _₊·ᵣ_ invℝ₊
Is·₊Groupℝ = makeIsGroup
   isSetℝ₊
   (λ _ _ _ → ℝ₊≡ (·ᵣAssoc _ _ _ ))
   (λ _ → ℝ₊≡ (·IdR _)) (λ _ → ℝ₊≡ (·IdLᵣ _))
   (λ (x , 0<x) →
     ℝ₊≡ (cong (x ·ᵣ_) (cong fst (invℝ₊-impl (x , 0<x))) ∙ ·invℝ' x 0<x))
   (λ (x , 0<x) →
     ℝ₊≡ (·ᵣComm _ _
       ∙ cong (x ·ᵣ_) (cong fst (invℝ₊-impl (x , 0<x)))
       ∙ ·invℝ' x 0<x))

ℝ₋₊ : Type
ℝ₋₊ = Σ ℝ (0 ＃_)

_·ᵣ₋₊_ : ℝ₋₊ → ℝ₋₊ → ℝ₋₊
x ·ᵣ₋₊ x₁ = (fst x ·ᵣ fst x₁) , 0＃· _ _ (snd x) (snd x₁)

ℝ₋₊≡ : ∀ {x y : ℝ₋₊} → fst x ≡ fst y → x ≡ y
ℝ₋₊≡ = Σ≡Prop (isProp＃ 0)

ℝ₋₊→ℝ₊×Bool : ℝ₋₊ → (ℝ₊ × Bool)
ℝ₋₊→ℝ₊×Bool x = (absᵣ (fst x) , 0＃→0<abs _ (snd x)) ,
  ⊎.rec (const true) (const false) (snd x)

ℝ₊×Bool→ℝ₋₊ : (ℝ₊ × Bool) → ℝ₋₊
ℝ₊×Bool→ℝ₋₊ x = (if (snd x) then (1 , inl decℚ<ᵣ?) else (-1 , inr decℚ<ᵣ?))
  ·ᵣ₋₊ (fst (fst x) , inl (snd (fst x)))

opaque
 unfolding 0＃· absᵣ
 sec-ℝ₋₊→ℝ₊×Bool : section ℝ₋₊→ℝ₊×Bool ℝ₊×Bool→ℝ₋₊
 sec-ℝ₋₊→ℝ₊×Bool (x , false) =
   cong₂ _,_
   (ℝ₊≡ (·absᵣ _ _ ∙ ·IdLᵣ _ ∙ absᵣPos _ (snd x)))
   refl
 sec-ℝ₋₊→ℝ₊×Bool (x , true) =
  cong₂ _,_
   (ℝ₊≡ (·absᵣ _ _ ∙ ·IdLᵣ _ ∙ absᵣPos _ (snd x)))
   refl

ret-ℝ₋₊→ℝ₊×Bool : retract ℝ₋₊→ℝ₊×Bool ℝ₊×Bool→ℝ₋₊
ret-ℝ₋₊→ℝ₊×Bool (fst₁ , inl x) =
  ℝ₋₊≡ (·IdLᵣ _ ∙ absᵣPos _ x)
ret-ℝ₋₊→ℝ₊×Bool (fst₁ , inr x) =
  ℝ₋₊≡ (sym (-ᵣ≡[-1·ᵣ] _)
    ∙∙ cong (-ᵣ_) (absᵣNeg _ x)
    ∙∙ -ᵣInvol _)

Iso-ℝ₋₊-ℝ₊×𝟚 : Iso ℝ₋₊ (ℝ₊ × Bool)
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.fun  = ℝ₋₊→ℝ₊×Bool
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.inv = ℝ₊×Bool→ℝ₋₊
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.sec = sec-ℝ₋₊→ℝ₊×Bool
Iso-ℝ₋₊-ℝ₊×𝟚 .Iso.ret = ret-ℝ₋₊→ℝ₊×Bool

IsGroupℝˣ : IsGroup {G = ℝ₋₊}
  (1 , inl decℚ<ᵣ?)
  _·ᵣ₋₊_
  λ (x , 0＃x) → invℝ x 0＃x , invℝ0＃ x 0＃x
IsGroupℝˣ = makeIsGroup
  (isSetΣ isSetℝ (isProp→isSet ∘ isProp＃ 0))
  (λ _ _ _ → ℝ₋₊≡ (·ᵣAssoc _ _ _))
  (λ _ → ℝ₋₊≡ (·IdR _)) (λ _ → ℝ₋₊≡ (·IdLᵣ _))
  (λ _ → ℝ₋₊≡ (x·invℝ[x] _ _))
  (λ _ → ℝ₋₊≡ (·ᵣComm _ _ ∙ x·invℝ[x] _ _))

·₊Groupℝ : Group₀
·₊Groupℝ = group _ _ _ _ Is·₊Groupℝ

·Groupℝ : Group₀
·Groupℝ = group _ _ _ _ IsGroupℝˣ


-- GroupIso-ℝˣ-ℝˣ₊×𝟚 : GroupIso ·Groupℝ (DirProd ·₊Groupℝ BoolGroup)
-- GroupIso-ℝˣ-ℝˣ₊×𝟚 = Iso-ℝ₋₊-ℝ₊×𝟚 , makeIsGroupHom {!!}


module AutCont (Gstr : GroupStr ℝ) where

 open GroupStr Gstr
 Ĝ : Group₀
 Ĝ = ℝ , Gstr

 contGroupIso : Type
 contGroupIso = Σ (GroupIso Ĝ Ĝ) λ x → (IsContinuous (Iso.fun (fst x))
                                        × IsContinuous (Iso.inv (fst x)))
 i≡ : ∀ {x₀ x₁ : contGroupIso} → Iso.fun (fst (fst x₀)) ≡ Iso.fun (fst (fst x₁)) → x₀ ≡ x₁
 i≡ {x₀} {x₁} = Σ≡Prop (λ _ → isProp× (isPropIsContinuous _) (isPropIsContinuous _))
  ∘ GroupIso≡ ∘ SetsIso≡fun isSetℝ isSetℝ


 Aut[_]ᵣ : Group₀
 Aut[_]ᵣ =
   makeGroup {G = contGroupIso}
     (idGroupIso , IsContinuousId , IsContinuousId)
     (λ (a , b , c) (a' , b' , c') →
       compGroupIso a a' , IsContinuous∘ _ _ b' b , IsContinuous∘ _ _ c c')
     (λ (a , b , c) → invGroupIso a , c , b)
     (isSetΣ (isSetΣ (isSet-SetsIso isSetℝ isSetℝ)
        (λ _ → isProp→isSet (isPropIsGroupHom _ _)))
         (λ _ → isProp→isSet (isProp× (isPropIsContinuous _) (isPropIsContinuous _))))
     (λ _ _ _ → i≡ refl)
          (λ _ → i≡ refl)
          (λ _ → i≡ refl)
          (λ ((x , _) , _) → i≡ (funExt (Iso.ret x)))
          (λ ((x , _) , _) → i≡ (funExt (Iso.sec x)))



open AutCont public using (Aut[_]ᵣ)

module +GrAutomorphism (A : ⟨ (Aut[ +Groupℝ ]) ⟩) where

 open IsGroupHom (snd A)
 open Iso (fst A)

 f-linℚ : ∀ x q → rat q ·ᵣ fun x ≡ fun (rat q ·ᵣ x)
 f-linℚ x = SQ.ElimProp.go w
  where

  w'' : ∀ x n → fromNat n ·ᵣ fun x ≡ fun (fromNat n ·ᵣ x)
  w'' x zero = Rℝ.0LeftAnnihilates _ ∙∙
    sym pres1 ∙∙ cong fun (sym (Rℝ.0LeftAnnihilates _))
  w'' x (suc n) = sym (x+n·x≡sn·x n (fun x)) ∙∙
     cong (fun x +ᵣ_) (w'' x n) ∙∙
      (sym (pres· _ _) ∙ cong fun (x+n·x≡sn·x n x))


  w' : ∀ n m → rat [ ℤ.pos m , (1+ n) ] ·ᵣ fun x ≡ fun (rat [ ℤ.pos m , (1+ n) ] ·ᵣ x)
  w' n m = cong₂ _·ᵣ_ (cong rat (ℚ.[/]≡· (ℤ.pos m) (1+ n))
      ∙ rat·ᵣrat _ _ ∙ ·ᵣComm  _ _)
    refl ∙
    (sym (·ᵣAssoc _ _ _) ∙
     cong (rat [ pos 1 / 1+ n ] ·ᵣ_)
       (w'' _ _)) ∙
        cong (rat [ pos 1 / 1+ n ] ·ᵣ_)
          (cong fun (cong (_·ᵣ x)
           (cong rat (sym (m·n/m n m)) ∙ rat·ᵣrat _ _)
           ∙ sym (·ᵣAssoc _ _ _)) ∙ sym (w'' _ _)) ∙ ·ᵣAssoc _ _ _
          ∙ cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)
           ∙ cong rat (ℚ.·Comm _ _
            ∙ sym (ℚ.[/]≡· (pos (suc n)) (1+ n)) ∙
            eq/ _ _ (ℤ.·Comm _ _))) refl ∙ ·IdLᵣ _


  w : ElimProp (λ z → rat z ·ᵣ fun x ≡ fun (rat z ·ᵣ x))
  w .ElimProp.isPropB _ = isSetℝ _ _
  w .ElimProp.f (pos m , (1+ n)) = w' n m
  w .ElimProp.f (ℤ.negsuc m , (1+ n)) =
    cong₂ _·ᵣ_ (cong rat (ℚ.-[/] _ _) ∙ sym (-ᵣ-rat _)) refl  ∙ (-ᵣ· _ _)
    ∙ cong -ᵣ_ (w' n (suc m)) ∙ sym (presinv _) ∙
     cong fun (sym (-ᵣ· _ _) ∙
       cong₂ _·ᵣ_ (-ᵣ-rat _ ∙ cong rat (sym (ℚ.-[/] _ _) )) refl)

 α : ℝ
 α = fun 1

 fun-rat : ∀ q → fun (rat q) ≡ rat q ·ᵣ α
 fun-rat q = cong fun (sym (·IdR _)) ∙ sym (f-linℚ 1 q)

 -- _ : {!!}
 -- _ = {!fun-rat 1!}

 Σfun' : Σ[ f' ∈ (ℝ → ℝ) ] ∃[ L ∈ ℚ₊ ] (Lipschitz-ℝ→ℝ L f')
 Σfun' = fromLipschitz' (fun ∘ rat)
  (PT.map
     (λ (δ , <δ , δ<) →
      let δ₊ = δ , <ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _
              (0≤absᵣ _) <δ)
      in δ₊ , λ q r ε x x₁ →
          let u = ℚ.absFrom<×< (fst ε) (q ℚ.- r) x x₁
          in invEq (∼≃abs<ε _ _ _)
                (isTrans≡<ᵣ _ _ _
                  (cong absᵣ (cong₂ _-ᵣ_ (fun-rat q) (fun-rat r)
                   ∙ sym (Rℝ.·DistL- _ _ _))
                    ∙ ·absᵣ _ _ ∙
                     ·ᵣComm _ _ ∙
                      cong (absᵣ α ·ᵣ_)
                      (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ-rat _ ) )
                  (isTrans≤<ᵣ _ _ _
                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-·ᵣo _ _ _
                        (≤ℚ→≤ᵣ _ _ (0≤abs _) )
                        (<ᵣWeaken≤ᵣ _ _ <δ))
                      (sym (rat·ᵣrat _ _)))
                    (<ℚ→<ᵣ _ _ (ℚ.<-o· _ _ _ (snd δ₊) u))))
         )
     (denseℚinℝ (absᵣ α) ((absᵣ α) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR (absᵣ α)))
         (<ᵣ-o+ 0 1 _ decℚ<ᵣ?))))


 fun' : ℝ → ℝ
 fun' = fst Σfun'

 fun'-cont : IsContinuous fun'
 fun'-cont = PT.rec
  (isPropIsContinuous _)
  (λ x → Lipschitz→IsContinuous _ _ (snd x))
  (snd Σfun')

 fun'· : ∀ x → fun' x ≡ x ·ᵣ α
 fun'· = ≡Continuous _ _ fun'-cont
   (IsContinuous·ᵣR α)
    λ q → fromLipschitz'-rat fun _ _ ∙ fun-rat q

 fun'-rat : ∀ x → fun' (rat x) ≡ fun (rat x)
 fun'-rat x = fun'· (rat x) ∙ sym (fun-rat x)



-- .Elimℝ-Prop2Sym.rat-ratA r q p =
--     let z = sym (fun'-rat r) ∙∙ p ∙∙ fun'-rat q
--     in isoFunInjective (fst A) _ _ z
--   w .Elimℝ-Prop2Sym.rat-limA = {!!}
--   w .Elimℝ-Prop2.lim-limA = {!!}
--   w .Elimℝ-Prop2.isPropA _ _ = isPropΠ λ _ → isSetℝ _ _

 -- fun'·-equiv : isEquiv fun'
 -- fun'·-equiv = isEmbedding×isSurjection→isEquiv {f = fun'}
 --  (fun-emb , {!!})

-- module +GrAutomorphism-Cont (A : ⟨ (Aut[ +Groupℝ ]) ⟩) where

--  module F = +GrAutomorphism A
--  module F' = +GrAutomorphism (invGroupIso A)

--  isom' : Iso ℝ ℝ
--  isom' .Iso.fun = F.fun'
--  isom' .Iso.inv = F'.fun'
--  isom' .Iso.sec = {!!}
--  -- ≡Continuous _ _
--  --   (IsContinuous∘ _ _ F.fun'-cont F'.fun'-cont) IsContinuousId
--  --     λ r → {!!}
--  isom' .Iso.ret = {!!}

--  α·α'≡1 : F'.α ·ᵣ F.α ≡ 1
--  α·α'≡1 = sym (F.fun'· _)
--   ∙  cong F.fun' (sym (·IdL _) ∙ sym (F'.fun'· _)) ∙ isom' .Iso.sec 1

--  g-linℚ : ∀ x q → rat q ·ᵣ g x ≡ g (rat q ·ᵣ x)
--  g-linℚ = {!!}


--  β = g 1


--  g-rat : ∀ q → g (rat q) ≡ rat q ·ᵣ β
--  g-rat q = cong g (sym (·IdR _)) ∙ sym (g-linℚ 1 q)


--  α·β=1 : α ·ᵣ β ≡ 1
--  α·β=1 =
--    let q : ℚ
--        q = {!!}
--        pp : {!!}
--        pp =     cong g {!f
--        !}
--                ∙ Iso.ret (fst A) (rat q)
--    in {!!}

--  -- f≠1 : f 1 ≡ 0 → ⊥
--  -- f≠1 p = {!inj-rat _ _
--  --   (isoFunInjective (fst A) _ _ (p ∙ sym (pres1)))!}

--  0<∣α∣ : 0 <ᵣ absᵣ α
--  0<∣α∣ = {! !}


-- --  _ : {!!}
-- --  _ = {!g (absᵣ α)!}


-- --  f-cont : IsContinuous f
-- --  f-cont u ε =
-- --   PT.map
-- --     {!!}
-- --     {!!}


Invlipschitz-ℝ→ℝ→injective-interval : ∀ K a b f →
 Invlipschitz-ℝ→ℝℙ K (intervalℙ a b) f
    → ∀ x x∈ y y∈ → f x x∈ ≡ f y y∈ → x ≡ y
Invlipschitz-ℝ→ℝ→injective-interval K a b f il x x∈ y y∈ =
 fst (∼≃≡ _ _) ∘
   (λ p ε → subst∼ (ℚ.y·[x/y] K (fst ε))
     (il x x∈ y  y∈ ((invℚ₊ K) ·₊ ε) (p (invℚ₊ K ·₊ ε))))
   ∘S invEq (∼≃≡ _ _)


intervalℙ→dist< : ∀ a b x y → x ∈ intervalℙ a b → y ∈ intervalℙ a b
                   → absᵣ (x -ᵣ y) ≤ᵣ b -ᵣ a
intervalℙ→dist< a b x y (a≤x , x≤b) (a≤y , y≤b) =
  isTrans≡≤ᵣ _ _ _ (abs-max _ ∙ cong (maxᵣ _) (-[x-y]≡y-x _ _) )
    (max≤-lem _ _ _ (≤ᵣMonotone+ᵣ _ _ _ _ x≤b (-ᵣ≤ᵣ _ _ a≤y))
                    ((≤ᵣMonotone+ᵣ _ _ _ _ y≤b (-ᵣ≤ᵣ _ _ a≤x))))



ℚ1≤x⊔1/x : ∀ x → 1 ℚ.≤ ℚ.max (fst x) (fst (invℚ₊ x))
ℚ1≤x⊔1/x x =
  ⊎.rec
     (λ 1≤x →
       ℚ.isTrans≤ _ _ _ 1≤x (ℚ.≤max (fst x) (fst (invℚ₊ x))) )
     (λ x<1 →
       ℚ.isTrans≤ _ _ _ (ℚ.invℚ≤invℚ 1 _
         (ℚ.<Weaken≤ _ _ x<1))
         (ℚ.≤max' (fst x) (fst (invℚ₊ x))))
   (ℚ.Dichotomyℚ 1 (fst x))


opaque
 unfolding maxᵣ
 1≤x⊔1/x : ∀ x → 1 ≤ᵣ maxᵣ (fst x) (fst (invℝ₊ x))
 1≤x⊔1/x =
   uncurry (<→≤ContPos'pred {0}
     (AsContinuousWithPred _ _
       (IsContinuousConst _))
        (contDiagNE₂WP maxR _ _ _
          (AsContinuousWithPred _ _
            IsContinuousId) IsContinuousWithPred-invℝ₊)
              λ u 0<u →
                subst (1 ≤ᵣ_) (sym (maxᵣ-rat _ _)
                  ∙ cong (maxᵣ (rat u))
                  (sym (invℝ'-rat _ _ _)
                   ∙ sym (cong fst (invℝ₊-impl (rat u , 0<u)))))
                  (≤ℚ→≤ᵣ _ _ (
                   (ℚ1≤x⊔1/x (u , <ᵣ→<ℚ _ _ 0<u)))))


ℚ1<x+1/x : ∀ x → 1 ℚ.< fst x ℚ.+ fst (invℚ₊ x)
ℚ1<x+1/x x =
 ⊎.rec
   (λ 1≤x →
     subst (ℚ._< (fst x ℚ.+ fst (invℚ₊ x)))
       (ℚ.+IdR 1)
       (ℚ.≤<Monotone+ 1 (fst x) 0 (fst (invℚ₊ x)) 1≤x (snd (invℚ₊ x))))
   (λ x<1 →
     ℚ.<WeakenNonNeg+ 1 (fst (invℚ₊ x)) (fst x)
       (subst (1 ℚ.<_) ℚ! (ℚ.invℚ<invℚ 1 x x<1))
       (ℚ.<Weaken≤ 0 (fst x) (snd x)))
   (ℚ.Dichotomyℚ 1 (fst x))
opaque
 unfolding _+ᵣ_
 1≤x+1/x : ∀ x → 1 ≤ᵣ fst x +ᵣ fst (invℝ₊ x)
 1≤x+1/x =
   uncurry (<→≤ContPos'pred {0}
     (AsContinuousWithPred _ _
       (IsContinuousConst _))
        (contDiagNE₂WP sumR _ _ _
          (AsContinuousWithPred _ _
            IsContinuousId) IsContinuousWithPred-invℝ₊)
              λ u 0<u →
                subst (1 ≤ᵣ_) (sym (+ᵣ-rat _ _)
                  ∙ cong (rat u +ᵣ_)
                  (sym (invℝ'-rat _ _ _)
                   ∙ sym (cong fst (invℝ₊-impl (rat u , 0<u)))))
                  (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ 1 _
                   (ℚ1<x+1/x (u , <ᵣ→<ℚ _ _ 0<u)))))

-- pasting : (x₀ : ℝ) → (f< : ∀ x → x ≤ᵣ x₀ → ℝ)
--                   → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
--                   → f< x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀)
--                   → Σ[ f ∈ (ℝ → ℝ) ]
--                         (∀ x x≤x₀ → f x ≡ f< x x≤x₀)
--                          × (∀ x x₀≤x → f x ≡ <f x x₀≤x)
-- pasting x₀ f< <f p =
--   (λ x → (<f (maxᵣ x₀ x) (≤maxᵣ _ _)
--       +ᵣ f< (minᵣ x₀ x) (min≤ᵣ _ _))
--        -ᵣ f< x₀ (≤ᵣ-refl x₀))
--   , (λ x x≤x₀ →
--       let z = minᵣComm _ _ ∙ ≤→minᵣ _ _ x≤x₀
--       in cong₂ _-ᵣ_ (cong₂ _+ᵣ_
--              (cong (uncurry <f) (Σ≡Prop (λ _ → isProp≤ᵣ _ _)
--                (maxᵣComm _ _ ∙ ?))) -- x≤x₀
--              (cong (uncurry f<) (Σ≡Prop (λ _ → isProp≤ᵣ _ _) z)) ) p ∙
--           L𝐑.lem--063)
--   , λ x x₀≤x →
--        Rℝ.plusMinus' _ _ _ (cong (uncurry f<)
--         (Σ≡Prop (λ _ → isProp≤ᵣ _ _) (≤→minᵣ _ _ x₀≤x))) ∙
--         (cong (uncurry <f)
--         (Σ≡Prop (λ _ → isProp≤ᵣ _ _) ?)) -- x₀≤x


-- pasting< : ∀ b x₀ b<x₀
--                   → (f< : ∀ x → b <ᵣ x → x ≤ᵣ x₀ → ℝ)
--                   → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
--                   → f< x₀ b<x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀)
--                   → Σ[ f ∈ (∀ x → b <ᵣ x → ℝ) ]
--                         (∀ x b<x x≤x₀ → f x b<x ≡ f< x b<x x≤x₀)
--                          × (∀ x b<x x₀≤x → f x b<x ≡ <f x x₀≤x)
-- pasting< b x₀ b<x₀ f< <f p =
--    ((λ x x< → (<f (maxᵣ x₀ x) (≤maxᵣ _ _)
--       +ᵣ f< (minᵣ x₀ x) (<min-lem _ _ _ b<x₀ x<) (min≤ᵣ _ _))
--        -ᵣ f< x₀ b<x₀ (≤ᵣ-refl x₀)))
--   , (λ x b<x x≤x₀ →
--       let z = minᵣComm _ _ ∙ ≤→minᵣ _ _ x≤x₀
--       in cong₂ _-ᵣ_ (cong₂ _+ᵣ_
--              (cong (uncurry <f) (Σ≡Prop (λ _ → isSetℝ _ _)
--                (maxᵣComm _ _ ∙ x≤x₀)))
--              (cong (uncurry (uncurry f<))
--                (Σ≡Prop (flip isProp≤ᵣ _ ∘ fst) (Σ≡Prop (isProp<ᵣ _) z)))
--              ) p ∙
--           L𝐑.lem--063)
--    , λ x b<x x₀≤x →
--      Rℝ.plusMinus' _ _ _ (cong (uncurry (uncurry f<))
--         (Σ≡Prop (λ (x , _) → isProp≤ᵣ x _) (Σ≡Prop (isProp<ᵣ _) (≤→minᵣ _ _ x₀≤x))) ) ∙
--        cong (uncurry <f) ((Σ≡Prop (λ _ → isSetℝ _ _) x₀≤x))



-- pasting≤ : ∀ b x₀ b≤x₀
--                   → (f< : ∀ x → b ≤ᵣ x → x ≤ᵣ x₀ → ℝ)
--                   → (<f : ∀ x → x₀ ≤ᵣ x → ℝ)
--                   → f< x₀ b≤x₀ (≤ᵣ-refl x₀) ≡ <f x₀ (≤ᵣ-refl x₀)
--                   → Σ[ f ∈ (∀ x → b ≤ᵣ x → ℝ) ]
--                         (∀ x b≤x x≤x₀ → f x b≤x ≡ f< x b≤x x≤x₀)
--                          × (∀ x b≤x x₀≤x → f x b≤x ≡ <f x x₀≤x)
-- pasting≤ b x₀ b≤x₀ f< <f p =
--   (λ x _ → (fst h) x)
--   , (λ x b≤x x≤x₀ → fst (snd h) x x≤x₀ ∙ q b≤x)
--   ,  const ∘ snd (snd h)
--  where

--  q : ∀ {y y' : Σ[ x ∈ ℝ ] (b ≤ᵣ x) × (x ≤ᵣ x₀)}
--          → (a : (fst y) ≡ (fst y')) → _ ≡ _
--  q {y} {y'} = cong {x = y} {y = y'} (uncurry $ uncurry ∘ f<) ∘
--          (Σ≡Prop (λ _ → isProp× (isSetℝ _ _) (isSetℝ _ _)))

--  h = pasting x₀
--        (λ x x≤x₀ → f< (maxᵣ b x) (≤maxᵣ _ _)
--          (max≤-lem _ _ _ b≤x₀ x≤x₀))
--        <f (q b≤x₀ ∙ p)


opaque
 unfolding _+ᵣ_
 slope-lower-bound : (z : ℝ₊) (B : ℚ₊) (1<z : 1 <ᵣ fst z) → (y₀ y₁ : ℚ )
   → (y₀<y₁ : y₀ ℚ.< y₁)
   → (y₀∈ : y₀ ∈ ℚ.ℚintervalℙ (ℚ.- (fst B)) (fst B))
   → (y₁∈ : y₁ ∈ ℚ.ℚintervalℙ (ℚ.- (fst B)) (fst B)) →
   fst (z ^ℚ (ℚ.- fst B)) ·ᵣ
        ((fst z -ᵣ 1) ／ᵣ₊ z)
       <ᵣ
   ((fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  y₀<y₁ ))
 slope-lower-bound z B 1<z y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
   isTrans<≡ᵣ _ _ _
     (≤<ᵣ₊Monotone·ᵣ
       ((z ^ℚ (ℚ.- (fst B)))) (fst (z ^ℚ y₀))
       (_ ,
         isTrans≡≤ᵣ _ _ _ (sym (Rℝ.0LeftAnnihilates _))
            (≤ᵣ-·ᵣo 0 _ _
             (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ (fst z , z .snd))))
              (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))))
               ((fst (z ^ℚ (fst h₊)) -ᵣ 1) ／ᵣ₊ ℚ₊→ℝ₊ h₊)

       (^ℚ-MonotoneR {z} (ℚ.- (fst B)) y₀ -B≤y₀ (<ᵣWeaken≤ᵣ _ _ 1<z))

        (invEq (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)
           brn )
        )
       (·ᵣAssoc _ _ _
        ∙ cong (_·ᵣ
         fst (invℝ₊ (ℚ₊→ℝ₊ h₊)))
          (sym (factor-xᵃ-xᵇ z _ _) ))

  where
   h₊ : ℚ₊
   h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁

   brn : fst (ℚ₊→ℝ₊ h₊) ·ᵣ (fst z -ᵣ 1)   <ᵣ
         fst z ·ᵣ (fst (z ^ℚ fst h₊) -ᵣ rat [ pos 1 / 1+ 0 ])

   brn = isTrans<≡ᵣ _ _ _ (a+c<b⇒a<b-c _ _ _ (isTrans≡<ᵣ _ _ _ (sym (·DistR+ (fst (ℚ₊→ℝ₊ h₊)) 1 _))
          (a+c<b⇒a<b-c _ _ 1
           (isTrans≡<ᵣ _ _ _
            (cong (λ t → t ·ᵣ (fst z -ᵣ 1) +ᵣ 1) (+ᵣ-rat (fst h₊) 1)
             ∙ +ᵣComm (rat (fst h₊ ℚ.+ [ pos 1 / 1+ 0 ]) ·ᵣ
       (fst z -ᵣ rat [ pos 1 / 1+ 0 ])) 1) (bernoulli's-ineq-^ℚ z (fst h₊ ℚ.+ 1)
             1<z (subst (1 ℚ.<_) (ℚ.+Comm 1 (fst h₊))
              (ℚ≤→<+₊ _ _ h₊ (ℚ.isRefl≤ 1))) )))))
             (sym (+ᵣAssoc (fst (z ^ℚ (fst h₊ ℚ.+ 1))) _ _) ∙
              cong₂ _+ᵣ_
                (cong fst (sym (^ℚ-+ z (fst h₊) 1))
                  ∙ ·ᵣComm _ _ ∙
                    cong (_·ᵣ (z ^ℚ fst h₊) .fst) (cong fst (^ℚ-1 _) ))
                ((sym (-ᵣDistr _ _) ∙
                  cong (-ᵣ_) (cong (1 +ᵣ_) (·IdLᵣ _)
                    ∙ (+ᵣComm 1 (fst z -ᵣ 1)
                      ∙ sym (+ᵣAssoc (fst z) (-ᵣ 1) 1)
                      ∙ cong (fst z +ᵣ_) (+ᵣComm (-ᵣ 1) 1 ∙ +-ᵣ 1)
                      ∙ +IdR (fst z))
                    ∙ sym (·IdLᵣ _)))
                  ∙ sym (-ᵣ· _ _) ∙ ·ᵣComm _ _)
               ∙ sym (·DistL+ _ _ _) )


slope-upper-bound : (z : ℝ₊) (B : ℚ₊) → (y₀ y₁ : ℚ )
  → (y₀<y₁ : y₀ ℚ.< y₁)
  → (y₀∈ : y₀ ∈ ℚ.ℚintervalℙ (ℚ.- (fst B)) (fst B))
  → (y₁∈ : y₁ ∈ ℚ.ℚintervalℙ (ℚ.- (fst B)) (fst B)) →
  ((fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
    ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ _ _  y₀<y₁ ))
     ≤ᵣ fst (z ^ℚ (fst B)) ·ᵣ (fst z -ᵣ 1)
slope-upper-bound z B y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
  isTrans≤≡ᵣ _ _ _
    (slope-monotone z
      y₀ y₁ (fst B) (fst B ℚ.+ 1)
       y₀<y₁ B<B+1 y₀≤B
         (ℚ.isTrans≤ _ _ _ y₁≤B (ℚ.<Weaken≤ _ _ B<B+1))
         )
     (Rℝ.·IdR' _ _ (cong (fst ∘ invℝ₊)
       (ℝ₊≡ (cong rat ℚ!)) ∙ cong fst invℝ₊1) ∙
        factor-xᵃ-xᵇ z (fst B ℚ.+ 1) (fst B) ∙
          cong (λ u → fst (z ^ℚ fst B) ·ᵣ (fst u -ᵣ 1))
           (cong (z ^ℚ_) ℚ! ∙ ^ℚ-1 z))

 where
  h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁
  B<B+1 = ℚ≤→<+₊ _ _ 1 (ℚ.isRefl≤ (fst B))


-- -- lowBnd-1/ℕ : (ε : ℝ₊) → ∃[ k ∈ ℕ₊₁ ] rat [ 1 / k ] <ᵣ fst ε
-- -- lowBnd-1/ℕ = {!!}


-- -- ceilℚ₊ q = 1+ (fst (fst (floor-fracℚ₊ q))) ,
-- --    subst2 (_<_) --  (fromNat (suc (fst (fst (floor-fracℚ₊ q)))))
-- --       (ℚ.+Comm _ _ ∙ fst (snd (floor-fracℚ₊ q)))
-- --       (ℚ.ℕ+→ℚ+ _ _)
-- --        (<-+o _ _ (fromNat (fst (fst (floor-fracℚ₊ q))))
-- --          (snd (snd (snd (floor-fracℚ₊ q)))))


slUpBd : ℕ → ℕ → ℚ₊
slUpBd Z m = (ℚ._ℚ₊^ⁿ_ (fromNat (suc (suc Z))) (suc m)) ·₊ fromNat (suc Z)



monotone^ℚ' : ∀ q q' q''
 → q ℚ.≤ q'
 → q' ℚ.≤ q''
 → ∀ u 0<u
 → minᵣ (fst ((rat u , 0<u) ^ℚ q)) (fst ((rat u , 0<u) ^ℚ q'')) ≤ᵣ
   fst ((rat u , 0<u) ^ℚ q')
monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u =
 ⊎.rec
   (λ 1≤u →
     isTrans≤ᵣ _ _ _ (min≤ᵣ (fst ((rat u , 0<u) ^ℚ q))
            (fst ((rat u , 0<u) ^ℚ q'')))
        (^ℚ-MonotoneR {(rat u , 0<u)} q q'
           q≤q'
        (≤ℚ→≤ᵣ _ _ 1≤u)))
   (λ u<1 → isTrans≤ᵣ _ _ _
     (min≤ᵣ' (fst ((rat u , 0<u) ^ℚ q))
            (fst ((rat u , 0<u) ^ℚ q'')))
       let xx = (^ℚ-MonotoneR {invℝ₊ (rat u , 0<u)}
               _ _  (ℚ.minus-≤ _ _ q'≤q'')
                   (isTrans≤≡ᵣ _ _ _
                    (invEq (z≤x/y₊≃y₊·z≤x 1 1 (rat u , 0<u))
                      (isTrans≡≤ᵣ _ _ _ (·IdR _)
                        (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ u<1))))
                    (·IdLᵣ _)))
       in subst2 _≤ᵣ_
            (cong fst (sym (^ℚ-minus _ _)))
            (cong fst (sym (^ℚ-minus _ _)))
            xx)
   (ℚ.Dichotomyℚ 1 u)


opaque
 unfolding minᵣ
 monotone^ℚ : ∀ q q' q''
  → q ℚ.≤ q'
  → q' ℚ.≤ q''
  → ∀ z
  → minᵣ (fst (z ^ℚ q)) (fst (z ^ℚ q'')) ≤ᵣ fst (z ^ℚ q')
 monotone^ℚ q q' q'' q≤q' q'≤q'' =
   uncurry (<→≤ContPos'pred {0}
     (contDiagNE₂WP minR _ _ _
       (IsContinuous^ℚ q)
       (IsContinuous^ℚ q''))
     (IsContinuous^ℚ q')
     λ u 0<u → monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u)

-- module BDL (z : ℝ₊) (Z : ℕ)
--           (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
--           (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ]  ≤ᵣ fst z)
--           -- (1+1/Z<z : rat (1 ℚ.+ [ 1 / 1+ (suc Z) ]) ≤ᵣ fst z )
--            where


-- bdl' : 1 ≤ᵣ fst z → boundedLipschitz (fst ∘ z ^ℚ_) (slUpBd Z)
-- bdl' 1≤z n = ℚ.elimBy≡⊎<
--  (λ x y X y∈ x∈ → subst2 _≤ᵣ_
--       (minusComm-absᵣ _ _)
--       (cong (rat ∘ (fst (slUpBd Z n) ℚ.·_)) (ℚO.abs-Comm _ _))
--       (X x∈ y∈)  )
--  (λ x _ _ → subst2 _≤ᵣ_
--     (cong absᵣ (sym (+-ᵣ _)))
--     (cong rat (sym (𝐐'.0RightAnnihilates' _ _ (cong ℚ.abs (ℚ.+InvR x)))))
--     (≤ᵣ-refl 0))
--  λ y₀ y₁ y₀<y₁ y₀∈ y₁∈ →
--   isTrans≡≤ᵣ _ _ _ (absᵣNonNeg _ (x≤y→0≤y-x _ _
--         (^ℚ-MonotoneR _ _ (ℚ.<Weaken≤ _ _ y₀<y₁) 1≤z )))
--     (isTrans≤≡ᵣ _ _ _ (isTrans≤ᵣ _ _ _ (
--    (fst (z/y≤x₊≃z≤y₊·x _ _ _) (slope-upper-bound z (fromNat (suc n))
--    y₀ y₁ y₀<y₁
--     (ℚ.absTo≤×≤ (fromNat (suc n)) y₀ y₀∈)
--     (ℚ.absTo≤×≤ (fromNat (suc n)) y₁ y₁∈))))
--      (≤ᵣ-o· _ _ _ (ℚ.<Weaken≤ 0 _ (ℚ.-< _ _ y₀<y₁))
--       (≤ᵣ₊Monotone·ᵣ _ _ _ _
--         (<ᵣWeaken≤ᵣ _ _ $ snd (fromNat (suc (suc Z)) ^ℚ fst (fromNat (suc n))))
--         (x≤y→0≤y-x _ _ 1≤z)
--         (^ℚ-Monotone {y = fromNat (suc (suc Z))}
--          (fromNat (suc n)) z≤Z)
--         (≤ᵣ-+o _ _ (-1) z≤Z))))
--      (·ᵣComm _ _ ∙
--       cong₂ (_·ᵣ_)
--         (cong₂ (_·ᵣ_) (^ⁿ-ℚ^ⁿ _ _) (cong rat (ℚ.ℤ+→ℚ+ _ _))
--          ∙ sym (rat·ᵣrat _ _) )
--         (cong rat (sym (ℚO.0<→abs≡id _ (ℚ.-< _ _ y₀<y₁))))
--        ∙ sym (rat·ᵣrat _ _)))



-- --  slUpBdInv : ℕ → ℚ₊
-- --  slUpBdInv m = (fromNat (suc (suc Z))) ℚ₊^ⁿ (suc (suc (suc m)))
-- --      -- ℚ₊· ((invℚ₊ (fromNat (suc (suc Z)))) ℚ₊· invℚ₊ (fromNat (suc (suc Z))))
-- -- -- ((fst z -ᵣ 1) ／ᵣ₊ z)

--  -- slpBdIneq : ∀ n → fst (invℚ₊ (slUpBdInv n)) ℚ.≤
--  --    fst (slUpBd n)
--  -- slpBdIneq n = ℚ.isTrans≤ _ 1 _
--  --   (fst (ℚ.invℚ₊-≤-invℚ₊ 1 _)
--  --     (ℚ.1≤x^ⁿ (fromNat (suc (suc Z)))
--  --          (suc (suc (suc n)))
--  --          (≤ℤ→≤ℚ 1 (pos (suc (suc Z)))
--  --            (ℤ.suc-≤-suc {0} {pos (suc Z)}
--  --             (ℤ.zero-≤pos {suc Z})))))
--  --   (ℚ.≤Monotone·-onNonNeg 1 _ 1 _
--  --    ((ℚ.1≤x^ⁿ (fromNat (suc (suc Z)))
--  --          ((suc n))
--  --          (≤ℤ→≤ℚ 1 (pos (suc (suc Z)))
--  --            (ℤ.suc-≤-suc {0} {pos (suc Z)}
--  --             (ℤ.zero-≤pos {suc Z})))))
--  --    ((≤ℤ→≤ℚ 1 (pos (suc Z))
--  --            (ℤ.suc-≤-suc {0} {pos Z}
--  --             (ℤ.zero-≤pos {Z}))))
--  --    (ℚ.decℚ≤? {0} {1})
--  --    (ℚ.decℚ≤? {0} {1}))

-- --  1<z : 1 <ᵣ (fst z)
-- --  1<z = isTrans<ᵣ _ _ _ (<ℚ→<ᵣ _ _ (ℚ.<+ℚ₊' _ _ _ (ℚ.isRefl≤ 1))) 1+1/Z<z


-- clampᵣ₊ : ℝ₊ → ℝ₊ → ℝ₊ → ℝ₊
-- clampᵣ₊ d u x = minᵣ₊ (maxᵣ₊ d x) u

isIncrasingℙᵣ : (P : ℙ ℝ) → (∀ (x : ℝ) → x ∈ P → ℝ) → Type
isIncrasingℙᵣ P f =
 ∀ (x : ℝ) (x∈ : x ∈ P) (y : ℝ) (y∈ : y ∈ P) → x <ᵣ y → f x x∈ <ᵣ f y y∈


isNondecrasingℙᵣ : (P : ℙ ℝ) → (∀ (x : ℝ) → x ∈ P → ℝ) → Type
isNondecrasingℙᵣ P f =
 ∀ (x : ℝ) (x∈ : x ∈ P) (y : ℝ) (y∈ : y ∈ P) → x ≤ᵣ y → f x x∈ ≤ᵣ f y y∈

opaque
 unfolding minᵣ maxᵣ
 ∈interval→≤ContPos'pred : {x₀ x₁ : ℚ} → (x₀ ℚ.≤ x₁)
          → {f₀ f₁ : ∀ x → x ∈ intervalℙ (rat x₀) (rat x₁)   → ℝ}
          → IsContinuousWithPred (intervalℙ (rat x₀) (rat x₁)) f₀
          → IsContinuousWithPred (intervalℙ (rat x₀) (rat x₁)) f₁
          → (∀ u x₀<u<x₁ → f₀ (rat u) x₀<u<x₁
                     ≤ᵣ f₁ (rat u) x₀<u<x₁ )
              → ∀ x x₀<x<x₁ → f₀ x x₀<x<x₁ ≤ᵣ f₁ x x₀<x<x₁
 ∈interval→≤ContPos'pred {x₀} {x₁} x₀≤x₁ {f₀} {f₁} f₀C f₁C X x (≤x , x≤) =
   subst (λ (u , u∈) → f₀ u u∈ ≤ᵣ f₁ u u∈)
    (Σ≡Prop (∈-isProp ((intervalℙ (rat x₀) (rat x₁))))
      (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ (≤x , x≤))))
    $ ≤Cont
      {λ x → f₀ (clampᵣ (rat x₀) (rat x₁) x)
        (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ _ _ x₀≤x₁) _)}
      {λ x → f₁ (clampᵣ (rat x₀) (rat x₁) x)
       ((clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ _ _ x₀≤x₁) _))}
      (IsContinuousWithPred∘IsContinuous _ _ _
          _ f₀C (IsContinuousClamp (rat x₀) (rat x₁)))
      (IsContinuousWithPred∘IsContinuous _ _ _
          _ f₁C (IsContinuousClamp (rat x₀) (rat x₁)))
      (λ u →
        let
          I = intervalℙ (rat x₀) (rat x₁)
          cl∈ = clampᵣ∈ℚintervalℙ (rat x₀) (rat x₁) (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) (rat u)
          cl≡ = clampᵣ-rat x₀ x₁ u
        in subst (λ (v , v∈) → f₀ v v∈ ≤ᵣ f₁ v v∈)
             (Σ≡Prop (∈-isProp I) (sym cl≡))
             (X (ℚ.clamp x₀ x₁ u) (subst (_∈ I) cl≡ cl∈)))
      x
