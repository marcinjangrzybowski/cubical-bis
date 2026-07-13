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
open import Cubical.HITs.CauchyReals.ContinuousOrder
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
   uncurry (continuousOpenLowerComparison {0}
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
   uncurry (continuousOpenLowerComparison {0}
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
   uncurry (continuousOpenLowerComparison {0}
     (contDiagNE₂WP minR _ _ _
       (IsContinuous^ℚ q)
       (IsContinuous^ℚ q''))
     (IsContinuous^ℚ q')
     λ u 0<u → monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u)
