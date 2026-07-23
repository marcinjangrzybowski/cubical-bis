module Cubical.HITs.CauchyReals.Analysis.Continuity.AdditiveAutomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Extension
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness using (ℝ₋₊)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict using (<ᵣ-o+)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties


module AutCont (Gstr : GroupStr ℝ) where

  open GroupStr Gstr

  Ĝ : Group₀
  Ĝ = ℝ , Gstr

  contGroupIso : Type
  contGroupIso = Σ (GroupIso Ĝ Ĝ) λ x →
    IsContinuous (Iso.fun (fst x)) × IsContinuous (Iso.inv (fst x))

  i≡ : ∀ {x₀ x₁ : contGroupIso} →
    Iso.fun (fst (fst x₀)) ≡ Iso.fun (fst (fst x₁)) → x₀ ≡ x₁
  i≡ {x₀} {x₁} =
    Σ≡Prop (λ _ →
      isProp× (isPropIsContinuous _) (isPropIsContinuous _))
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
        (λ _ → isProp→isSet
          (isProp× (isPropIsContinuous _) (isPropIsContinuous _))))
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

    w' : ∀ n m →
      rat [ ℤ.pos m , (1+ n) ] ·ᵣ fun x ≡
      fun (rat [ ℤ.pos m , (1+ n) ] ·ᵣ x)
    w' n m =
      cong₂ _·ᵣ_
        (cong rat (ℚ.[/]≡· (ℤ.pos m) (1+ n))
          ∙ rat·ᵣrat [ ℤ.pos m / 1 ] [ pos 1 / 1+ n ]
          ∙ ·ᵣComm (rat [ ℤ.pos m / 1 ]) (rat [ pos 1 / 1+ n ]))
        refl
      ∙ (sym (·ᵣAssoc _ _ _)
        ∙ cong (rat [ pos 1 / 1+ n ] ·ᵣ_) (w'' x m))
      ∙ cong (rat [ pos 1 / 1+ n ] ·ᵣ_)
        (cong fun
          (cong (_·ᵣ x)
            (cong rat (sym (ℚ.[c/1]·[n/c]≡[n/1] (1+ n) m))
              ∙ rat·ᵣrat
                [ pos (suc n) / 1 ]
                [ ℤ.pos m / 1+ n ])
            ∙ sym (·ᵣAssoc
              (fromNat (suc n))
              (rat [ ℤ.pos m / 1+ n ])
              x))
          ∙ sym (w'' (rat [ ℤ.pos m / 1+ n ] ·ᵣ x) (suc n)))
        ∙ ·ᵣAssoc _ _ _
        ∙ cong₂ _·ᵣ_
          (sym (rat·ᵣrat
            [ pos 1 / 1+ n ]
            [ pos (suc n) / 1 ])
          ∙ cong rat
            (ℚ.·Comm [ pos 1 / 1+ n ] [ pos (suc n) / 1 ]
            ∙ sym (ℚ.[/]≡· (pos (suc n)) (1+ n))
            ∙ eq/
              (pos (suc n) , 1+ n)
              (pos 1 , 1)
              (ℤ.·Comm (pos (suc n)) (pos 1))))
          refl
        ∙ ·IdLᵣ _

    w : ElimProp (λ z → rat z ·ᵣ fun x ≡ fun (rat z ·ᵣ x))
    w .ElimProp.isPropB _ = isSetℝ _ _
    w .ElimProp.f (pos m , (1+ n)) = w' n m
    w .ElimProp.f (ℤ.negsuc m , (1+ n)) =
      cong₂ _·ᵣ_ (cong rat (ℚ.-[/] _ _) ∙ sym (-ᵣ-rat _)) refl
      ∙ (-ᵣ· _ _)
      ∙ cong -ᵣ_ (w' n (suc m))
      ∙ sym (presinv _)
      ∙ cong fun
        (sym (-ᵣ· _ _)
        ∙ cong₂ _·ᵣ_ (-ᵣ-rat _ ∙ cong rat (sym (ℚ.-[/] _ _))) refl)

  α : ℝ
  α = fun 1

  fun-rat : ∀ q → fun (rat q) ≡ rat q ·ᵣ α
  fun-rat q = cong fun (sym (·IdR _)) ∙ sym (f-linℚ 1 q)

  Σfun' : Σ[ f' ∈ (ℝ → ℝ) ] ∃[ L ∈ ℚ₊ ] (Lipschitz-ℝ→ℝ L f')
  Σfun' = fromLipschitz' (fun ∘ rat)
    (PT.map
      (λ (δ , <δ , δ<) →
        let δ₊ : ℚ₊
            δ₊ = δ , <ᵣ→<ℚ _ _
              (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) <δ)

            lip : Lipschitz-ℚ→ℝ δ₊ (fun ∘ rat)
            lip q r ε -ε<q-r q-r<ε =
              let u = ℚ.absFrom<×< (fst ε) (q ℚ.- r) -ε<q-r q-r<ε
              in invEq (∼≃abs<ε _ _ _)
                (isTrans≡<ᵣ _ _ _
                  (cong absᵣ
                    (cong₂ _-ᵣ_ (fun-rat q) (fun-rat r)
                    ∙ sym (Rℝ.·DistL- _ _ _))
                  ∙ ·absᵣ _ _
                  ∙ ·ᵣComm _ _
                  ∙ cong (absᵣ α ·ᵣ_)
                    (cong absᵣ (-ᵣ-rat₂ q r) ∙ absᵣ-rat (q ℚ.- r)))
                  (isTrans≤<ᵣ _ _ _
                    (isTrans≤≡ᵣ _ _ _
                      (≤ᵣ-·ᵣo _ _ _
                        (≤ℚ→≤ᵣ _ _ (0≤abs (q ℚ.- r)))
                        (<ᵣWeaken≤ᵣ _ _ <δ))
                      (sym (rat·ᵣrat _ _)))
                    (<ℚ→<ᵣ _ _ (ℚ.<-o· _ _ _ (snd δ₊) u))))
        in δ₊ , lip)
      (denseℚinℝ (absᵣ α) (absᵣ α +ᵣ 1)
        (isTrans≡<ᵣ _ _ _
          (sym (Rℝ.+IdR (absᵣ α)))
          (<ᵣ-o+ 0 1 _ decℚ<ᵣ?))))

  fun' : ℝ → ℝ
  fun' = fst Σfun'

  fun'-cont : IsContinuous fun'
  fun'-cont = PT.rec
    (isPropIsContinuous _)
    (λ x → Lipschitz→IsContinuous (fst x) fun' (snd x))
    (snd Σfun')

  fun'· : ∀ x → fun' x ≡ x ·ᵣ α
  fun'· = ≡Continuous _ _ fun'-cont (IsContinuous·ᵣR α)
    λ q → fromLipschitz'-rat fun _ _ ∙ fun-rat q

  fun'-rat : ∀ x → fun' (rat x) ≡ fun (rat x)
  fun'-rat x = fun'· (rat x) ∙ sym (fun-rat x)

scalarAdditiveAutomorphism : ℝ₋₊ → Aut[ snd +Groupℝ ]ᵣ .fst
scalarAdditiveAutomorphism (α , 0＃α) =
  (i , makeIsGroupHom λ x y → ·DistR+ x y α) ,
  IsContinuous·ᵣR α , IsContinuous·ᵣR (invℝ α 0＃α)
  where
  i : Iso ℝ ℝ
  i .Iso.fun = _·ᵣ α
  i .Iso.inv = _·ᵣ invℝ α 0＃α
  i .Iso.sec x = [x/y]·yᵣ x α 0＃α
  i .Iso.ret x = [x·y]/yᵣ x α 0＃α

automorphismScalar : Aut[ snd +Groupℝ ]ᵣ .fst → ℝ
automorphismScalar a = Iso.fun (fst (fst a)) 1

automorphismActsByScalar :
  (a : Aut[ snd +Groupℝ ]ᵣ .fst) →
  ∀ x → x ·ᵣ automorphismScalar a ≡ Iso.fun (fst (fst a)) x
automorphismActsByScalar a =
  ≡Continuous _ _
    (IsContinuous·ᵣR (automorphismScalar a))
    (fst (snd a))
    (sym ∘ +GrAutomorphism.fun-rat (fst a))
