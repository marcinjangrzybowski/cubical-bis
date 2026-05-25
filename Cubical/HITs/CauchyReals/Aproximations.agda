module Cubical.HITs.CauchyReals.Aproximations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

import Cubical.Functions.Logic as L


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
import Cubical.Data.Fin as F
open import Cubical.Data.Int.Fast as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Data.NatPlusOne


open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.CommRing.Instances.Int.Fast
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Algebra.Ring.BigOps
import Cubical.Data.FinData as FD

open import Cubical.HITs.PropositionalTruncation.MagicTrick
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.HITs.CauchyReals.RationalsImports 
open import Cubical.HITs.CauchyReals.Sequence 


open ℚ using (_⁻¹₊)


open import Cubical.Tactics.CommRingSolver.Specialised.Reals


digits : ℕ → ℚ → ℕ × ℕ
digits N q =
  ℤ.abs (integralPart) , ℤ.abs (Ffp.integralPart)
 where
 open ℚ.Floor (ℚ.floorℚ q)
 module Ffp = ℚ.Floor (ℚ.floorℚ ([ pos (10 ℕ.^ N) / 1 ] ℚ.· fst fractionalPart))


open import Cubical.HITs.CauchyReals.LiftingExpr

Approx : ℝ → Type
Approx x = (ε : ℚ₊) → ∃[ m ∈ ℚ ] (rat m ∼[ ε ] x)

Approx≤ : ℝ → Type
Approx≤ x = (ε : ℚ₊) → ∃[ m ∈ ℚ ] (absᵣ (rat m -ᵣ x) ≤ᵣ rat (fst ε))

module WithConvexParam (α β : ℚ₊) (is-convex : ⟨ α ⟩₊ ℚ.+ ⟨ β ⟩₊ ≡ 1) where



   
 
  ∃approx' : (x : ℝ) → Approx x
  ∃approx' = Elimℝ-Prop.go w where
   open Elimℝ-Prop
   w : Elimℝ-Prop (λ z → (ε : ℚ₊) → ∃-syntax ℚ (λ m → rat m ∼[ ε ] z))
   w .ratA _ _ = ∣ _ , refl∼ _ _ ∣₁
   w .limA x xc IH ε  = do
    (m , ιm≈xβε) ← IH (β ·₊ ε) (α ·₊ ε)
    let
     αε+βε≡ε : ⟨ α ·₊ ε +₊ β ·₊ ε ⟩₊ ≡ ⟨ ε ⟩₊
     αε+βε≡ε = sym (ℚ.·DistR+ ⟨ α ⟩₊ ⟨ β ⟩₊ ⟨ ε ⟩₊)
               ∙∙ cong (ℚ._· ⟨ ε ⟩₊) is-convex
               ∙∙ ℚ.·IdL ⟨ ε ⟩₊
     ιm≈lim = subst∼ αε+βε≡ε
       (𝕣-lim _ _ _ _ _ ιm≈xβε) 
    return (m , ιm≈lim)
   
   w .isPropA _ = isPropΠ λ _ → squash₁


  open Recover (ℚ , 0) (isHomogeneousDiscrete discreteℚ) using () renaming
    (RecoveredFrom to RecoveredApprox ; recover to recoverℚ)

  _🪄'_ : ℝ → ℚ₊ → Type
  x 🪄' ε = RecoveredApprox (PT.map fst (∃approx' x ε))
  
  getApproxVal' : ∀ x ε → x 🪄' ε 
  getApproxVal' x ε = recoverℚ (PT.map fst (∃approx' x ε))



  toApprox≤ : ∀ x → ((Σ[ q ∈ ℚ ] (rat q ≡ x)) ⊎ Approx≤ x) → Approx≤ x
  toApprox≤ x (inl (q , p)) ε = ∣ q , <ᵣWeaken≤ᵣ  _ _ (fst  (eqℝ≃< _ _) p ε)   ∣₁
  toApprox≤ x (inr x₁) ε = x₁ ε

  colapseApprox : ∀ x → ℚ₊ → ∥ (Σ[ q ∈ ℚ ] (rat q ≡ x)) ⊎ Approx≤ x ∥₁ → ∥ Bool × ℚ ∥₁ 
  colapseApprox x ε = PT.rec squash₁
    (⊎.rec (∣_∣₁ ∘ (true ,_) ∘ fst) λ A → PT.map ((false ,_) ∘ fst) (A ε) )
      
  ∃[rat⊎approx] : (x : ℝ) → ∥ (Σ[ q ∈ ℚ ] (rat q ≡ x)) ⊎ Approx≤ x ∥₁
  ∃[rat⊎approx] = Elimℝ-Prop.go w where
   open Elimℝ-Prop
   w : Elimℝ-Prop _
   w .ratA q = ∣ inl (q , refl) ∣₁
   w .limA x p IH = ∣ (inr h) ∣₁
     
    where
     h' : ∀ ε → ∃ ℚ (λ m → absᵣ (rat m -ᵣ lim x p) ≤ᵣ rat (fst ε))
     h' ε = do 
       ih ← (IH (β ·₊ ε))
       (m , ιm≈xβε) ← toApprox≤ _ ih (α ·₊ ε)
       
       let
        αε+βε≡ε : ⟨ α ·₊ ε +₊ β ·₊ ε ⟩₊ ≡ ⟨ ε ⟩₊
        αε+βε≡ε = sym (ℚ.·DistR+ ⟨ α ⟩₊ ⟨ β ⟩₊ ⟨ ε ⟩₊)
                  ∙∙ cong (ℚ._· ⟨ ε ⟩₊) is-convex
                  ∙∙ ℚ.·IdL ⟨ ε ⟩₊
        zz : absᵣ (x (β ·₊ ε) -ᵣ lim x p) ≤ᵣ rat (fst (β ·₊ ε))                  
        zz = x<y+δ→x≤y _ _ λ δ →
               isTrans<≡ᵣ _ _ _
                 (fst (∼≃abs<ε _ _ _) (𝕣-lim-self x p (β ·₊ ε) δ))
                 (sym (+ᵣ-rat _ _))
        zzz : absᵣ (rat m -ᵣ x (β ·₊ ε)) ≤ᵣ rat (fst (α ·₊ ε))
        zzz = ιm≈xβε
        
       return (m , isTrans≤≡ᵣ _ _ _
          (isTrans≤ᵣ _ _ _ (
            isTrans≡≤ᵣ _ _ _
              (cong absᵣ ℝ!) (absᵣ-triangle _ _))
            (≤ᵣMonotone+ᵣ _ _ _ _ zzz zz))
         (+ᵣ-rat _ _ ∙ cong rat (αε+βε≡ε)))
     
     h : Approx≤ (lim x p)
     h ε = PT.rec squash₁ (⊎.rec (∣_∣₁ ∘ map-snd λ a≡x →
        x<y+δ→x≤y _ _
          λ δ →
           let y = subst (_∼[ ε +₊ δ ] lim x p) (sym a≡x) (𝕣-lim-self x p ε δ)
           in isTrans<≡ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) y) (sym (+ᵣ-rat _ _))  )
         λ _ → h' ε)
       (IH ε)
   w .isPropA _ = squash₁


  open Recover (Bool × ℚ , (false , 0))
     (isHomogeneousDiscrete (discreteΣ 𝟚._≟_ λ _ → discreteℚ)) using () renaming
    (RecoveredFrom to RecoveredApprox⊎ ; recover to recover⊎)


  getApproxVal'⊎ : ∀ x ε → 
     RecoveredApprox⊎ (colapseApprox x ε (∃[rat⊎approx] x))
  getApproxVal'⊎ x ε = recover⊎ (colapseApprox x ε (∃[rat⊎approx] x))



  open Recover (ℕ × ℕ , (0 , 0))
     (isHomogeneousDiscrete (discreteΣ discreteℕ λ _ → discreteℕ)) using () renaming
    (RecoveredFrom to RecoveredApproxDigits ; recover to recoverDigits)

  _d🪄'_ : ℝ → ℕ → Type
  x d🪄' N = RecoveredApproxDigits ((PT.map (digits N ∘ fst) (∃approx' x ([ 1 / 10 ]₊ ℚ.ℚ₊^ⁿ (N)))))
  
  digitsℝ' : (x : ℝ) → (N : ℕ)
    → x d🪄' N
  digitsℝ' x N = recoverDigits (PT.map (digits N ∘ fst) (∃approx' x ([ 1 / 10 ]₊ ℚ.ℚ₊^ⁿ (N))))
  
open WithConvexParam [ 1 / 2 ]₊ [ 1 / 2 ]₊ (eq/ _ _ refl) using ()
 renaming (∃approx' to ∃approx ; getApproxVal' to getApproxVal ; getApproxVal'⊎ to getApproxVal⊎
           ; digitsℝ' to digitsℝ ; _d🪄'_ to _d🪄_ ; _🪄'_ to _🪄_)
   public


-- module _ x y x' y' (_ : lim x y ≡ lim x' y') where
--  opaque
--   unfolding _·ᵣ_

--   -- _ : ℝ
--   -- _ = {!lim x y ·ᵣ lim x' y'!}

multByℚ : ∀ q x y → singl (rat q ·ᵣ lim x y)
multByℚ q x y = 
  lim x' y' , x=x'

  where
   L : ℚ
   L = ℚ.max 1 (abs q)
   
   opaque
    1≤L : 1 ℚ.≤ L
    1≤L = ℚ.≤max 1 (abs q)
    0<L : 0 ℚ.< L
    0<L = ℚ.isTrans<≤ 0 _ _ (ℚ.pos<pos tt) 1≤L

   1/L : ℚ₊
   1/L = (L , 0<L) ℚ.⁻¹₊

   x' : ℚ₊ → ℝ
   x' ε = x (ε ℚ.₊／₊ (L , 0<L))
   opaque
    y' : (δ ε : ℚ₊) → x' δ ∼[ δ +₊ ε ] x' ε
    y' δ ε = 
      ∼-monotone≤ ( subst2 ℚ._≤_ ℚ!! (
           ℚ!!
         ∙ (Rℚ.·IdR' ((δ +₊ ε) .fst) _ (ℚ.⁻¹inverse (L , 0<L))))
                 (ℚ.≤-o· _ _ (fst 1/L)
                  (ℚ.<Weaken≤ _ _ (snd 1/L)) h) )
        (y (δ ℚ.₊／₊ (L , 0<L)) (ε ℚ.₊／₊ (L , 0<L)))
     where
      h :  (fst δ ℚ.+ fst ε) ℚ.· 1 ℚ.≤
              (fst δ ℚ.+ fst ε) ℚ.· L
      h = ℚ.≤-o· 1 L (fst δ ℚ.+ fst ε) (ℚ.0≤ℚ₊ (δ +₊ ε)) 1≤L

    -- fromC· : Unit
    -- fromC· = {!!}
    -- -- 
   
    x=x' : rat q ·ᵣ lim x y ≡ lim x' y'
    x=x' = eqℝ _ _ $ λ ε → PT.rec (isProp∼ _ _ _) (idfun _)
       do (δ , Δ) ← IsContinuous·ᵣL (rat q) (lim x y) (ε /4₊)
          (δ' , Δ') ← IsContinuous·ᵣL (rat q) (lim x' y') (ε /4₊)
          ∣ subst∼ {!!}
            (triangle∼  (Δ (x (δ /2₊))
               (subst∼ ℚ!! $
                sym∼ _ _ _ (𝕣-lim-self x y (δ /2₊) (δ /2₊))))
                 (triangle∼ {ε = {!!}} 
                   {!Δ' ? ?!}
                   (𝕣-lim-self x' y' (ε /2₊ /4₊) (ε /2₊ /4₊))
                   -- (sym∼ _ _ _ $
                   --   Δ' (x' (δ' /2₊)) (subst∼ {!!} $
                   --  (sym∼ _ _ _ $
                   --    𝕣-lim-self x' y' (δ' /2₊) (δ' /2₊))))
                      )) ∣₁
      -- λ ε → PT.rec {!!} {!!}
      --   {!!}
      --   -- let _ = 
      --   -- in {!∼1!}
     

-- multiplicationSingl : ∀ x y → singl (x ·ᵣ y)
-- multiplicationSingl = go w
--  where
--  open Elimℝ-Prop2
--  w : Elimℝ-Prop2 (λ z z₁ → singl (z ·ᵣ z₁))
--  w .rat-ratA r q = rat (r ℚ.· q) , ℚℝ!
--  w .rat-limA r x y _ = multByℚ r x y
--  w .lim-ratA x y r _ = map-snd (·ᵣComm _ _ ∙_) (multByℚ r x y)
--  w .lim-limA x y x' y' M = {!!} 
--   -- lim (fst ∘ x·x') {!!} , {!!}
--   --   where
--   --   X X' : ℚ₊
--   --   X = ?
--   --   X' = ?
--   --   <X : x <ᵣ (rat (fst X))
--   --   <X = ?
--   --   <X' : x' <ᵣ (rat (fst X'))
--   --   <X' = ?

--   --   x·x' : ∀ ε → singl (x (ε /2₊) ·ᵣ x' (ε /2₊))
--   --   x·x' ε =
--   --     M (ε /2₊) (ε /2₊)
--   --   x·x'∼ : (δ ε : ℚ₊) → fst (x·x' δ) ∼[ δ +₊ ε ] fst (x·x' ε)
--   --   x·x'∼ =
--   --    let z = {!_·ᵣ_!}
--   --    in {!!}
   
--  w .isPropA _ _ = isPropSingl
