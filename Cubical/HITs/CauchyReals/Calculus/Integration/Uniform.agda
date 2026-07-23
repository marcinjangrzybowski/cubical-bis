module Cubical.HITs.CauchyReals.Calculus.Integration.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; negsuc; ℕ₊₁→ℤ; _·_; _-_)
import Cubical.Data.Int.Fast.Properties as ℤ
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp using
  (clampᵣ∈intervalℙ)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring using (-ᵣ≡[-1·ᵣ])
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Limits using (lim-const)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Analysis.Uniform using
  ( IsUContinuousConst
  ; IsUContinuousAbsᵣ
  ; IsUContinuous+ᵣ₂
  ; IsUContinuous-ᵣ₂
  ; clampDistᵣ
  )
open import Cubical.HITs.CauchyReals.Calculus.Integration.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Properties
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.MeanValue
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Concatenation
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

module IntegrationUC
 (rtpℚ : ∀ (A B : ℚ) → A ℚ.≤ B
    → RefinableTaggedPartition[ rat A , rat B ] ) where


 module _ (a b : ℝ) (a≤b : a ≤ᵣ b) where


  Integrate-UContinuous' : ∀ f → IsUContinuous f →
   Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B) → Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
  Integrate-UContinuous' f ucf ((A , B) , A≤a , b≤B) =
        IntegralOfUContinuous , isIntegralOfUContinuous
   where
   clamped-pts =
    (clamp-RefinableTaggedPartition
             _ _ a b a≤b
              (A≤a , (isTrans≤ᵣ _ _ _ a≤b b≤B))
              (isTrans≤ᵣ _ _ _ A≤a a≤b , b≤B)
             (rtpℚ A B
               (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _ A≤a a≤b)
                   b≤B))))
   open PreIntegration a b a≤b A B A≤a b≤B clamped-pts f ucf

  preIntegrate-UContinuous : ∀ f → IsUContinuous f
   → ∃[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)
   → Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
  preIntegrate-UContinuous f ucf =
    PT.rec {A = Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)}
     (IntegratedProp a b a≤b f)
     (Integrate-UContinuous' f ucf)

  opaque
   Integrate-UContinuous : ∀ f → IsUContinuous f →
    Σ ℝ λ R → on[ a , b ]IntegralOf f is' R
   Integrate-UContinuous f ucf = preIntegrate-UContinuous f ucf
      (∃enclosingℚInterval a b)



   IntegralConst : ∀ C fc
      → fst (Integrate-UContinuous (λ _ → C) fc) ≡ (C ·ᵣ (b -ᵣ a))
   IntegralConst C fc =
    PT.elim
      (λ q → isSetℝ
        (fst (PT.rec {A = Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)}
      (IntegratedProp a b a≤b (λ _ → C))
      (Integrate-UContinuous' (λ _ → C) fc) q))
        ((C ·ᵣ (b -ᵣ a)) ))
        AA
      (∃enclosingℚInterval a b)
    where
    AA : (x : Σ[ (A , B) ∈ (ℚ × ℚ) ] (rat A ≤ᵣ a) × (b ≤ᵣ rat B)) →
          fst
          (PT.rec (IntegratedProp a b a≤b (λ _ → C))
           (Integrate-UContinuous' (λ _ → C) fc) ∣ x ∣₁)
          ≡ C ·ᵣ (b -ᵣ a)
    AA ((A , B) , A≤a , b≤B) =
      congLim' _ _ _ (λ ε →
         Partition[_,_].riemannSum'Const
           (snd (tpSeq (suc _))) C) ∙ lim-const _ _

     where

      rtp : RefinableTaggedPartition[ rat A , rat B ]
      rtp = (rtpℚ A B ((≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _ A≤a a≤b)
                   b≤B))))

      clamped-pts : RefinableTaggedPartition[ a , b ]
      clamped-pts = (clamp-RefinableTaggedPartition
             _ _ a b a≤b
              (A≤a , (isTrans≤ᵣ _ _ _ a≤b b≤B))
              (isTrans≤ᵣ _ _ _ A≤a a≤b , b≤B)
             (rtpℚ A B
               (≤ᵣ→≤ℚ _ _ (isTrans≤ᵣ _ _ _
                 (isTrans≤ᵣ _ _ _ A≤a a≤b)
                   b≤B))))
      open RefinableTaggedPartition[_,_] clamped-pts

      open PreIntegration a b a≤b A B A≤a b≤B clamped-pts
        (λ _ → C) (IsUContinuousConst C)


 IntegralConcat :
   ∀ a b c (a≤b : a ≤ᵣ b) (b≤c : b ≤ᵣ c)
     (f : ℝ → ℝ) (fc : IsUContinuous f) →
     fst (Integrate-UContinuous a b a≤b f fc)
     +ᵣ fst (Integrate-UContinuous b c b≤c f fc)
     ≡ fst (Integrate-UContinuous a c (isTrans≤ᵣ _ _ _ a≤b b≤c) f fc)
 IntegralConcat a b c a≤b b≤c f fc =
   Integral'-additive a b c a≤b b≤c f
        _ _ _
        (snd (Integrate-UContinuous a b a≤b f fc))
        (snd (Integrate-UContinuous b c b≤c f fc))
        (snd (Integrate-UContinuous a c (isTrans≤ᵣ _ _ _ a≤b b≤c) f fc))

 Integral+ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → fst (Integrate-UContinuous a b a≤b f fc)
      +ᵣ  fst (Integrate-UContinuous a b a≤b g gc)
       ≡ fst (Integrate-UContinuous a b a≤b
         (λ x → f x +ᵣ g x) (IsUContinuous+ᵣ₂ f g fc gc))
 Integral+ a b a≤b f g fc gc =
   Integral'Uniq a b a≤b _ _ _
    (Integral'-+ a b a≤b f g
     _ _
     (snd (Integrate-UContinuous a b a≤b f fc))
     (snd (Integrate-UContinuous a b a≤b g gc)))
    (snd (Integrate-UContinuous a b a≤b
         (λ x → f x +ᵣ g x) (IsUContinuous+ᵣ₂ f g fc gc)))



 Integral-C· : ∀ a b (a≤b : a ≤ᵣ b) C f fc fc'
    → C ·ᵣ fst (Integrate-UContinuous a b a≤b f fc)

       ≡ fst (Integrate-UContinuous a b a≤b
         (λ x → C ·ᵣ f x) fc')
 Integral-C· a b a≤b C f fc fc' =
   Integral'Uniq a b a≤b _ _ _
     (Integral'-C· a b a≤b C f _ (snd (Integrate-UContinuous a b a≤b f fc)) )
     (snd (Integrate-UContinuous a b a≤b
         (λ x → C ·ᵣ f x) fc'))


 Integrate-UContinuous-≡ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → (∀ x → f x ≡ g x)
     → fst (Integrate-UContinuous a b a≤b f fc)
     ≡ fst (Integrate-UContinuous a b a≤b g gc)
 Integrate-UContinuous-≡ a b a≤b f g fc gc x =
   cong {A = Σ _ IsUContinuous}
         {x = f , fc} {g , subst IsUContinuous (funExt x) fc }
         (λ (g , gc) → fst (Integrate-UContinuous a b a≤b g gc))
          (ΣPathP (funExt x , toPathP refl))
     ∙ Integral'Uniq a b a≤b _ _ _
       (snd (Integrate-UContinuous a b a≤b g
          (subst IsUContinuous (funExt x) fc)))
        (snd (Integrate-UContinuous a b a≤b g gc))


 Integrate-UContinuous-≡-∈ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → (∀ x → x ∈ intervalℙ a b → f x ≡ g x)
       → fst (Integrate-UContinuous a b a≤b f fc)
       ≡ fst (Integrate-UContinuous a b a≤b g gc)
 Integrate-UContinuous-≡-∈ a b a≤b f g fc gc x =
   Integral'Uniq a b a≤b _ _ _
     (Integral'≡ a b a≤b f g
       (fst (Integrate-UContinuous a b a≤b f fc))
       x
       (snd (Integrate-UContinuous a b a≤b f fc)))
     (snd (Integrate-UContinuous a b a≤b g gc))

 Integral- : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → fst (Integrate-UContinuous a b a≤b f fc)
      -ᵣ  fst (Integrate-UContinuous a b a≤b g gc)
       ≡ fst (Integrate-UContinuous a b a≤b
         (λ x → f x -ᵣ g x) (IsUContinuous-ᵣ₂ f g fc gc))
 Integral- a b a≤b f g fc gc = PT.rec
   (isSetℝ _ _)
     (λ icNeg →
        let -1·gc : IsUContinuous (λ x → (rat [ ℤ.negsuc zero / 1+ zero ]) ·ᵣ g x)
            -1·gc = subst IsUContinuous
                    (funExt (λ _ → ·ᵣComm _ _)) (IsUContinuous∘ icNeg gc)
            -gc : IsUContinuous (λ x → -ᵣ (g x))
            -gc = subst IsUContinuous
                    (funExt λ x → sym (-ᵣ≡[-1·ᵣ] (g x))) -1·gc
        in   cong (fst (Integrate-UContinuous a b a≤b f fc) +ᵣ_)
                   (-ᵣ≡[-1·ᵣ] (fst (Integrate-UContinuous a b a≤b g gc))
                     ∙∙ Integral-C· a b a≤b
                         (rat [ ℤ.negsuc zero / 1+ zero ]) g gc -1·gc
                     ∙∙ Integrate-UContinuous-≡ a b a≤b
                         _ _ _ _
                          (λ x → sym (-ᵣ≡[-1·ᵣ] (g x))))

                ∙ Integral+ a b a≤b f (-ᵣ_ ∘ g) fc
                  -gc
                 ∙ Integrate-UContinuous-≡ a b a≤b _ _ _ _
                   (λ x → sym (x-ᵣy≡x+ᵣ[-ᵣy] (f x) (g x))))
     (IsUContinuous·ᵣR (rat [ ℤ.negsuc zero / 1+ zero ]) )

 Integral-absᵣ≤ : ∀ a b (a≤b : a ≤ᵣ b) f fc fc' →
       absᵣ (fst (Integrate-UContinuous a b a≤b f fc))
         ≤ᵣ (fst (Integrate-UContinuous a b a≤b (absᵣ ∘ f) fc'))
 Integral-absᵣ≤ a b a≤b f fc fc' =
   Integral'-abs≤ a b a≤b f _ _
     (snd (Integrate-UContinuous a b a≤b f fc))
     (snd (Integrate-UContinuous a b a≤b (absᵣ ∘ f) fc'))


 IntegralAbs : ∀ a b (a≤b : a ≤ᵣ b) f fc
    → ∀ fc-sup → (∀ x → x ∈ intervalℙ a b → absᵣ (f x) ≤ᵣ fc-sup)
    → absᵣ (fst (Integrate-UContinuous a b a≤b f fc)) ≤ᵣ fc-sup ·ᵣ (b -ᵣ a)
 IntegralAbs a b a≤b f fc fc-sup x =
  isTrans≤≡ᵣ _ _ _
    (isTrans≤ᵣ _ _ _
    (Integral-absᵣ≤  a b a≤b _ _ _)
    (Integral'-≤ a b a≤b (absᵣ ∘ f) (λ _ → fc-sup) _ _
      x
      (snd (Integrate-UContinuous a b a≤b (absᵣ ∘ f)
        (IsUContinuous∘ IsUContinuousAbsᵣ fc)) )
      (snd (Integrate-UContinuous a b a≤b (λ _ → fc-sup)
        (IsUContinuousConst _)))))
    (IntegralConst a b a≤b fc-sup _)

 Integrate-UContinuousℙ : ∀ a b (a≤b : a ≤ᵣ b) f
   → IsUContinuousℙ (intervalℙ a b) f →
    Σ ℝ λ R → on[ a , b ]IntegralOf curry ∘ f is R
 Integrate-UContinuousℙ a b a≤b f ucf =
   map-snd (fst (clampᵣ-IntegralOf' _ _ _ _ _))
     (Integrate-UContinuous
       a b a≤b (λ x → f (clampᵣ a b x) (clampᵣ∈intervalℙ a b a≤b x))
        ((λ {ε} →
          map-snd
           λ {δ} X u v u∼v →
            X _ _ _ _
             (invEq (∼≃abs<ε _ _ _)
              (isTrans≤<ᵣ _ _ _
                (clampDistᵣ a b v u)
                (fst (∼≃abs<ε _ _ _) u∼v))))
           ∘ ucf))


 Integrate-UContinuousℙ-≡ : ∀ a b (a≤b : a ≤ᵣ b) f g fc gc
    → (∀ x x∈ → f x x∈ ≡ g x x∈)
    → fst (Integrate-UContinuousℙ a b a≤b f fc)
       ≡ fst (Integrate-UContinuousℙ a b a≤b g gc)
 Integrate-UContinuousℙ-≡ a b a≤b f g fc gc x =
   cong {x = f , fc} {g , _}
     (fst ∘ uncurry (Integrate-UContinuousℙ a b a≤b))
      (ΣPathP (funExt₂ x , toPathP refl))
        ∙ IntegralUniq a b a≤b _ _ _
       (snd (Integrate-UContinuousℙ a b a≤b g
          (subst (IsUContinuousℙ (intervalℙ a b)) (funExt₂ x) fc)))
        (snd (Integrate-UContinuousℙ a b a≤b g gc))


 -- Previous names: FTOC⇒, FTOC⇐', and FTOC⇐ lived here.
 -- They now live in FundamentalTheoremOfCalculus with the point-point
 -- `uDerivativeOfℙ` API.

-- Previously this module opened `IntegrationUC rtp-1/n public`, exporting the
-- default integration machinery at top level. Open `IntegrationUC rtp-1/n` explicitly instead.
