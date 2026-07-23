module Cubical.HITs.CauchyReals.Calculus.Integration.Base where

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
import Cubical.Data.Nat.Order.Inductive as ℕᵗ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast.Base as ℤ using (pos; ℕ₊₁→ℤ; _·_; _-_)
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
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Summation
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base


open import Cubical.Tactics.CauchyReals.ExpressionLifting


open import Cubical.HITs.CauchyReals.Foundation.Rationals


open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.Tactics.CauchyReals.ExpressionLifting


on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type

on[ a , b ]IntegralOf f is s =
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh≤ᵣ p (rat (fst δ)) →
       absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))


on[_,_]IntegralOf_is'_ : ∀ a b → (ℝ → ℝ) → ℝ → Type
on[ a , b ]IntegralOf f is' s =
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh≤ᵣ p (rat (fst δ)) →
       absᵣ (riemannSum' t f -ᵣ s) <ᵣ rat (fst ε))


Integral'Uniq : ∀ a b → (a ≤ᵣ b) → ∀ f s s'
  → on[ a , b ]IntegralOf f is' s
  → on[ a , b ]IntegralOf f is' s'
  → s ≡ s'
Integral'Uniq a b a≤b f s s' S S' =
   eqℝ _ _
    λ ε →
      PT.rec2 (isProp∼ _ _ _ )
       (λ (δ , X) (δ' , X') →
         let δ⊔δ' = min₊ δ δ'
         in PT.rec (isProp∼ _ _ _)
             (λ (TP , TP<) → subst∼ (ε/2+ε/2≡ε (fst ε))
              (triangle∼ {ε = half₊ ε} {half₊ ε}
                (sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
                 (X TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ'))))))
                (invEq (∼≃abs<ε _ _ _)
                  (X' TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                   (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))
                (∃Partition< a b a≤b δ⊔δ'))
       (S (half₊ ε)) (S' (half₊ ε))



IntegralUniq : ∀ a b → (a ≤ᵣ b) → ∀ f s s'
  → on[ a , b ]IntegralOf f is s
  → on[ a , b ]IntegralOf f is s'
  → s ≡ s'
IntegralUniq a b a≤b f s s' S S' =
  eqℝ _ _
    λ ε →
      PT.rec2 (isProp∼ _ _ _ )
       (λ (δ , X) (δ' , X') →
         let δ⊔δ' = min₊ δ δ'
         in PT.rec (isProp∼ _ _ _)
             (λ (TP , TP<) → subst∼ (ε/2+ε/2≡ε (fst ε))
              (triangle∼ {ε = half₊ ε} {half₊ ε}
                (sym∼ _ _ _ (invEq (∼≃abs<ε _ _ _)
                 (X TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ'))))))
                (invEq (∼≃abs<ε _ _ _)
                  (X' TP λ k → isTrans≤ᵣ _ _ _ (TP< k)
                   (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))
                (∃Partition< a b a≤b δ⊔δ'))
       (S (half₊ ε)) (S' (half₊ ε))


Integral'≡ : ∀ a b → (a ≤ᵣ b) → ∀ f g s
  → (∀ x → x ∈ intervalℙ a b → f x ≡ g x)
  → on[ a , b ]IntegralOf f is' s
  → on[ a , b ]IntegralOf g is' s
Integral'≡ a b a≤b f g s p =
  (λ {ε} → PT.map (map-snd λ X tp msh≤ →
    isTrans≡<ᵣ _ _ _ (cong (absᵣ ∘ (_-ᵣ s))
      (sym (riemannSum'≡ (snd tp) f g p)))
     (X tp msh≤))) ∘_


IntegratedProp : ∀ a b → a ≤ᵣ b → ∀ f → isProp (Σ _ on[ a , b ]IntegralOf f is'_)
IntegratedProp a b a≤b f (s , S) (s' , S')  =
  Σ≡Prop (λ _ → isPropΠ λ _ → squash₁ )
   (Integral'Uniq a b a≤b f s s' S S')

IntegratedℙPropℙ : ∀ a b → a ≤ᵣ b → ∀ f → isProp (Σ _ on[ a , b ]IntegralOf f is_)
IntegratedℙPropℙ a b a≤b f (s , S) (s' , S')  =
  Σ≡Prop (λ _ → isPropΠ λ _ → squash₁ )
   (IntegralUniq a b a≤b f s s' S S')



integral'-transl : ∀ a b Δ f s
         → (on[ a  , b ]IntegralOf (f ∘S (Δ +ᵣ_)) is' s)
         → (on[ a +ᵣ Δ  , b +ᵣ Δ  ]IntegralOf f is' s)
integral'-transl a b Δ f s X ε =
  PT.map
    (map-snd (λ {δ} Y (p , tp) m≤ →
      isTrans≡<ᵣ _ _ _
       (cong (λ rs → absᵣ (rs -ᵣ s))
        (riemannSum'-alt-lem tp f ∙∙
          cong (λ (gg : Fin (suc (len p)) → ℝ) → foldlFin {n = 1 ℕ.+ len p}
              (λ S k →
               S +ᵣ gg k ) 0
               (idfun (Fin (1 ℕ.+ len p))))
            (funExt
             (λ x → cong₂ _·ᵣ_
                (sym (Partition-pre+.partition-pre+-lem
                  (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp) x) ∙
                   cong₂ _-ᵣ_
                    (pts'-tranp ((Rℝ.plusMinus a Δ)) ((Rℝ.plusMinus b Δ))
                      (Partition-pre+.partition-pre+
                     (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp))
                     (fsuc x) (fsuc x) refl)
                    ((pts'-tranp ((Rℝ.plusMinus a Δ)) ((Rℝ.plusMinus b Δ))
                      (Partition-pre+.partition-pre+
                     (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp))
                     (finj x) (finj x) refl)) )
               (cong f ((sym (Rℝ.minusPlus _ Δ)
                 ∙ cong ((_+ᵣ Δ) ∘ (_+ᵣ (-ᵣ Δ)))
                  (cong (samples tp) (toℕ-injective {k = 1 ℕ.+ len p} refl))) ∙ +ᵣComm _ _ ))))
         ∙∙ sym (riemannSum'-alt-lem
           (fst
             (subst2
              (λ a' b' →
                 Σ TaggedPartition[ a' , b' ]
                 (λ pp → mesh≤ᵣ (fst pp) (rat (fst δ))))
              (Rℝ.plusMinus a Δ) (Rℝ.plusMinus b Δ)
              (Partition-pre+.partition-pre+ (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ)
               (p , tp)
               ,
               Partition-pre+.mesh-pre+ (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (rat (fst δ))
               (p , tp) m≤))
             .snd) (f ∘S _+ᵣ_ Δ))))
        (uncurry Y
         (subst2 (λ a' b' →
          Σ (TaggedPartition[ a' , b' ]) (λ (xx , _) →
            mesh≤ᵣ xx (rat (fst δ)) ) )
            (Rℝ.plusMinus a Δ) (Rℝ.plusMinus b Δ)
         (Partition-pre+.partition-pre+
          (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (p , tp) ,
           Partition-pre+.mesh-pre+
          (a +ᵣ Δ) (b +ᵣ Δ) (-ᵣ Δ) (rat (fst δ)) (p , tp) m≤)))))
    (X ε)


module _ (a b : ℝ) (α : ℝ) (0<α : 0 <ᵣ α) where

 module PP = Partition-pre· (a ·ᵣ α) (b ·ᵣ α)
  (fst (invℝ₊ (α , 0<α))) (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ (α , 0<α))))

 integral'-pre·< : ∀ f s
          → (on[ a  , b ]IntegralOf (f ∘S (_·ᵣ (α))) is' s)
          → (on[ a ·ᵣ α  , b ·ᵣ α  ]IntegralOf f is' (s ·ᵣ α))
 integral'-pre·< f s X ε =
   PT.rec2 squash₁
      (λ (x'' , (0<x'' , x''<α)) (x' , (α<x' , _)) →
       let x'₊ : ℚ₊
           x'₊ = (x' , ℚ<→0< x'
                  (<ᵣ→<ℚ [ pos 0 / 1+ 0 ] x'
                   (isTrans<ᵣ (rat [ pos 0 / 1+ 0 ]) α (rat x') 0<α α<x')))
       in PT.map
         (λ ((δ , XX) : Σ _ λ δ' → (((p , tg) : TaggedPartition[ a , b ]) →
                               mesh≤ᵣ p (rat (fst δ')) →
                               absᵣ (riemannSum' tg (f ∘S (_·ᵣ α)) -ᵣ s) <ᵣ
                               rat (fst (ε ℚ₊· invℚ₊ x'₊)))) →
          let x''₊ : ℚ₊
              x''₊ = x'' , ℚ<→0< x'' (<ᵣ→<ℚ 0 x'' 0<x'')
              δ' : ℚ₊
              δ' = δ ℚ₊· x''₊
          in δ' ,
               λ (p , tg) (m≤ : mesh≤ᵣ p (rat (fst δ')))  →
               let (p' , tg') = PP.partition-pre· (p , tg)
                   ZZ : Σ TaggedPartition[ a , b ] (λ (p , _) → mesh≤ᵣ p (rat (fst δ)))
                   ZZ = subst2 (λ u v → Σ TaggedPartition[ u , v ]
                              λ (p , _) → mesh≤ᵣ p (rat (fst δ)))
                         ([x·yᵣ]/₊y a (α , 0<α)) ([x·yᵣ]/₊y b (α , 0<α))
                        ((p' , tg') ,

                          λ k →
                            isTrans≤ᵣ _ _ _
                              (PP.mesh-pre· (rat (fst δ')) (p , tg) m≤ k)
                               (isTrans≤≡ᵣ _ _ _
                                 (≤ᵣ-o·ᵣ _ (fst (invℝ₊ (ℚ₊→ℝ₊ x''₊))) _ (
                                  <ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ δ')))
                                  (invEq (invℝ₊-≤-invℝ₊ _ _)
                                    (<ᵣWeaken≤ᵣ _ _ x''<α)))
                                 (cong (_·ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ x''₊)))
                                   (rat·ᵣrat (fst δ) x'')
                                  ∙ [x·yᵣ]/₊y (rat (fst δ)) (ℚ₊→ℝ₊ x''₊)))
                                 )
                   zzz = isTrans<≡ᵣ _ _ _ (uncurry XX ZZ)
                           (rat·ᵣrat (fst ε) _ ∙
                             cong (rat (fst ε) ·ᵣ_) (sym (invℝ₊-rat x'₊)))
                   zzz' = fst (z<x/y₊≃y₊·z<x _ _ (ℚ₊→ℝ₊ x'₊)) zzz
               in isTrans≡<ᵣ _ _ _
                    (cong absᵣ
                      (cong (_-ᵣ s ·ᵣ α)
                        ( riemannSum'-alt-lem tg f
                         ∙∙ (cong (λ (f : Fin (1 ℕ.+ len (fst (fst ZZ))) → ℝ) →
                              foldlFin {n = 1 ℕ.+ len (fst (fst ZZ))}
                              (λ S k → S +ᵣ f k) 0
                              (idfun (Fin (1 ℕ.+ len (fst (fst ZZ))))))
                              (funExt
                                λ (k : Fin (1 ℕ.+ len (fst (fst ZZ)))) →
                                 cong₂ _·ᵣ_
                                   (x/₊y≡z→x≡z·y _ _ (α , 0<α)
                                     (Rℝ.·DistL- _ _ _
                                       ∙
                                        sym (PP.partition-pre·-lem (p , tg) k)
                                         ∙
                                         cong₂ _-ᵣ_
                                          (pts'-tranp
                                            ([x·yᵣ]/₊y a (α , 0<α))
                                            ([x·yᵣ]/₊y b (α , 0<α))
                                            (p' , tg') (fsuc k) (fsuc k) refl)
                                          ((pts'-tranp
                                            ([x·yᵣ]/₊y a (α , 0<α))
                                            ([x·yᵣ]/₊y b (α , 0<α))
                                            (p' , tg') (finj k) (finj k) refl)))
                                    ∙ ·ᵣComm _ _)
                                   (cong f
                                    (x/₊y≡z→x≡z·y _ _ (α , 0<α)
                                      (cong
                                        (λ k
                                         → (fst (samplesΣ tg k) ／ᵣ₊ (α , 0<α)))
                                        (toℕ-injective {k = 1 ℕ.+ len p} refl)))) ∙
                                  sym (·ᵣAssoc _ _ _))
                          ∙ foldFin·DistL' (1 ℕ.+ len (fst (fst ZZ)))
                             _
                              α (idfun _))
                           ∙ ·ᵣComm _ _ ∙∙
                         cong (_·ᵣ α)
                           (sym (riemannSum'-alt-lem
                            (fst ZZ .snd) (λ x → f (x ·ᵣ α)))))
                        ∙∙
                       sym (Rℝ.·DistL- _ _ α) ∙∙ ·ᵣComm _ _)
                      ∙∙ ·absᵣ _ _ ∙∙
                      cong (_·ᵣ absᵣ (riemannSum' (fst ZZ .snd) (f ∘S (_·ᵣ α)) -ᵣ s))
                          (absᵣPos _ 0<α))
                    (isTrans≤<ᵣ _ _ _
                       (≤ᵣ-·ᵣo _ _ _ (0≤absᵣ _) (<ᵣWeaken≤ᵣ _ _ α<x'))
                      zzz'))
          (X (ε ℚ₊· invℚ₊ x'₊)))
     (denseℚinℝ 0 α 0<α)
     (denseℚinℝ α (α +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 α decℚ<ᵣ?)))

integral'-pre· : ∀ a b f s (α : ℝ₊)
  → on[ a , b ]IntegralOf f is' s
  → on[ a ·ᵣ fst α , b ·ᵣ fst α ]IntegralOf
      (f ∘S (_·ᵣ fst (invℝ₊ α))) is' (s ·ᵣ fst α)
integral'-pre· a b f s α X =
  integral'-pre·< a b (fst α) (snd α)
    (f ∘S (_·ᵣ fst (invℝ₊ α))) s
    (subst (λ g → on[ a , b ]IntegralOf g is' s)
      (sym (funExt λ x →
        cong f
          (cong ((x ·ᵣ fst α) ·ᵣ_)
             (invℝ₊≡invℝ α (inl (snd α)))
           ∙ [x·y]/yᵣ x (fst α) (inl (snd α)))))
      X)



module PreIntegration a b (a≤b : a ≤ᵣ b) (A B : ℚ)
  (A≤a : rat A ≤ᵣ a)
  (b≤B : b ≤ᵣ rat B) (rtp : RefinableTaggedPartition[ a , b ])
  f (ucf : IsUContinuous f) where

 open RefinableTaggedPartition[_,_] rtp

 ∫-seq : Seq
 ∫-seq = (flip Sample.riemannSum' f ∘ snd) ∘S tpSeq

 module HLP (ε : ℚ₊) where
  σ' : ℚ₊
  σ' = ℚ.max 1 (B ℚ.- A) ,
      ℚ<→0< (ℚ.max 1 (B ℚ.- A))
       (ℚ.isTrans<≤ 0 1 (ℚ.max 1 (B ℚ.- A))
        (ℚ.decℚ<? {0} {1}) ((ℚ.≤max 1 (B ℚ.- A))))


  η' : ℚ₊
  η' = (half₊ ε) ℚ₊· invℚ₊ σ'

  σ : ℝ₊
  σ = maxᵣ 1 (b -ᵣ a) ,
      isTrans<≤ᵣ _ _ _ (decℚ<ᵣ? {0} {1}) (≤maxᵣ 1 (b -ᵣ a))

  η : ℝ₊
  η = ℚ₊→ℝ₊ (half₊ ε) ₊·ᵣ invℝ₊ σ


  opaque
    unfolding maxᵣ
    η'≤η : rat (fst η') ≤ᵣ fst η
    η'≤η = isTrans≡≤ᵣ _ _ _ (rat·ᵣrat _ _)
               (≤ᵣ-o·ᵣ _ _ _
                (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ (half₊ ε))))
                invσ'≤invσ)
     where
     b-a≤B-A : b -ᵣ a ≤ᵣ rat (B ℚ.- A)
     b-a≤B-A =
       isTrans≤≡ᵣ _ _ _
         (a+d≤c+b⇒a-b≤c-d b a (rat B) (rat A)
           (≤ᵣMonotone+ᵣ _ _ _ _ b≤B A≤a))
         (-ᵣ-rat₂ _ _)

     σ≤σ' : fst σ ≤ᵣ rat (fst σ')
     σ≤σ' =
       isTrans≤≡ᵣ _ _ _
         (max-monotone-≤ᵣ 1 (b -ᵣ a) (rat (B ℚ.- A)) b-a≤B-A)
         (maxᵣ-rat 1 (B ℚ.- A))

     invσ'≤invσ : rat (fst (invℚ₊ σ')) ≤ᵣ fst (invℝ₊ σ)
     invσ'≤invσ =
       isTrans≡≤ᵣ _ _ _
         (sym (invℝ₊-rat σ'))
         (invEq (invℝ₊-≤-invℝ₊ _ _) σ≤σ')


 IsCauchySequence'-∫-seq : IsCauchySequence' ∫-seq
 IsCauchySequence'-∫-seq ε =
  let (δ , Y) = ucf η'
      (N , X) = tpRef (quarter₊ δ)
  in N , λ m n N<n N<m →
    let qqzq = Resample.resampleΔ-UC a b a≤b f ucf (half₊ ε) δ
          (λ u v x →
           isTrans<≤ᵣ
            _ _ _ (fst (∼≃abs<ε _ _ _) (Y u v x))
            η'≤η)
           (tpSeq n) (tpSeq m) (X n N<n) (X m N<m)
     in isTrans≤<ᵣ _ _ _
          qqzq (<ℚ→<ᵣ _ _ (x/2<x ε))
  where
  open HLP ε

 IntegralOfUContinuous : ℝ
 IntegralOfUContinuous =
   fromCauchySequence' ∫-seq IsCauchySequence'-∫-seq

 isIntegralOfUContinuous : on[ a , b ]IntegralOf f is' IntegralOfUContinuous
 isIntegralOfUContinuous ε =
  let (δ , Y) = ucf η'
      (N , X) = tpRef (quarter₊ δ)
      zuio = fst (∼≃abs<ε _ _ _) (𝕣-lim-self _ (fromCauchySequence'-isCA
               ∫-seq IsCauchySequence'-∫-seq)
                (half₊ (half₊ ε)) ((half₊ (half₊ ε))))
      zzLem : riemannSum' (snd (tpSeq (suc N))) f
         ≡ ∫-seq (suc (fst (IsCauchySequence'-∫-seq (half₊ (half₊ ε)))))
      zzLem = refl
  in ∣ quarter₊ δ ,
     (λ (pa , tp) pa≤δ →
       let qqzq = Resample.resampleΔ-UC a b a≤b f ucf (half₊ (half₊ (half₊ ε))) δ
              (λ u v x →
                isTrans<≤ᵣ
                 _ _ _ (fst (∼≃abs<ε _ _ _) (Y u v x))
                 η'≤η)
                (pa , tp) (tpSeq (suc N))
                pa≤δ (X _ ℕ.≤-refl)
           zuii = isTrans≤<ᵣ _ _ _ (absᵣ-triangle _ _)
               (≤<ᵣMonotone+ᵣ _ _ _ _
                 qqzq zuio)
        in (isTrans<≤ᵣ _ _ _ (subst2 _<ᵣ_
            (cong absᵣ
              (cong
                (λ z →
                  riemannSum' tp f -ᵣ riemannSum' (snd (tpSeq (suc N))) f
                  +ᵣ (z +ᵣ -ᵣ IntegralOfUContinuous))
                (sym zzLem)
               ∙ +ᵣAssoc _ _ _
               ∙ cong (_+ᵣ (-ᵣ IntegralOfUContinuous))
                   (sym (+ᵣAssoc _ _ _)
                    ∙ cong (riemannSum' tp f +ᵣ_)
                        (+ᵣComm (-ᵣ riemannSum' (snd (tpSeq (suc N))) f)
                          (riemannSum' (snd (tpSeq (suc N))) f)
                         ∙ +-ᵣ (riemannSum' (snd (tpSeq (suc N))) f))
                    ∙ +IdR (riemannSum' tp f))))
              (+ᵣ-rat _ _ ∙
                cong rat (cong (fst (half₊ (half₊ (half₊ ε))) ℚ.+_)
               (ε/2+ε/2≡ε (fst (half₊ ε)))))

            zuii )) (isTrans≤≡ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _
                ((ℚ.<-+o (fst (half₊ (half₊ (half₊ ε))))
                   ((fst (half₊ ε))) ((fst (half₊ ε)))
                  (ℚ.isTrans<
                    (fst (half₊ (half₊ (half₊ ε))))
                    (fst (half₊ (half₊ ε)))
                    (fst (half₊ ε))
                    (x/2<x (half₊ (half₊ ε))) (x/2<x (half₊ ε)))))))
                  (cong rat (ε/2+ε/2≡ε (fst ε))))) ∣₁
  where
  open HLP (half₊ (half₊ ε))
