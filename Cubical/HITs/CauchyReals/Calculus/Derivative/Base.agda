module Cubical.HITs.CauchyReals.Calculus.Derivative.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base public
  using (IsUContinuous; restrIsUContinuousℙ)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base


open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting


open import Cubical.HITs.CauchyReals.Foundation.Rationals


open ℚ using (_⁻¹₊)
invℚ₊ : ℚ₊ → ℚ₊
invℚ₊ = _⁻¹₊

ℚε/2+ε/2≡ε : ∀ ε → (ε ℚ.· [ pos 1 , 2 ]) ℚ.+ (ε ℚ.· [ pos 1 , 2 ]) ≡ ε
ℚε/2+ε/2≡ε ε = ℚ!!

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting


IsUContinuous→IsContinuous : ∀ f → IsUContinuous f → IsContinuous f
IsUContinuous→IsContinuous f fc u ε =
  ∣ map-snd (_$ u) (fc ε) ∣₁

IsUContinuous∘ : ∀ {f g} → IsUContinuous f → IsUContinuous g →
  IsUContinuous (f ∘ g)
IsUContinuous∘ cF cG ε =
  let (η , X) = cF ε ; (δ , Y) = cG η
  in _ , λ _ _ → X _ _ ∘ Y _ _


interpℝ : ℝ → ℝ → ℝ → ℝ
interpℝ a b t = a +ᵣ t ·ᵣ (b -ᵣ a)



IsUContinuous+ᵣL : ∀ x → IsUContinuous (x +ᵣ_)
IsUContinuous+ᵣL x ε = ε , λ u v u∼v →
  subst2 (_∼[ ε ]_) (+ᵣComm _ _) (+ᵣComm _ _) $ +ᵣ-∼ u v x ε u∼v


·ᵣ-∼ : ∀ u v r r' ε
    → absᵣ r ≤ᵣ rat (fst r')
    → u ∼[ ε ·₊ invℚ₊ r' ] v
    → (u ·ᵣ r) ∼[ ε ] (v ·ᵣ r)
·ᵣ-∼ u v r r' ε abs-r≤ᵣr' u∼v =
 invEq (∼≃abs<ε _ _ _)
   (isTrans≤<ᵣ _ _ _
     (isTrans≡≤ᵣ _ _ _
       (cong absᵣ ℝ!
        ∙ ·absᵣ _ _)
       (≤ᵣ-·ᵣo _ _ (absᵣ (u +ᵣ -ᵣ v)) (0≤absᵣ _) abs-r≤ᵣr'))
     (isTrans<≡ᵣ _ _ _
    (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ r')  (fst (∼≃abs<ε _ _ _) u∼v))
    (sym (rat·ᵣrat _ _) ∙ cong rat (cong ((fst r') ℚ.·_) (ℚ.·Comm (fst ε) _)
     ∙ ℚ.y·[x/y] r' (fst ε) ))))



IsUContinuous·ᵣR : ∀ x → ∥ IsUContinuous (_·ᵣ x) ∥₁
IsUContinuous·ᵣR x =
  PT.map
    (λ (x' , (absᵣx<x' , _)) ε →
      ε ·₊ invℚ₊ (x' ,
        (<ᵣ→<ℚ 0 x' (isTrans≤<ᵣ 0 (absᵣ x) _ (0≤absᵣ _) absᵣx<x'))) ,
       λ _ _ → ·ᵣ-∼ _ _ _ _ ε (<ᵣWeaken≤ᵣ _ _ absᵣx<x') )
    (denseℚinℝ (absᵣ x) ((absᵣ x) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 (absᵣ x) decℚ<ᵣ?)))

IsUContinuous∘ℙ : ∀ P {f g} → IsUContinuous f → IsUContinuousℙ P g  →
  IsUContinuousℙ P (λ x x∈ → f (g x x∈))
IsUContinuous∘ℙ P cF cG ε =
  let (η , X) = cF ε ; (δ , Y) = cG η
  in _ , λ _ _ _ _ → X _ _ ∘ Y _ _ _ _

IsUContinuousℙ∘ℙ : ∀ P P' {f g} → (g∈ : ∀ x x∈ → g x x∈ ∈ P')
  → IsUContinuousℙ P' f → IsUContinuousℙ P g

  → IsUContinuousℙ P (λ x x∈ → f (g x x∈) (g∈ x x∈))
IsUContinuousℙ∘ℙ P P' g∈ cF cG  ε =
  let (η , X) = cF ε ; (δ , Y) = cG η
     in _ , λ _ _ _ _ → X _ _ _ _ ∘ Y _ _ _ _


IsUContinuous-εᵣ : ∀ f → IsUContinuous f →
   ∀ (ε : ℝ₊) → ∃[ δ ∈ ℚ₊ ]
     (∀ u v → u ∼[ δ ] v → absᵣ (f u -ᵣ f v) <ᵣ fst ε)
IsUContinuous-εᵣ f fuc εᵣ =
 PT.map
   (λ (ε , 0<ε , ε<εᵣ) →
     map-snd
      (λ {δ} X →
        λ u v u∼v → isTrans<ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) (X u v u∼v)) ε<εᵣ)
      (fuc (ε , (<ᵣ→<ℚ 0 ε 0<ε))))
   (denseℚinℝ 0 (fst εᵣ) (snd εᵣ))



IsUContinuousℚ : (ℚ → ℝ) → Type
IsUContinuousℚ f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v → abs (u ℚ.- v) ℚ.< fst ε  → f u ∼[ ε ] f v)


Lipschitiz→IsUContinuous : ∀ L f →
     Lipschitz-ℝ→ℝ L f → IsUContinuous f
Lipschitiz→IsUContinuous L f X ε =
   (invℚ₊ L) ·₊ ε ,
    ( λ u v → subst∼ (ℚ.y·[x/y] (fst L , L .snd) _)
      ∘ X u v ((invℚ₊ L) ·₊ ε))

at_limitOf_is_ : (x : ℝ) → (∀ r → x ＃ r → ℝ)  → ℝ → Type
at x limitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r x＃r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r x＃r) <ᵣ fst ε)

at_limitOfℙ_,_is_ : (x : ℝ) → (P : ℙ ℝ) →  (∀ r → r ∈ P → x ＃ r → ℝ)  → ℝ → Type
at x limitOfℙ P , f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r r∈ x＃r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r r∈ x＃r) <ᵣ fst ε)

at_limitOfℙ_,_is'_ : (x : ℝ) → (P : ℙ ℝ) →  (∀ r → r ∈ P → x ＃ r → ℝ)  → ℝ → Type
at x limitOfℙ P , f is' L =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
   (∀ r r∈ x＃r → absᵣ (x -ᵣ r) <ᵣ rat (fst δ) → absᵣ (L -ᵣ f r r∈ x＃r) <ᵣ rat (fst ε))

at_limitOf_is'_ : (x : ℝ) → (∀ r → x ＃ r → ℝ)  → ℝ → Type
at x limitOf f is' L =
  ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
   (∀ r x＃r → absᵣ (x -ᵣ r) <ᵣ rat (fst δ) → absᵣ (L -ᵣ f r x＃r) <ᵣ rat (fst ε))

at_inclLimitOf_is_ : (x : ℝ) → (∀ r → ℝ)  → ℝ → Type
at x inclLimitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r) <ᵣ fst ε)

inclLimit→Limit : ∀ f x L → at x inclLimitOf f is L
                          → at x limitOf (λ r _ → f r)  is L
inclLimit→Limit f x L = PT.map (map-snd (const ∘_)) ∘_

substLim : ∀ {x f f' L}
  → (∀ r x＃r → f r x＃r ≡ f' r x＃r)
  → at x limitOf f is L → at x limitOf f' is L
substLim {x} {L = L} p =  subst (at x limitOf_is L) (funExt₂ p)

IsContinuousInclLim : ∀ f x → IsContinuous f →
                    at x inclLimitOf f is (f x)
IsContinuousInclLim f x cx = uncurry
  λ ε → (PT.rec squash₁
   λ (q , 0<q , q<ε) →
     PT.map (λ (δ , X) →
       (ℚ₊→ℝ₊ δ) ,
         λ r x₁ → isTrans<ᵣ _ _ _
           (fst (∼≃abs<ε _ _ _) (X r (invEq (∼≃abs<ε _ _ _) x₁)))
            q<ε  )
       (cx x (q , (<ᵣ→<ℚ 0 q 0<q)))) ∘ denseℚinℝ 0 ε

IsContinuousLim : ∀ f x → IsContinuous f →
                    at x limitOf (λ r _ → f r) is (f x)
IsContinuousLim f x cx = inclLimit→Limit _ _ _ (IsContinuousInclLim f x cx)

IsContinuousLimℙ : ∀ P f x x∈ → IsContinuousWithPred P f →
                    at x limitOfℙ P , (λ r r∈ _ → f r r∈) is (f x x∈)
IsContinuousLimℙ P f x x∈ cx = uncurry
  λ ε → (PT.rec squash₁
   λ (q , 0<q , q<ε) →
     PT.map (λ (δ , X) →
       (ℚ₊→ℝ₊ δ) ,
         λ r x₁ xx yy → isTrans<ᵣ _ _ _
           (fst (∼≃abs<ε _ _ _) ((X r x₁ (invEq (∼≃abs<ε _ _ _) yy))))
            q<ε)
       (cx x (q , (<ᵣ→<ℚ 0 q 0<q)) x∈)) ∘ denseℚinℝ 0 ε



IsContinuousInclLim→IsContinuous : ∀ f  →
                    (∀ x → at x inclLimitOf f is (f x))
                    → IsContinuous f
IsContinuousInclLim→IsContinuous f xc x (ε , 0<ε) =
  PT.rec squash₁ w z

 where
  z = xc x (rat ε , <ℚ→<ᵣ 0 ε (0<ε) )
  w : Σ ℝ₊
        (λ δ →
           (r : ℝ) →
           absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (f x -ᵣ f r) <ᵣ rat ε) →
        ∃-syntax ℚ₊ (λ δ → (v₁ : ℝ) → x ∼[ δ ] v₁ → f x ∼[ ε , 0<ε ] f v₁)
  w ((δ , 0<δ) , X) =
      PT.map (λ (q , 0<q , q<δ) →
        ((q ,  (<ᵣ→<ℚ 0 q 0<q))) ,
          λ r x∼r → invEq (∼≃abs<ε _ _ _) (X r
            (isTrans<ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) x∼r) q<δ)))
       (denseℚinℝ 0 δ 0<δ)

IsContinuousInclLim≃IsContinuous : ∀ f  →
                    (∀ x → at x inclLimitOf f is (f x))
                    ≃ (IsContinuous f)
IsContinuousInclLim≃IsContinuous f =
  propBiimpl→Equiv (isPropΠ2 λ _ _ → squash₁) (isPropIsContinuous f)
    (IsContinuousInclLim→IsContinuous f)
     λ fc x → IsContinuousInclLim f x fc

IsContinuousLimΔ : ∀ f x → IsContinuous f →
                    at 0 limitOf (λ Δx _ → f (x +ᵣ Δx)) is (f x)
IsContinuousLimΔ f x cx =
  subst (at rat [ pos 0 / 1+ 0 ] limitOf (λ Δx _ → f (x +ᵣ Δx)) is_)
   (cong f (+IdR x))
  (IsContinuousLim (λ Δx → f (x +ᵣ Δx)) 0
    (IsContinuous∘ _ _ cx (IsContinuous+ᵣL x)))



const-lim : ∀ C x → at x limitOf (λ _ _ → C) is C
const-lim C x ε = ∣ (1 , decℚ<ᵣ?) ,
  (λ r x＃r x₁ → subst (_<ᵣ fst ε) (sym (absᵣ-rat 0) ∙ cong absᵣ (sym (+-ᵣ C))) (snd ε)) ∣₁

const-limℙ : ∀ P C x → at x limitOfℙ P ,  (λ _ _ _ → C) is C
const-limℙ _ C x ε = ∣ (1 , decℚ<ᵣ?) ,
  (λ r x＃r _ x₁ → subst (_<ᵣ fst ε) (sym (absᵣ-rat 0) ∙ cong absᵣ (sym (+-ᵣ C))) (snd ε) ) ∣₁



id-lim : ∀ x → at x limitOf (λ r _ → r) is x
id-lim x ε = ∣ ε , (λ r x＃r p → p )  ∣₁

_$[_]$_ : (ℝ → ℝ)
        → (ℝ → ℝ → ℝ)
        → (ℝ → ℝ)
        → (ℝ → ℝ)
f $[ _op_ ]$ g = λ r → (f r) op (g r)

_#[_]$_ : {x : ℝ}
        → (∀ r → x ＃ r → ℝ)
        → (ℝ → ℝ → ℝ)
        → (∀ r → x ＃ r → ℝ)
        → (∀ r → x ＃ r → ℝ)
f #[ _op_ ]$ g = λ r x → (f r x) op (g r x)

+-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f #[ _+ᵣ_ ]$ g) is (F +ᵣ G)
+-lim x f g F G fL gL ε =
  PT.map2 (λ (δ , p) (δ' , p') →
       (minᵣ₊ δ δ') ,
        λ r x＃r x₁ →
         let u = p r x＃r (isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ _ _))
             u' = p' r x＃r (isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _))
         in subst2 _<ᵣ_
                (cong absᵣ ℝ!)
                (x·rat[α]+x·rat[β]=x (fst ε))
               (isTrans≤<ᵣ _ _ _
                 (absᵣ-triangle _ _)
                 (<ᵣMonotone+ᵣ _ _ _ _ u u')))
    (fL (ε ₊·ᵣ (rat [ 1 / 2 ] , decℚ<ᵣ?)))
     (gL (ε ₊·ᵣ (rat [ 1 / 2 ] , decℚ<ᵣ?)))


·-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f #[ _·ᵣ_ ]$ g) is (F ·ᵣ G)
·-lim x f g F G fL gL ε = PT.map3 w (fL (ε'f)) (gL (ε'g)) (gL 1)

 where

  ε'f : ℝ₊
  ε'f = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ G ,
           isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
            (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G)))

  ε'g : ℝ₊
  ε'g = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ F ,
            isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
            (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)))

  w : _
  w (δ , p) (δ' , p') (δ'' , p'') = δ* , ww

   where

    δ* : ℝ₊
    δ* = minᵣ₊ (minᵣ₊ δ δ') δ''

    ww : (r : ℝ) (x＃r : x ＃ r) →
           absᵣ (x -ᵣ r) <ᵣ fst δ* →
           absᵣ (F ·ᵣ G -ᵣ (f #[ _·ᵣ_ ]$ g) r x＃r) <ᵣ fst ε
    ww r x＃r x₁ = subst2 _<ᵣ_
         (cong absᵣ ℝ!)
         yy
         (isTrans≤<ᵣ _ _ _
           ((absᵣ-triangle _ _) )
           (<ᵣMonotone+ᵣ _ _ _ _
             (isTrans≡<ᵣ _ _ _
               (·absᵣ _ _)
               (<ᵣ₊Monotone·ᵣ _ _ _ _
               (0≤absᵣ _) (0≤absᵣ _) gx< u))
               (isTrans≡<ᵣ _ _ _ (·absᵣ _ _)
                 (<ᵣ₊Monotone·ᵣ _ _ _ _
               ((0≤absᵣ F)) (0≤absᵣ _)
                (subst (_<ᵣ (1 +ᵣ (absᵣ F)))
                 (+IdL _)
                  (<ᵣ-+o (rat 0) (rat 1) (absᵣ F) decℚ<ᵣ?)) u'))))


      where
       x₁' = isTrans<≤ᵣ _ _ _ x₁
                  (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ _ _))
       x₁'' = isTrans<≤ᵣ _ _ _ x₁
                  (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ' _ _))
       x₁''' = isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _)
       u = p r x＃r x₁'
       u' = p' r x＃r x₁''
       u'' = p'' r x＃r x₁'''
       gx< : absᵣ (g r x＃r) <ᵣ 1 +ᵣ absᵣ G
       gx< =
          subst (_<ᵣ (1 +ᵣ absᵣ G))
             (cong absᵣ ℝ!)

            (isTrans≤<ᵣ _ _ _
              (absᵣ-triangle ((g r x＃r) -ᵣ G) G)
               (<ᵣ-+o _ 1 (absᵣ G)
                 (subst (_<ᵣ 1) (minusComm-absᵣ _ _) u'')))
       0<1+g = isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G))
       0<1+f = isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) $ <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)

       yy : _ ≡ _
       yy = (cong₂ _+ᵣ_
           (cong ((1 +ᵣ absᵣ G) ·ᵣ_)
             (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
               (invℝ≡ _ _ _)
              ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
             (invℝ (1 +ᵣ absᵣ G)
                 (inl 0<1+g))) ∙
             ·ᵣAssoc _ _ _)
           (cong ((1 +ᵣ absᵣ F) ·ᵣ_)
             (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
              (invℝ≡ _ _ _)
              ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
             (invℝ (1 +ᵣ absᵣ F)
                 (inl 0<1+f))) ∙
              ·ᵣAssoc _ _ _) ∙
           sym (·DistR+ _ _ (fst (ε ₊／ᵣ₊ 2)))
            ∙∙ cong {y = 2} (_·ᵣ (fst (ε ₊／ᵣ₊ 2)))
                            (cong₂ _+ᵣ_
                                (x·invℝ[x] (1 +ᵣ absᵣ G)
                                  (inl 0<1+g))
                                (x·invℝ[x] (1 +ᵣ absᵣ F)
                                  (inl 0<1+f))
                               ∙ +ᵣ-rat _ _)
                       ∙∙ ·ᵣComm 2 (fst (ε ₊／ᵣ₊ 2))  ∙
                         [x/y]·yᵣ (fst ε) _ (inl _))

At_limitOf_ : (x : ℝ) → (∀ r → x ＃ r → ℝ) → Type
At x limitOf f = Σ _ (at x limitOf f is_)


derivativeErrorℙ : (P : ℙ ℝ) → (f f' : ∀ r → r ∈ P → ℝ)
                   → ∀ x → x ∈ P → ∀ y → y ∈ P → ℝ
derivativeErrorℙ P f f' x x∈ y y∈ =
  f y y∈ -ᵣ f x x∈ -ᵣ f' x x∈ ·ᵣ (y -ᵣ x)

DerivativeOfℙ_,_is_ : (P : ℙ ℝ) → (∀ r → r ∈ P → ℝ)
                                    → (∀ r → r ∈ P → ℝ) → Type
DerivativeOfℙ P , f is f' =
  ∀ x x∈ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
   (∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ)
    → absᵣ (derivativeErrorℙ P f f' x x∈ y y∈)
       ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x))

uDerivativeOfℙ_,_is_ : (P : ℙ ℝ) → (∀ r → r ∈ P → ℝ)
                                    → (∀ r → r ∈ P → ℝ) → Type
uDerivativeOfℙ P , f is f' =
  ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
   (∀ x x∈ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ)
    → absᵣ (derivativeErrorℙ P f f' x x∈ y y∈)
       ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x))

isProp-uDerivativeOfℙ : ∀ P f f' → isProp (uDerivativeOfℙ P , f is f')
isProp-uDerivativeOfℙ P f f' = isPropΠ λ _ → squash₁

isProp-DerivativeOfℙ : ∀ P f f' → isProp (DerivativeOfℙ P , f is f')
isProp-DerivativeOfℙ P f f' = isPropΠ2 λ _ _ → isPropΠ λ _ → squash₁

uDerivativeOfℙ→DerivativeOfℙ : ∀ P f f'
  → uDerivativeOfℙ P , f is f'
  → DerivativeOfℙ P , f is f'
uDerivativeOfℙ→DerivativeOfℙ P f f' df x x∈ ε =
  PT.map (map-snd (λ X y y∈ y-x≤δ → X x x∈ y y∈ y-x≤δ)) (df ε)

uDerivativeOfℙ-restr : ∀ (P P' : ℙ ℝ) f f' → (P'⊆P : P' ⊆ P)
 → uDerivativeOfℙ P , f is f'
 → uDerivativeOfℙ P' , (λ x x∈ → f x (P'⊆P x x∈)) is λ x x∈ → f' x (P'⊆P x x∈)
uDerivativeOfℙ-restr P P' f f' P'⊆P X =
  PT.map (map-snd (λ X x x∈ y y∈ y-x≤δ →
    X x (P'⊆P x x∈) y (P'⊆P y y∈) y-x≤δ)) ∘ X

DerivativeOfℙ-restr : ∀ (P P' : ℙ ℝ) f f' → (P'⊆P : P' ⊆ P)
 → DerivativeOfℙ P , f is f'
 → DerivativeOfℙ P' , (λ x x∈ → f x (P'⊆P x x∈)) is λ x x∈ → f' x (P'⊆P x x∈)
DerivativeOfℙ-restr P P' f f' P'⊆P X x x∈ =
  PT.map (map-snd (λ X y y∈ y-x≤δ →
    X y (P'⊆P y y∈) y-x≤δ)) ∘ X x (P'⊆P x x∈)

IsUContinuousℙ-restr : ∀ (P P' : ℙ ℝ) f → (P'⊆P : P' ⊆ P)
 → IsUContinuousℙ P f
 → IsUContinuousℙ P' (λ x x∈ → f x (P'⊆P x x∈))
IsUContinuousℙ-restr P P' f  P'⊆P X =
  map-snd (λ X u v u∈ v∈  → X _ _ _ _) ∘ X

0≤ε·abs : ∀ ε h → 0 ≤ᵣ rat (fst ε) ·ᵣ absᵣ h
0≤ε·abs ε h =
  isTrans≡≤ᵣ _ _ _
    (sym (Rℝ.0LeftAnnihilates (absᵣ h)))
    (≤ᵣ-·ᵣo 0 (rat (fst ε)) (absᵣ h)
      (0≤absᵣ h)
      (<ᵣWeaken≤ᵣ 0 (rat (fst ε)) (snd (ℚ₊→ℝ₊ ε))))

abs0≤ε·abs : ∀ ε h z → z ≡ 0 → absᵣ z ≤ᵣ rat (fst ε) ·ᵣ absᵣ h
abs0≤ε·abs ε h z z≡0 =
  isTrans≡≤ᵣ _ _ _ (cong absᵣ z≡0 ∙ absᵣ0) (0≤ε·abs ε h)

ε/2+ε/2·abs≡ε·abs : ∀ ε h →
  rat (fst (ε /2₊)) ·ᵣ absᵣ h
  +ᵣ rat (fst (ε /2₊)) ·ᵣ absᵣ h
  ≡ rat (fst ε) ·ᵣ absᵣ h
ε/2+ε/2·abs≡ε·abs ε h =
  cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _)
  ∙ sym (·DistL+ (absᵣ h) (rat (fst (ε /2₊))) (rat (fst (ε /2₊))))
  ∙ cong (absᵣ h ·ᵣ_)
      (+ᵣ-rat (fst (ε /2₊)) (fst (ε /2₊))
       ∙ cong rat (ℚε/2+ε/2≡ε (fst ε)))
  ∙ ·ᵣComm (absᵣ h) (rat (fst ε))

+uDerivativeℙ : ∀ P  f f' g g'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , g is g'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ +ᵣ g x x∈)
          is (λ x x∈ → f' x x∈ +ᵣ g' x x∈)
+uDerivativeℙ P f f' g g' F G ε =
  PT.map2
    (λ (δ , X) (δ' , X') →
       let δ⊔δ' = min₊ δ δ'
       in δ⊔δ' ,
           λ x x∈ y y∈ y-x≤δ⊔δ' →
              (subst2 _≤ᵣ_
                (cong absᵣ ℝ!)
                (ε/2+ε/2·abs≡ε·abs ε (y -ᵣ x))
               (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
                (≤ᵣMonotone+ᵣ _ _ _ _
                 (X x x∈ y y∈ (isTrans≤ᵣ _ _ _ y-x≤δ⊔δ'
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ') ))))
                 (X' x x∈ y y∈ (isTrans≤ᵣ _ _ _ y-x≤δ⊔δ'
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))))
    (F (ε /2₊))
    (G (ε /2₊))

+Derivativeℙ : ∀ P  f f' g g'
        → DerivativeOfℙ P , f is f'
        → DerivativeOfℙ P , g is g'
        → DerivativeOfℙ P , (λ x x∈ → f x x∈ +ᵣ g x x∈)
          is (λ x x∈ → f' x x∈ +ᵣ g' x x∈)
+Derivativeℙ P f f' g g' F G x x∈ ε =
  PT.map2
    (λ (δ , X) (δ' , X') →
       let δ⊔δ' = min₊ δ δ'
       in δ⊔δ' ,
           λ y y∈ y-x≤δ⊔δ' →
              (subst2 _≤ᵣ_
                (cong absᵣ ℝ!)
                (ε/2+ε/2·abs≡ε·abs ε (y -ᵣ x))
               (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
                (≤ᵣMonotone+ᵣ _ _ _ _
                 (X y y∈ (isTrans≤ᵣ _ _ _ y-x≤δ⊔δ'
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ') ))))
                 (X' y y∈ (isTrans≤ᵣ _ _ _ y-x≤δ⊔δ'
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))))
    (F x x∈ (ε /2₊))
    (G x x∈ (ε /2₊))

uDerivativeℙ-id : ∀ P
 → uDerivativeOfℙ P , (λ x _ → x) is (λ _ _ → 1)
uDerivativeℙ-id P ε =
 ∣ ε , (λ x _ y _ _ →
   abs0≤ε·abs ε (y -ᵣ x) _ ℝ!) ∣₁

uDerivativeℙ-const : ∀ P C →
 uDerivativeOfℙ P , (λ _ _ → C) is (λ _ _ → 0)

uDerivativeℙ-const P C ε =
 ∣ 1 , (λ x _ y _ _ →
   abs0≤ε·abs ε (y -ᵣ x) _ ℝ!) ∣₁

Derivativeℙ-id : ∀ P
 → DerivativeOfℙ P , (λ x _ → x) is (λ _ _ → 1)
Derivativeℙ-id P =
  uDerivativeOfℙ→DerivativeOfℙ P (λ x _ → x) (λ _ _ → 1)
    (uDerivativeℙ-id P)

Derivativeℙ-const : ∀ P C →
 DerivativeOfℙ P , (λ _ _ → C) is (λ _ _ → 0)
Derivativeℙ-const P C =
  uDerivativeOfℙ→DerivativeOfℙ P (λ _ _ → C) (λ _ _ → 0)
    (uDerivativeℙ-const P C)


uDerivativeℙ-cancelConst : ∀ P C f f'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ +ᵣ C) is f'
        → uDerivativeOfℙ P , f is f'
uDerivativeℙ-cancelConst P C f f' df =
   subst2
     (uDerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → Rℝ.plusMinus _ _)
     (funExt₂ λ _ _ → +IdR _)
     (+uDerivativeℙ P _ _ _ _ df (uDerivativeℙ-const P (-ᵣ C)) )

Derivativeℙ-cancelConst : ∀ P C f f'
        → DerivativeOfℙ P , (λ x x∈ → f x x∈ +ᵣ C) is f'
        → DerivativeOfℙ P , f is f'
Derivativeℙ-cancelConst P C f f' df =
   subst2
     (DerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → Rℝ.plusMinus _ _)
     (funExt₂ λ _ _ → +IdR _)
     (+Derivativeℙ P _ _ _ _ df (Derivativeℙ-const P (-ᵣ C)) )


C·uDerivativeℙ : ∀ P C f f'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , (λ x x∈ → C ·ᵣ f x x∈) is (λ x x∈ → C ·ᵣ f' x x∈)
C·uDerivativeℙ P C f f' udp ε =
  PT.rec squash₁
    (λ (η , 0<η , η<1/[C+1]) →
      PT.map (map-snd
        (λ X x x∈ y y∈ y-x≤δ →
          let η₊ = η , (<ᵣ→<ℚ 0 η 0<η)
              ∣C∣≤∣C∣+1 =
                isTrans≡≤ᵣ _ _ _
                  (sym (+IdR (absᵣ C)))
                  (≤ᵣ-o+ 0 1 (absᵣ C) decℚ≤ᵣ?)
              0<∣C∣+1 =
                isTrans≡<ᵣ _ _ _
                  (sym (+ᵣ-rat _ _))
                  (≤<ᵣMonotone+ᵣ _ _ _ _
                    (0≤absᵣ C) (decℚ<ᵣ? {0} {1}))
              ∣C∣+1 = absᵣ C +ᵣ 1 , 0<∣C∣+1
              ∣C∣+1·η≤ε =
                <ᵣWeaken≤ᵣ _ _
                  (fst (z<x/y₊≃y₊·z<x (rat (fst ε)) (rat η) ∣C∣+1)
                    η<1/[C+1])
          in isTrans≡≤ᵣ _ _ _
             (cong absᵣ ℝ!
               ∙ ·absᵣ _ _)
             (isTrans≤ᵣ _ _ _
               (≤ᵣ-o·ᵣ _ _ (absᵣ C) (0≤absᵣ C)
                 (X x x∈ y y∈ y-x≤δ))
               (isTrans≤ᵣ _ _ _
                 (isTrans≤≡ᵣ _ _ _
                   (≤ᵣ-·ᵣo (absᵣ C) (absᵣ C +ᵣ 1)
                     (rat η ·ᵣ absᵣ (y -ᵣ x))
                     (0≤ε·abs η₊ (y -ᵣ x))
                     ∣C∣≤∣C∣+1)
                   ℝ!)
                 (≤ᵣ-·ᵣo ((absᵣ C +ᵣ 1) ·ᵣ rat η)
                   (rat (fst ε)) (absᵣ (y -ᵣ x))
                   (0≤absᵣ (y -ᵣ x)) ∣C∣+1·η≤ε)))))
        (udp (η ,  (<ᵣ→<ℚ _ _ 0<η))))
    (denseℚinℝ 0 _ (snd (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (absᵣ C +ᵣ 1 ,
      isTrans≡<ᵣ _ _ _
        (sym (+ᵣ-rat _ _)) (≤<ᵣMonotone+ᵣ _ _ _ _
          (0≤absᵣ C) (decℚ<ᵣ? {0} {1}))))))

C·Derivativeℙ : ∀ P C f f'
        → DerivativeOfℙ P , f is f'
        → DerivativeOfℙ P , (λ x x∈ → C ·ᵣ f x x∈) is (λ x x∈ → C ·ᵣ f' x x∈)
C·Derivativeℙ P C f f' dp x x∈ ε =
  PT.rec squash₁
    (λ (η , 0<η , η<1/[C+1]) →
      PT.map (map-snd
        (λ X y y∈ y-x≤δ →
          let η₊ = η , (<ᵣ→<ℚ 0 η 0<η)
              ∣C∣≤∣C∣+1 =
                isTrans≡≤ᵣ _ _ _
                  (sym (+IdR (absᵣ C)))
                  (≤ᵣ-o+ 0 1 (absᵣ C) decℚ≤ᵣ?)
              0<∣C∣+1 =
                isTrans≡<ᵣ _ _ _
                  (sym (+ᵣ-rat _ _))
                  (≤<ᵣMonotone+ᵣ _ _ _ _
                    (0≤absᵣ C) (decℚ<ᵣ? {0} {1}))
              ∣C∣+1 = absᵣ C +ᵣ 1 , 0<∣C∣+1
              ∣C∣+1·η≤ε =
                <ᵣWeaken≤ᵣ _ _
                  (fst (z<x/y₊≃y₊·z<x (rat (fst ε)) (rat η) ∣C∣+1)
                    η<1/[C+1])
          in isTrans≡≤ᵣ _ _ _
             (cong absᵣ ℝ!
               ∙ ·absᵣ _ _)
             (isTrans≤ᵣ _ _ _
               (≤ᵣ-o·ᵣ _ _ (absᵣ C) (0≤absᵣ C)
                 (X y y∈ y-x≤δ))
               (isTrans≤ᵣ _ _ _
                 (isTrans≤≡ᵣ _ _ _
                   (≤ᵣ-·ᵣo (absᵣ C) (absᵣ C +ᵣ 1)
                     (rat η ·ᵣ absᵣ (y -ᵣ x))
                     (0≤ε·abs η₊ (y -ᵣ x))
                     ∣C∣≤∣C∣+1)
                   ℝ!)
                 (≤ᵣ-·ᵣo ((absᵣ C +ᵣ 1) ·ᵣ rat η)
                   (rat (fst ε)) (absᵣ (y -ᵣ x))
                   (0≤absᵣ (y -ᵣ x)) ∣C∣+1·η≤ε)))))
        (dp x x∈ (η ,  (<ᵣ→<ℚ _ _ 0<η))))
    (denseℚinℝ 0 _ (snd (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (absᵣ C +ᵣ 1 ,
      isTrans≡<ᵣ _ _ _
        (sym (+ᵣ-rat _ _)) (≤<ᵣMonotone+ᵣ _ _ _ _
          (0≤absᵣ C) (decℚ<ᵣ? {0} {1}))))))

uDerivativeOfℙ-ᵣ : ∀ P f f'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , (λ x x∈ → -ᵣ (f x x∈)) is (λ x x∈ → -ᵣ (f' x x∈))
uDerivativeOfℙ-ᵣ P f f' df =
     subst2
     (uDerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
     (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
     (C·uDerivativeℙ P -1 f f' df)

DerivativeOfℙ-ᵣ : ∀ P f f'
        → DerivativeOfℙ P , f is f'
        → DerivativeOfℙ P , (λ x x∈ → -ᵣ (f x x∈)) is (λ x x∈ → -ᵣ (f' x x∈))
DerivativeOfℙ-ᵣ P f f' df =
     subst2
     (DerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
     (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
     (C·Derivativeℙ P -1 f f' df)


·CuDerivativeℙ : ∀ P C f f'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ ·ᵣ C) is (λ x x∈ → f' x x∈ ·ᵣ C)
·CuDerivativeℙ P C f f' df =
     subst2
     (uDerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → ·ᵣComm _ _)
     (funExt₂ λ _ _ → ·ᵣComm _ _)
     (C·uDerivativeℙ P C f f' df)

·CDerivativeℙ : ∀ P C f f'
        → DerivativeOfℙ P , f is f'
        → DerivativeOfℙ P , (λ x x∈ → f x x∈ ·ᵣ C) is (λ x x∈ → f' x x∈ ·ᵣ C)
·CDerivativeℙ P C f f' df =
     subst2
     (DerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → ·ᵣComm _ _)
     (funExt₂ λ _ _ → ·ᵣComm _ _)
     (C·Derivativeℙ P C f f' df)


-uDerivativeℙ : ∀ P  f f' g g'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , g is g'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ -ᵣ g x x∈)
          is (λ x x∈ → f' x x∈ -ᵣ g' x x∈)
-uDerivativeℙ P f f' g g' F G =
 +uDerivativeℙ P _ _ _ _ F (uDerivativeOfℙ-ᵣ P _ _ G)

-Derivativeℙ : ∀ P  f f' g g'
        → DerivativeOfℙ P , f is f'
        → DerivativeOfℙ P , g is g'
        → DerivativeOfℙ P , (λ x x∈ → f x x∈ -ᵣ g x x∈)
          is (λ x x∈ → f' x x∈ -ᵣ g' x x∈)
-Derivativeℙ P f f' g g' F G =
 +Derivativeℙ P _ _ _ _ F (DerivativeOfℙ-ᵣ P _ _ G)

limitUniq : ∀ x f y y'
 → at x limitOf f is y
 → at x limitOf f is y'
 → y ≡ y'
limitUniq x f y y' X X' = eqℝ _ _
  λ ε →
    PT.rec2 (isProp∼ _ _ _)
      (λ (δ , D) (δ' , D') →
        let [δ⊔δ]/2 = (minᵣ₊ δ δ') ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ]₊))
            x＃ : x ＃ (x +ᵣ -ᵣ (minᵣ₊ δ δ' ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ]₊)) .fst)
            x＃ = (inr (isTrans<≡ᵣ _ _ _
                        (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ (snd [δ⊔δ]/2))) ℝ!))
        in subst∼ ℚ!!
                  (triangle∼  {ε = ε /2₊} {ε /2₊}
                    (invEq (∼≃abs<ε _ _ _) (D (x -ᵣ fst [δ⊔δ]/2)
                     x＃
                     ((isTrans≡<ᵣ _ _ _
                       (cong
                         absᵣ ℝ! ∙ absᵣPos _ (snd [δ⊔δ]/2))
                       (isTrans≤<ᵣ _ _ _
                         (≤ᵣ-·o _ _ _ (ℚ.0≤pos _ _) (min≤ᵣ _ _)) (isTrans<≡ᵣ _ _ _
                           (<ᵣ-o·ᵣ _ _ δ decℚ<ᵣ?) (·IdR _)))))))
                      (sym∼ _ _ _
                       ((invEq (∼≃abs<ε _ _ _) (D' (x -ᵣ fst [δ⊔δ]/2)
                     x＃
                     (isTrans≡<ᵣ _ _ _
                       (cong absᵣ ℝ! ∙ absᵣPos _ (snd [δ⊔δ]/2))
                       (isTrans≤<ᵣ _ _ _
                         (≤ᵣ-·o _ _ _ (ℚ.0≤pos _ _) (min≤ᵣ' _ _)) (isTrans<≡ᵣ _ _ _
                           (<ᵣ-o·ᵣ _ _ δ' decℚ<ᵣ?) (·IdR _)))))))))
        )
      (X (ℚ₊→ℝ₊ (ε /2₊))) (X' (ℚ₊→ℝ₊ (ε /2₊)))

Bounded : (P : ℙ ℝ) → (f : ∀ x → x ∈ P → ℝ)
                    → Type
Bounded P f = Σ[ b ∈ ℚ₊ ] (∀ x x∈ → absᵣ (f x x∈) ≤ᵣ rat (fst b))

chainRule-uDerivativeℙ : ∀ P P' →
  (f : ∀ x → x ∈ P → ℝ)
  (f' : ∀ x → x ∈ P → ℝ)
  (g : ∀ x → x ∈ P' → ℝ)
  (g' : ∀ x → x ∈ P' → ℝ)
  → Bounded P f'
  → ∥ Bounded P' g' ∥₁
  → (f∈ : ∀ x x∈ → f x x∈ ∈ P')
  → IsUContinuousℙ P f
  → uDerivativeOfℙ P' , g is g'
  → uDerivativeOfℙ P , f is f'
  → uDerivativeOfℙ P , (λ x x∈ → g (f x x∈) (f∈ x x∈))
      is λ x x∈ → g' (f x x∈) (f∈ x x∈) ·ᵣ f' x x∈
chainRule-uDerivativeℙ P P' f f' g g' (∣f'∣ , <∣f'∣) gBd
  f∈ fUC gD fD ε = do
  (∣g'∣ , <∣g'∣) ← gBd
  let α = invℚ₊ (1 +₊ ∣f'∣) ·₊ (ε /2₊)
      β = invℚ₊ (α +₊ ∣g'∣) ·₊ (ε /2₊)
  (δ-g , Dg) ← gD α
  (δ-f , Df) ← fD β
  let ω-f , fClose = fUC δ-g
      δ₀ = min₊ ω-f δ-f
      δ = δ₀ /2₊
      g∘f : ∀ x → x ∈ P → ℝ
      g∘f x x∈ = g (f x x∈) (f∈ x x∈)
      g'∘f : ∀ x → x ∈ P → ℝ
      g'∘f x x∈ = g' (f x x∈) (f∈ x x∈)
      δ≤ω : fst δ ℚ.≤ fst ω-f
      δ≤ω =
        ℚ.isTrans≤ _ _ _
          (ℚ.<Weaken≤ _ _ (/2₊<id δ₀))
          (ℚ.min≤ (fst ω-f) (fst δ-f))
      δ≤δ-f : fst δ ℚ.≤ fst δ-f
      δ≤δ-f =
        ℚ.isTrans≤ _ _ _
          (ℚ.<Weaken≤ _ _ (/2₊<id δ₀))
          (ℚ.min≤' (fst ω-f) (fst δ-f))
      ∣f'∣≤1+∣f'∣ : rat (fst ∣f'∣) ≤ᵣ rat (fst (1 +₊ ∣f'∣))
      ∣f'∣≤1+∣f'∣ =
        isTrans≡≤ᵣ _ _ _
          (sym (+IdL _))
          (isTrans≤≡ᵣ _ _ _
            (≤ᵣ-+o 0 1 (rat (fst ∣f'∣)) decℚ≤ᵣ?)
            (+ᵣ-rat 1 (fst ∣f'∣)))
      α·∣f'∣≤ε/2 : rat (fst α) ·ᵣ rat (fst ∣f'∣) ≤ᵣ rat (fst (ε /2₊))
      α·∣f'∣≤ε/2 =
        isTrans≤≡ᵣ _ _ _
          (≤ᵣ-o·ᵣ _ _ (rat (fst α))
            (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ α))
            ∣f'∣≤1+∣f'∣)
          (·ᵣComm _ _
           ∙ sym (rat·ᵣrat _ _)
           ∙ cong rat (ℚ.y·[x/y] (1 +₊ ∣f'∣) (fst (ε /2₊))))
      [α+∣g'∣]·β≡ε/2 : rat (fst (α +₊ ∣g'∣)) ·ᵣ rat (fst β) ≡ rat (fst (ε /2₊))
      [α+∣g'∣]·β≡ε/2 =
        sym (rat·ᵣrat _ _)
        ∙ cong rat (ℚ.y·[x/y] (α +₊ ∣g'∣) (fst (ε /2₊)))
  ∣ δ , (λ x x∈ y y∈ y-x≤δ →
    let Δx = y -ᵣ x
        Δf = f y y∈ -ᵣ f x x∈
        Ef = derivativeErrorℙ P f f' x x∈ y y∈
        Eg = derivativeErrorℙ P' g g'
               (f x x∈) (f∈ x x∈)
               (f y y∈) (f∈ y y∈)
        Ec = derivativeErrorℙ P g∘f
               (λ x x∈ → g'∘f x x∈ ·ᵣ f' x x∈)
               x x∈ y y∈
        y-x≤δ-f : absᵣ Δx ≤ᵣ rat (fst δ-f)
        y-x≤δ-f = isTrans≤ᵣ _ _ _ y-x≤δ (≤ℚ→≤ᵣ _ _ δ≤δ-f)
        x-y<ω : absᵣ (x -ᵣ y) <ᵣ rat (fst ω-f)
        x-y<ω =
          isTrans≡<ᵣ _ _ _
            (minusComm-absᵣ x y)
            (isTrans≤<ᵣ _ _ _
              y-x≤δ
              (isTrans<≤ᵣ _ _ _
                (<ℚ→<ᵣ _ _ (/2₊<id δ₀))
                (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst ω-f) (fst δ-f)))))
        fx∼fy : f x x∈ ∼[ δ-g ] f y y∈
        fx∼fy = fClose x y x∈ y∈ (invEq (∼≃abs<ε _ _ _) x-y<ω)
        fy-fx≤δ-g : absᵣ Δf ≤ᵣ rat (fst δ-g)
        fy-fx≤δ-g =
          <ᵣWeaken≤ᵣ _ _
            (isTrans≡<ᵣ _ _ _
              (minusComm-absᵣ (f y y∈) (f x x∈))
              (fst (∼≃abs<ε _ _ _) fx∼fy))
        Ef≤ : absᵣ Ef ≤ᵣ rat (fst β) ·ᵣ absᵣ Δx
        Ef≤ = Df x x∈ y y∈ y-x≤δ-f
        Eg≤ : absᵣ Eg ≤ᵣ rat (fst α) ·ᵣ absᵣ Δf
        Eg≤ = Dg (f x x∈) (f∈ x x∈) (f y y∈) (f∈ y y∈) fy-fx≤δ-g
        abs-f'Δx≤ : absᵣ (f' x x∈ ·ᵣ Δx)
                    ≤ᵣ rat (fst ∣f'∣) ·ᵣ absᵣ Δx
        abs-f'Δx≤ =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _)
            (≤ᵣ-·ᵣo _ _ _
              (0≤absᵣ Δx)
              (<∣f'∣ x x∈))
        absΔf≤ : absᵣ Δf
                  ≤ᵣ rat (fst ∣f'∣) ·ᵣ absᵣ Δx +ᵣ absᵣ Ef
        absΔf≤ =
          isTrans≤≡ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (absᵣ-triangle' Δf (f' x x∈ ·ᵣ Δx))
              (≤ᵣMonotone+ᵣ _ _ _ _
                (≤ᵣ-refl _)
                abs-f'Δx≤))
            (+ᵣComm _ _)
        zL : absᵣ Eg
             ≤ᵣ rat (fst α)
                ·ᵣ (rat (fst ∣f'∣) ·ᵣ absᵣ Δx +ᵣ absᵣ Ef)
        zL =
          isTrans≤ᵣ _ _ _
            Eg≤
            (≤ᵣ-o·ᵣ _ _ (rat (fst α))
              (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ α))
              absΔf≤)
        zR : absᵣ (g'∘f x x∈ ·ᵣ Ef)
             ≤ᵣ rat (fst ∣g'∣) ·ᵣ absᵣ Ef
        zR =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _)
            (≤ᵣ-·ᵣo _ _ _
              (0≤absᵣ Ef)
              (<∣g'∣ (f x x∈) (f∈ x x∈)))
        Ec≡Eg+gEf : Ec ≡ Eg +ᵣ g'∘f x x∈ ·ᵣ Ef
        Ec≡Eg+gEf = ℝ!
        pre≤ : absᵣ Ec
          ≤ᵣ rat (fst α) ·ᵣ rat (fst ∣f'∣) ·ᵣ absᵣ Δx
             +ᵣ rat (fst (α +₊ ∣g'∣)) ·ᵣ absᵣ Ef
        pre≤ =
          isTrans≤≡ᵣ _ _ _
            (isTrans≤ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (cong absᵣ Ec≡Eg+gEf)
                (absᵣ-triangle Eg (g'∘f x x∈ ·ᵣ Ef)))
              (≤ᵣMonotone+ᵣ _ _ _ _ zL zR))
            ((cong₂ _+ᵣ_ (·DistL+ _ _ _) refl)
             ∙ sym (+ᵣAssoc _ _ _)
             ∙ cong₂ _+ᵣ_
                (·ᵣAssoc _ _ _)
                (sym (·DistR+ _ _ _)
                 ∙ cong₂ _·ᵣ_ (+ᵣ-rat (fst α) (fst ∣g'∣)) refl))
        z₁ : rat (fst α) ·ᵣ rat (fst ∣f'∣) ·ᵣ absᵣ Δx
             ≤ᵣ rat (fst (ε /2₊)) ·ᵣ absᵣ Δx
        z₁ =
          ≤ᵣ-·ᵣo _ _ _
            (0≤absᵣ Δx)
            α·∣f'∣≤ε/2
        z₂ : rat (fst (α +₊ ∣g'∣)) ·ᵣ absᵣ Ef
             ≤ᵣ rat (fst (ε /2₊)) ·ᵣ absᵣ Δx
        z₂ =
          isTrans≤≡ᵣ _ _ _
            (≤ᵣ-o·ᵣ _ _ (rat (fst (α +₊ ∣g'∣)))
              (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ (α +₊ ∣g'∣)))
              Ef≤)
            (·ᵣAssoc _ _ _
             ∙ cong (_·ᵣ absᵣ Δx) [α+∣g'∣]·β≡ε/2)
    in isTrans≤ᵣ _ _ _
        pre≤
        (isTrans≤≡ᵣ _ _ _
          (≤ᵣMonotone+ᵣ _ _ _ _ z₁ z₂)
          (ε/2+ε/2·abs≡ε·abs ε Δx))) ∣₁


uDerivativeOfℙ· : ∀ a b → a <ᵣ b
  → (f g f' g' : ∀ x → x ∈ intervalℙ a b → ℝ)
  → Bounded (intervalℙ a b) f
  → Bounded (intervalℙ a b) g
  → IsUContinuousℙ (intervalℙ a b) f
  → Bounded (intervalℙ a b) g'
  → uDerivativeOfℙ intervalℙ a b , f is f'
  → uDerivativeOfℙ intervalℙ a b , g is g'
  → uDerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ g x x∈)
    is λ x x∈ → f' x x∈ ·ᵣ g x x∈ +ᵣ g' x x∈ ·ᵣ f x x∈
uDerivativeOfℙ· a b a<b f g f' g' (bf , <bf) (bg , <bg) ucf (bg' , <bg') dF dG ε = do
  let M = max₊ (max₊ bf bg) bg'
  let ε' = ([ 1 / 3 ]₊ ·₊ ε) ·₊ invℚ₊ M
  (δf' , Df) ← dF ε'
  (δg' , Dg) ← dG ε'
  let (δf , Cf) = ucf ε'
  let δ = min₊ (min₊ δf' δg') (δf /2₊)
  return (δ , λ x x∈ y y∈ y-x≤δ →
    let h = y -ᵣ x
        Ef = derivativeErrorℙ (intervalℙ a b) f f' x x∈ y y∈
        Eg = derivativeErrorℙ (intervalℙ a b) g g' x x∈ y y∈
        q = fst ([ 1 / 3 ]₊ ·₊ ε)
        c = rat q
        ∣h∣ = absᵣ h
        third = c ·ᵣ ∣h∣

        err≡ : derivativeErrorℙ (intervalℙ a b)
                 (λ x₁ x∈₁ → f x₁ x∈₁ ·ᵣ g x₁ x∈₁)
                 (λ x₁ x∈₁ → f' x₁ x∈₁ ·ᵣ g x₁ x∈₁
                               +ᵣ g' x₁ x∈₁ ·ᵣ f x₁ x∈₁)
                 x x∈ y y∈
             ≡ g x x∈ ·ᵣ Ef +ᵣ f y y∈ ·ᵣ Eg
               +ᵣ (g' x x∈ ·ᵣ h) ·ᵣ (f y y∈ -ᵣ f x x∈)
        err≡ = ℝ!

        Mε'≡c : rat (fst M) ·ᵣ rat (fst ε') ≡ c
        Mε'≡c =
          sym (rat·ᵣrat (fst M) (fst ε'))
          ∙ cong rat
              (ℚ.·Assoc (fst M) q (fst (invℚ₊ M))
               ∙ cong (λ z → z ℚ.· fst (invℚ₊ M)) (ℚ.·Comm (fst M) q)
               ∙ sym (ℚ.·Assoc q (fst M) (fst (invℚ₊ M)))
               ∙ cong (q ℚ.·_) (ℚ.x·invℚ₊[x] M)
               ∙ ℚ.·IdR q)

        Mε'∣h∣≡third : rat (fst M) ·ᵣ (rat (fst ε') ·ᵣ ∣h∣) ≡ third
        Mε'∣h∣≡third =
          ·ᵣAssoc _ _ _ ∙ cong (_·ᵣ ∣h∣) Mε'≡c

        Mε'∣h∣≡third' : (rat (fst M) ·ᵣ rat (fst ε')) ·ᵣ ∣h∣ ≡ third
        Mε'∣h∣≡third' = cong (_·ᵣ ∣h∣) Mε'≡c

        ∣h∣Mε'≡third : ∣h∣ ·ᵣ (rat (fst M) ·ᵣ rat (fst ε')) ≡ third
        ∣h∣Mε'≡third =
          ·ᵣComm ∣h∣ (rat (fst M) ·ᵣ rat (fst ε')) ∙ Mε'∣h∣≡third'

        ∣h∣≤δf' : ∣h∣ ≤ᵣ rat (fst δf')
        ∣h∣≤δf' =
          isTrans≤ᵣ _ _ _ y-x≤δ
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.min≤ (ℚ.min (fst δf') (fst δg')) (fst (δf /2₊)))
                (ℚ.min≤ (fst δf') (fst δg'))))

        ∣h∣≤δg' : ∣h∣ ≤ᵣ rat (fst δg')
        ∣h∣≤δg' =
          isTrans≤ᵣ _ _ _ y-x≤δ
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.min≤ (ℚ.min (fst δf') (fst δg')) (fst (δf /2₊)))
                (ℚ.min≤' (fst δf') (fst δg'))))

        ∣h∣≤δf/2 : ∣h∣ ≤ᵣ rat (fst (δf /2₊))
        ∣h∣≤δf/2 =
          isTrans≤ᵣ _ _ _ y-x≤δ
            (≤ℚ→≤ᵣ _ _
              (ℚ.min≤' (ℚ.min (fst δf') (fst δg')) (fst (δf /2₊))))

        ∣g[x]∣≤M : absᵣ (g x x∈) ≤ᵣ rat (fst M)
        ∣g[x]∣≤M =
          isTrans≤ᵣ _ _ _ (<bg x x∈)
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.≤max' (fst bf) (fst bg))
                (ℚ.≤max _ (fst bg'))))

        ∣f[y]∣≤M : absᵣ (f y y∈) ≤ᵣ rat (fst M)
        ∣f[y]∣≤M =
          isTrans≤ᵣ _ _ _ (<bf y y∈)
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.≤max (fst bf) (fst bg))
                (ℚ.≤max _ (fst bg'))))

        ∣g'[x]∣≤M : absᵣ (g' x x∈) ≤ᵣ rat (fst M)
        ∣g'[x]∣≤M =
          isTrans≤ᵣ _ _ _ (<bg' x x∈)
            (≤ℚ→≤ᵣ _ _
              (ℚ.≤max' (ℚ.max (fst bf) (fst bg)) (fst bg')))

        Df* : absᵣ (g x x∈ ·ᵣ Ef) ≤ᵣ third
        Df* =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _)
            (isTrans≤≡ᵣ _ _ _
              (≤ᵣ₊Monotone·ᵣ _ _ _ _
                (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ M))
                (0≤absᵣ Ef)
                ∣g[x]∣≤M
                (Df x x∈ y y∈ ∣h∣≤δf'))
              Mε'∣h∣≡third)

        Dg* : absᵣ (f y y∈ ·ᵣ Eg) ≤ᵣ third
        Dg* =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _)
            (isTrans≤≡ᵣ _ _ _
              (≤ᵣ₊Monotone·ᵣ _ _ _ _
                (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ M))
                (0≤absᵣ Eg)
                ∣f[y]∣≤M
                (Dg x x∈ y y∈ ∣h∣≤δg'))
              Mε'∣h∣≡third)

        Cf* : absᵣ ((g' x x∈ ·ᵣ h) ·ᵣ (f y y∈ -ᵣ f x x∈)) ≤ᵣ third
        Cf* =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _
             ∙ cong₂ _·ᵣ_ (·absᵣ _ _) refl
             ∙ ℝ!)
            (isTrans≤≡ᵣ _ _ _
              (≤ᵣ-o·ᵣ _ _ ∣h∣ (0≤absᵣ h)
                (≤ᵣ₊Monotone·ᵣ _ _ _ _
                  (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ M))
                  (0≤absᵣ (f y y∈ -ᵣ f x x∈))
                  ∣g'[x]∣≤M
                  (<ᵣWeaken≤ᵣ _ _
                    (isTrans≡<ᵣ _ _ _
                      (minusComm-absᵣ (f y y∈) (f x x∈))
                      (fst (∼≃abs<ε _ _ _)
                        (Cf x y x∈ y∈
                          (invEq (∼≃abs<ε x y δf)
                            (isTrans≡<ᵣ _ _ _
                              (minusComm-absᵣ x y)
                              (isTrans≤<ᵣ _ _ _
                                ∣h∣≤δf/2
                                (<ℚ→<ᵣ _ _ (/2₊<id δf)))))))))))
              ∣h∣Mε'≡third)

        thirds≡ε : third +ᵣ third +ᵣ third ≡ rat (fst ε) ·ᵣ ∣h∣
        thirds≡ε =
            cong₂ _+ᵣ_
              (cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _))
              (·ᵣComm _ _)
          ∙ cong (_+ᵣ (∣h∣ ·ᵣ c)) (sym (·DistL+ ∣h∣ c c))
          ∙ sym (·DistL+ ∣h∣ (c +ᵣ c) c)
          ∙ cong (∣h∣ ·ᵣ_)
              (cong (_+ᵣ c) (+ᵣ-rat q q)
               ∙ +ᵣ-rat (q ℚ.+ q) q
               ∙ cong rat ℚ!)
          ∙ ·ᵣComm _ _
    in isTrans≡≤ᵣ _ _ _
      (cong absᵣ err≡)
      (isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _
          (absᵣ-triangle _ _)
          (≤ᵣMonotone+ᵣ _ _ _ _
            (isTrans≤ᵣ _ _ _
              (absᵣ-triangle _ _)
              (≤ᵣMonotone+ᵣ _ _ _ _ Df* Dg*))
            Cf*))
        thirds≡ε))

DerivativeOfℙ· : ∀ a b → a <ᵣ b
  → (f g f' g' : ∀ x → x ∈ intervalℙ a b → ℝ)
  → Bounded (intervalℙ a b) f
  → Bounded (intervalℙ a b) g
  → IsUContinuousℙ (intervalℙ a b) f
  → Bounded (intervalℙ a b) g'
  → DerivativeOfℙ intervalℙ a b , f is f'
  → DerivativeOfℙ intervalℙ a b , g is g'
  → DerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ g x x∈)
    is λ x x∈ → f' x x∈ ·ᵣ g x x∈ +ᵣ g' x x∈ ·ᵣ f x x∈
DerivativeOfℙ· a b a<b f g f' g' (bf , <bf) (bg , <bg) ucf (bg' , <bg') dF dG x x∈ ε = do
  let M = max₊ (max₊ bf bg) bg'
  let ε' = ([ 1 / 3 ]₊ ·₊ ε) ·₊ invℚ₊ M
  (δf' , Df) ← dF x x∈ ε'
  (δg' , Dg) ← dG x x∈ ε'
  let (δf , Cf) = ucf ε'
  let δ = min₊ (min₊ δf' δg') (δf /2₊)
  return (δ , λ y y∈ y-x≤δ →
    let h = y -ᵣ x
        Ef = derivativeErrorℙ (intervalℙ a b) f f' x x∈ y y∈
        Eg = derivativeErrorℙ (intervalℙ a b) g g' x x∈ y y∈
        q = fst ([ 1 / 3 ]₊ ·₊ ε)
        c = rat q
        ∣h∣ = absᵣ h
        third = c ·ᵣ ∣h∣

        err≡ : derivativeErrorℙ (intervalℙ a b)
                 (λ x₁ x∈₁ → f x₁ x∈₁ ·ᵣ g x₁ x∈₁)
                 (λ x₁ x∈₁ → f' x₁ x∈₁ ·ᵣ g x₁ x∈₁
                               +ᵣ g' x₁ x∈₁ ·ᵣ f x₁ x∈₁)
                 x x∈ y y∈
             ≡ g x x∈ ·ᵣ Ef +ᵣ f y y∈ ·ᵣ Eg
               +ᵣ (g' x x∈ ·ᵣ h) ·ᵣ (f y y∈ -ᵣ f x x∈)
        err≡ = ℝ!

        Mε'≡c : rat (fst M) ·ᵣ rat (fst ε') ≡ c
        Mε'≡c =
          sym (rat·ᵣrat (fst M) (fst ε'))
          ∙ cong rat
              (ℚ.·Assoc (fst M) q (fst (invℚ₊ M))
               ∙ cong (λ z → z ℚ.· fst (invℚ₊ M)) (ℚ.·Comm (fst M) q)
               ∙ sym (ℚ.·Assoc q (fst M) (fst (invℚ₊ M)))
               ∙ cong (q ℚ.·_) (ℚ.x·invℚ₊[x] M)
               ∙ ℚ.·IdR q)

        Mε'∣h∣≡third : rat (fst M) ·ᵣ (rat (fst ε') ·ᵣ ∣h∣) ≡ third
        Mε'∣h∣≡third =
          ·ᵣAssoc _ _ _ ∙ cong (_·ᵣ ∣h∣) Mε'≡c

        Mε'∣h∣≡third' : (rat (fst M) ·ᵣ rat (fst ε')) ·ᵣ ∣h∣ ≡ third
        Mε'∣h∣≡third' = cong (_·ᵣ ∣h∣) Mε'≡c

        ∣h∣Mε'≡third : ∣h∣ ·ᵣ (rat (fst M) ·ᵣ rat (fst ε')) ≡ third
        ∣h∣Mε'≡third =
          ·ᵣComm ∣h∣ (rat (fst M) ·ᵣ rat (fst ε')) ∙ Mε'∣h∣≡third'

        ∣h∣≤δf' : ∣h∣ ≤ᵣ rat (fst δf')
        ∣h∣≤δf' =
          isTrans≤ᵣ _ _ _ y-x≤δ
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.min≤ (ℚ.min (fst δf') (fst δg')) (fst (δf /2₊)))
                (ℚ.min≤ (fst δf') (fst δg'))))

        ∣h∣≤δg' : ∣h∣ ≤ᵣ rat (fst δg')
        ∣h∣≤δg' =
          isTrans≤ᵣ _ _ _ y-x≤δ
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.min≤ (ℚ.min (fst δf') (fst δg')) (fst (δf /2₊)))
                (ℚ.min≤' (fst δf') (fst δg'))))

        ∣h∣≤δf/2 : ∣h∣ ≤ᵣ rat (fst (δf /2₊))
        ∣h∣≤δf/2 =
          isTrans≤ᵣ _ _ _ y-x≤δ
            (≤ℚ→≤ᵣ _ _
              (ℚ.min≤' (ℚ.min (fst δf') (fst δg')) (fst (δf /2₊))))

        ∣g[x]∣≤M : absᵣ (g x x∈) ≤ᵣ rat (fst M)
        ∣g[x]∣≤M =
          isTrans≤ᵣ _ _ _ (<bg x x∈)
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.≤max' (fst bf) (fst bg))
                (ℚ.≤max _ (fst bg'))))

        ∣f[y]∣≤M : absᵣ (f y y∈) ≤ᵣ rat (fst M)
        ∣f[y]∣≤M =
          isTrans≤ᵣ _ _ _ (<bf y y∈)
            (≤ℚ→≤ᵣ _ _
              (ℚ.isTrans≤ _ _ _
                (ℚ.≤max (fst bf) (fst bg))
                (ℚ.≤max _ (fst bg'))))

        ∣g'[x]∣≤M : absᵣ (g' x x∈) ≤ᵣ rat (fst M)
        ∣g'[x]∣≤M =
          isTrans≤ᵣ _ _ _ (<bg' x x∈)
            (≤ℚ→≤ᵣ _ _
              (ℚ.≤max' (ℚ.max (fst bf) (fst bg)) (fst bg')))

        Df* : absᵣ (g x x∈ ·ᵣ Ef) ≤ᵣ third
        Df* =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _)
            (isTrans≤≡ᵣ _ _ _
              (≤ᵣ₊Monotone·ᵣ _ _ _ _
                (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ M))
                (0≤absᵣ Ef)
                ∣g[x]∣≤M
                (Df y y∈ ∣h∣≤δf'))
              Mε'∣h∣≡third)

        Dg* : absᵣ (f y y∈ ·ᵣ Eg) ≤ᵣ third
        Dg* =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _)
            (isTrans≤≡ᵣ _ _ _
              (≤ᵣ₊Monotone·ᵣ _ _ _ _
                (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ M))
                (0≤absᵣ Eg)
                ∣f[y]∣≤M
                (Dg y y∈ ∣h∣≤δg'))
              Mε'∣h∣≡third)

        Cf* : absᵣ ((g' x x∈ ·ᵣ h) ·ᵣ (f y y∈ -ᵣ f x x∈)) ≤ᵣ third
        Cf* =
          isTrans≡≤ᵣ _ _ _
            (·absᵣ _ _
             ∙ cong₂ _·ᵣ_ (·absᵣ _ _) refl
             ∙ ℝ!)
            (isTrans≤≡ᵣ _ _ _
              (≤ᵣ-o·ᵣ _ _ ∣h∣ (0≤absᵣ h)
                (≤ᵣ₊Monotone·ᵣ _ _ _ _
                  (≤ℚ→≤ᵣ _ _ (ℚ.0≤ℚ₊ M))
                  (0≤absᵣ (f y y∈ -ᵣ f x x∈))
                  ∣g'[x]∣≤M
                  (<ᵣWeaken≤ᵣ _ _
                    (isTrans≡<ᵣ _ _ _
                      (minusComm-absᵣ (f y y∈) (f x x∈))
                      (fst (∼≃abs<ε _ _ _)
                        (Cf x y x∈ y∈
                          (invEq (∼≃abs<ε x y δf)
                            (isTrans≡<ᵣ _ _ _
                              (minusComm-absᵣ x y)
                              (isTrans≤<ᵣ _ _ _
                                ∣h∣≤δf/2
                                (<ℚ→<ᵣ _ _ (/2₊<id δf)))))))))))
              ∣h∣Mε'≡third)

        thirds≡ε : third +ᵣ third +ᵣ third ≡ rat (fst ε) ·ᵣ ∣h∣
        thirds≡ε =
            cong₂ _+ᵣ_
              (cong₂ _+ᵣ_ (·ᵣComm _ _) (·ᵣComm _ _))
              (·ᵣComm _ _)
          ∙ cong (_+ᵣ (∣h∣ ·ᵣ c)) (sym (·DistL+ ∣h∣ c c))
          ∙ sym (·DistL+ ∣h∣ (c +ᵣ c) c)
          ∙ cong (∣h∣ ·ᵣ_)
              (cong (_+ᵣ c) (+ᵣ-rat q q)
               ∙ +ᵣ-rat (q ℚ.+ q) q
               ∙ cong rat ℚ!)
          ∙ ·ᵣComm _ _
    in isTrans≡≤ᵣ _ _ _
      (cong absᵣ err≡)
      (isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _
          (absᵣ-triangle _ _)
          (≤ᵣMonotone+ᵣ _ _ _ _
            (isTrans≤ᵣ _ _ _
              (absᵣ-triangle _ _)
              (≤ᵣMonotone+ᵣ _ _ _ _ Df* Dg*))
            Cf*))
        thirds≡ε))

uDerivativeOfℙ² : ∀ a b → a <ᵣ b
  → (f f' : ∀ x → x ∈ intervalℙ a b → ℝ)
  → Bounded (intervalℙ a b) f
  → IsUContinuousℙ (intervalℙ a b) f
  → Bounded (intervalℙ a b) f'
  → uDerivativeOfℙ intervalℙ a b , f is f'
  → uDerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ f x x∈)
    is λ x x∈ → 2 ·ᵣ (f' x x∈ ·ᵣ f x x∈)
uDerivativeOfℙ² a b a<b f f' bf ucf bf' df =
  subst (uDerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ f x x∈)
    is_) (funExt₂ λ _ _ → ℝ!)
     (uDerivativeOfℙ· a b a<b f f f' f' bf bf ucf bf' df df)

DerivativeOfℙ² : ∀ a b → a <ᵣ b
  → (f f' : ∀ x → x ∈ intervalℙ a b → ℝ)
  → Bounded (intervalℙ a b) f
  → IsUContinuousℙ (intervalℙ a b) f
  → Bounded (intervalℙ a b) f'
  → DerivativeOfℙ intervalℙ a b , f is f'
  → DerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ f x x∈)
    is λ x x∈ → 2 ·ᵣ (f' x x∈ ·ᵣ f x x∈)
DerivativeOfℙ² a b a<b f f' bf ucf bf' df =
  subst (DerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ f x x∈)
    is_) (funExt₂ λ _ _ → ℝ!)
     (DerivativeOfℙ· a b a<b f f f' f' bf bf ucf bf' df df)

uDerivativeOfℙ-transl : ∀ P f f' Δ
    → uDerivativeOfℙ P , f is f'
    → uDerivativeOfℙ P ∘ (_+ᵣ Δ) , (λ x x∈ → f (x +ᵣ Δ) x∈) is
         (λ x x∈ → f' (x +ᵣ Δ) x∈)
uDerivativeOfℙ-transl P f f' Δ df ε =
  PT.map (map-snd (λ X x x∈ y y∈ y-x≤ →
    isTrans≡≤ᵣ _ _ _
      (cong absᵣ
        (cong₂ _-ᵣ_
          (cong₂ _-ᵣ_
            refl
            refl)
          (cong₂ _·ᵣ_ refl ℝ!)))
      (isTrans≤≡ᵣ _ _ _
        (X (x +ᵣ Δ) x∈ (y +ᵣ Δ) y∈
          (isTrans≡≤ᵣ _ _ _ (cong absᵣ ℝ!) y-x≤))
        (cong (rat (fst ε) ·ᵣ_) (cong absᵣ ℝ!)))))
    (df ε)

DerivativeOfℙ-transl : ∀ P f f' Δ
    → DerivativeOfℙ P , f is f'
    → DerivativeOfℙ P ∘ (_+ᵣ Δ) , (λ x x∈ → f (x +ᵣ Δ) x∈) is
         (λ x x∈ → f' (x +ᵣ Δ) x∈)
DerivativeOfℙ-transl P f f' Δ df x x∈ ε =
  PT.map (map-snd (λ X y y∈ y-x≤ →
    isTrans≡≤ᵣ _ _ _
      (cong absᵣ
        (cong₂ _-ᵣ_
          (cong₂ _-ᵣ_
            refl
            refl)
          (cong₂ _·ᵣ_ refl ℝ!)))
      (isTrans≤≡ᵣ _ _ _
        (X (y +ᵣ Δ) y∈
          (isTrans≡≤ᵣ _ _ _ (cong absᵣ ℝ!) y-x≤))
        (cong (rat (fst ε) ·ᵣ_) (cong absᵣ ℝ!)))))
    (df (x +ᵣ Δ) x∈ ε)
