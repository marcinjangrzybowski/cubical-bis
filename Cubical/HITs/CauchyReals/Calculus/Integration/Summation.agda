module Cubical.HITs.CauchyReals.Calculus.Integration.Summation where

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
import Cubical.Data.Nat.Order.Inductive as ℕ
import Cubical.Data.Nat.Logarithm as ℕLog
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
  hiding (ElimFinSS; go-tail-finj; go-tail-flast)
import Cubical.Data.FinData as FD
import Cubical.Data.Fin.Properties as FinP
open FinP public using (ElimFinSS; go-tail-finj; go-tail-flast)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Algebra.CommSemiring.Base using (CommSemiring→Semiring)
open import Cubical.Algebra.CommSemiring.Instances.Nat using (ℕasCSR)
import Cubical.Algebra.Semiring.Properties as Semiring
import Cubical.Algebra.Ring.BigOps as RingBigOps
import Cubical.Algebra.OrderedCommRing.Properties as Ordered


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
  hiding (≤Cont₂; IsContinuous-₂∘)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
  using (IsContinuous-₂∘)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order using (≤Cont₂)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (abs-max)
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using
  (ℝOrderedCommRing)
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base


open import Cubical.Tactics.CauchyReals.ExpressionLifting


open import Cubical.HITs.CauchyReals.Foundation.Rationals


open ℚ using (_⁻¹₊)

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


open import Cubical.Tactics.CauchyReals.ExpressionLifting


private
  variable
    ℓ : Level
    A A' B B' : Type ℓ

  module ℕExponentiation =
    Semiring.ExponentiationLaws
      (CommSemiring→Semiring ℕasCSR) (ℕ._^_)
      (λ _ → refl) (λ _ _ → refl)

  module ℝOrder = Ordered.OrderedCommRingTheory ℝOrderedCommRing
  module ℝSum = Ordered.SumTheory ℝOrderedCommRing
  module ℝRingSum = RingBigOps.Sum
    (Ordered.OrderedCommRing→Ring ℝOrderedCommRing)

clampCases : ∀ a b → a ℚ.≤ b → ∀ u v → u ℚ.≤ v →
            (ℚ.clamp a b v ℚ.- ℚ.clamp a b u ≡ 0)
              ⊎ ((a ℚ.≤ v) × (u ℚ.≤ b))
clampCases a b a≤b u v u≤v =
  ⊎.rec (λ a≤v →
     ⊎.rec (λ u≤b → inr (a≤v , u≤b))
       (λ b<u → inl
            (cong (ℚ._-_ (ℚ.clamp a b v)) (sym (ℚ.minComm (ℚ.max a v) b ∙∙
           ℚ.≤→min _ (ℚ.max a v) ((ℚ.isTrans≤ b u _ (ℚ.<Weaken≤ b u b<u)
            (ℚ.isTrans≤ u v _ u≤v (ℚ.≤max' a v )))) ∙
            sym (ℚ.≤→min b (ℚ.max a u)
              ((ℚ.isTrans≤ b u _ (ℚ.<Weaken≤ b u b<u)
            ((ℚ.≤max' a u )))))
             ∙∙ ℚ.minComm b (ℚ.max a u))) ∙ ℚ!))
      (ℚ.Dichotomyℚ u b))
   (λ v<a → inl
         (cong (ℚ._-_ (ℚ.clamp a b v)) (sym ((ℚ.minComm (ℚ.max a v) b ∙∙
        cong (ℚ.min b) (ℚ.maxComm a v ∙ ℚ.≤→max v a (ℚ.<Weaken≤ v a v<a) ∙
          sym (ℚ.≤→max u a (ℚ.isTrans≤  u v _ u≤v (ℚ.<Weaken≤ v a v<a)))
           ∙ ℚ.maxComm u a )
       ∙∙ ℚ.minComm b (ℚ.max a u)))) ∙ ℚ!))
   (ℚ.Dichotomyℚ a v)


⊎-⊎-×-rec : A ⊎ B → A' ⊎ B' → (A ⊎ A') ⊎ (B × B')
⊎-⊎-×-rec (inl x) _ = inl (inl x)
⊎-⊎-×-rec (inr _) (inl x) = inl (inr x)
⊎-⊎-×-rec (inr x) (inr x₁) = inr (x , x₁)

≤x→clamp : ∀ L L' x → L' ℚ.≤ x → ℚ.clamp L L' x ≡ L'
≤x→clamp L L' x L'≤x = ℚ.minComm (ℚ.max L x) L'
  ∙ ℚ.≤→min L' (ℚ.max L x) (ℚ.isTrans≤ L' x _ L'≤x (ℚ.≤max' L x))

x≤→clamp : ∀ L L' x → L ℚ.≤ L' → x ℚ.≤ L → ℚ.clamp L L' x ≡ L
x≤→clamp L L' x L≤L' x≤L = ℚ.≤→min (ℚ.max L x) L'
  (subst (ℚ.max L x ℚ.≤_) (ℚ.maxIdem L')
   (ℚ.≤MonotoneMax L L' x L' L≤L' (ℚ.isTrans≤ x L L' x≤L L≤L')) ) ∙
  ℚ.maxComm L x ∙ ℚ.≤→max x L x≤L


clampDegen : ∀ a b x → b ℚ.≤ a → ℚ.clamp a b x ≡ b
clampDegen a b x b≤a =
  ℚ.minComm (ℚ.max a x) b ∙
   ℚ.≤→min _ _ (ℚ.isTrans≤ b a _ b≤a (ℚ.≤max a x))



ℚclampInterval-delta : ∀ a b a' b'
          → a  ℚ.≤ b
          → a' ℚ.≤ b'
               → ℚ.clamp a  b  b' ℚ.- ℚ.clamp a  b  a'
               ≡ ℚ.clamp a' b' b  ℚ.- ℚ.clamp a' b' a
ℚclampInterval-delta a b a' b' a≤b a'≤b' =
 ⊎.rec (⊎.rec
         (hhh a b a' b' a≤b a'≤b'  )
         (sym ∘ hhh a' b' a b a'≤b' a≤b))
       (λ (a≤b' , a'≤b) →
          hhh' a b a' b' a≤b a'≤b' a≤b' a'≤b
           ∙∙ cong₂ ℚ._-_ (ℚ.minComm b' b) (ℚ.maxComm a a') ∙∙
           sym (hhh' a' b' a b a'≤b' a≤b a'≤b a≤b') )
       (⊎-⊎-×-rec
          (ℚ.≤cases b' a)
          (ℚ.≤cases b a'))

  where

  hhh' : ∀ a b a' b'
         → a  ℚ.≤ b
         → a' ℚ.≤ b'
         → a ℚ.≤ b' → a' ℚ.≤ b
              → ℚ.clamp a  b  b' ℚ.- ℚ.clamp a  b  a'
              ≡ ℚ.min b' b ℚ.- ℚ.max a a'
  hhh' a b a' b' a≤b a'≤b' a≤b' a'≤b =
    cong₂ ℚ._-_ (cong (flip ℚ.min b) (ℚ.≤→max a b' a≤b'))
            (ℚ.≤→min (ℚ.max a a') b
             (subst (ℚ.max a a' ℚ.≤_) (ℚ.maxIdem b)
              (ℚ.≤MonotoneMax a b a' b a≤b a'≤b)) )



  hhh : ∀ a b a' b'
         → a  ℚ.≤ b
         → a' ℚ.≤ b'
         → b' ℚ.≤ a
              → ℚ.clamp a  b  b' ℚ.- ℚ.clamp a  b  a'
              ≡ ℚ.clamp a' b' b  ℚ.- ℚ.clamp a' b' a
  hhh a b a' b' a≤b a'≤b' b'≤a =
     cong₂ ℚ._-_ (x≤→clamp a b b' a≤b b'≤a)
                 (x≤→clamp a b a' a≤b (ℚ.isTrans≤ a' b' a a'≤b' b'≤a))
      ∙∙ ℚ.+InvR a ∙ sym (ℚ.+InvR b') ∙∙
      cong₂ ℚ._-_
        (sym (≤x→clamp a' b' b (ℚ.isTrans≤ b' a b b'≤a a≤b)))
        (sym (≤x→clamp a' b' a b'≤a))

clamp-dist : ∀ a b x y →
  abs (ℚ.clamp a b x ℚ.- ℚ.clamp a b y) ℚ.≤ abs (b ℚ.- a)
clamp-dist a b =
  ⊎.rec
    (λ a≤b →
      ℚ.elimBy≤
       (λ x y X →
         subst (ℚ._≤ abs (b ℚ.- a))
          (abs-Comm (ℚ.clamp a b x) (ℚ.clamp a b y)) X)
       λ x y x≤y →
         subst (ℚ._≤ abs (b ℚ.- a))
           (cong abs
             (sym (ℚclampInterval-delta a b x y a≤b x≤y))
           ∙ abs-Comm (ℚ.clamp a b y) (ℚ.clamp a b x))
           (ℚ.clampDist x y a b))
    (λ b≤a x y →
      subst (ℚ._≤ abs (b ℚ.- a))
       (cong {x = 0} abs (ℚ! ∙ cong (ℚ._-_ (ℚ.clamp a b x) ) (clampDegen a b x b≤a ∙ sym (clampDegen a b y b≤a))))
       
       (0≤abs (b ℚ.- a)) )
   (ℚ.≤cases a b)

opaque
 unfolding minᵣ NonExpanding₂.go
 clampᵣ-dist : ∀ a b x y → absᵣ (clampᵣ a b x -ᵣ clampᵣ a b y) ≤ᵣ absᵣ (b -ᵣ a)
 clampᵣ-dist a b x y = ≤Cont₂
  {f₀ x y} {λ a b → absᵣ (b -ᵣ a)}
  (cont∘₂ IsContinuousAbsᵣ
         (IsContinuous-₂∘ (IsContinuousClamp₂ _) (IsContinuousClamp₂ _)))
    ((cont∘₂ IsContinuousAbsᵣ
         (IsContinuous-₂∘

           ((λ _ → IsContinuousId) , ((λ _ → IsContinuousConst _)))
           (((λ _ → IsContinuousConst _)) ,
             (λ _ → IsContinuousId))) ))
   (λ aℚ bℚ →  let a = (rat aℚ) ; b = (rat bℚ) in
     ≤Cont₂ {λ x y → f₀ x y a b} {λ _ _ → absᵣ (b -ᵣ a)}
       (cont∘₂ IsContinuousAbsᵣ
         (IsContinuous-₂∘
           (((λ _ → IsContinuousConst _)) ,
             (λ _ → IsContinuousClamp a b))
           ((λ _ → IsContinuousClamp a b) , ((λ _ → IsContinuousConst _)))) )
         ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _))
       (λ x y → subst2 _≤ᵣ_
         (sym (absᵣ-rat _) ∙
            cong absᵣ (sym (-ᵣ-rat₂ _ _) ))
         (sym (absᵣ-rat _) ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _) ))
         (≤ℚ→≤ᵣ _ _ (clamp-dist aℚ bℚ x y))) x y)
  a b
  where
  f₀ : ℝ → ℝ → ℝ → ℝ → ℝ
  f₀ x y a b  = absᵣ (clampᵣ a b x -ᵣ clampᵣ a b y)


ℕ₊₁→ℕ-lem : ∀ n m → n ≡ ℕ₊₁→ℕ m → (1+ predℕ n) ≡ m
ℕ₊₁→ℕ-lem zero m x = ⊥.rec (ℕ.znots x )
ℕ₊₁→ℕ-lem (suc n) m x = cong 1+_ (ℕ.injSuc x)






substFin : ∀ {n} {m} → n ≡ m → Fin n → Fin m
substFin p = map-snd (subst (_ ℕ.<ᵗ_) p)

Fin→FinVec : ∀ {n} → (Fin n → A) → FD.FinVec A n
Fin→FinVec {n = n} V = V ∘ FinP.FinData→Fin n

foldFin+≡+∑ : ∀ n (f : A → ℝ) x (V : Fin n → A) →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
    ≡ x +ᵣ ℝSum.∑ (Fin→FinVec {n = n} (f ∘ V))
foldFin+≡+∑ zero f x V = sym (+IdR x)
foldFin+≡+∑ (suc n) f x V =
  foldFin+≡+∑ n f (x +ᵣ f (V fzero)) (V ∘ fsuc)
  ∙ sym (+ᵣAssoc x (f (V fzero))
      (ℝSum.∑ (Fin→FinVec {n = n} (f ∘ V ∘ fsuc))))

foldFin+≡∑ : ∀ n (f : A → ℝ) (V : Fin n → A) →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) 0 V
    ≡ ℝSum.∑ (Fin→FinVec {n = n} (f ∘ V))
foldFin+≡∑ n f V = foldFin+≡+∑ n f 0 V ∙ +IdL _

abs∑≤∑absᵣ : ∀ {n} (V : FD.Fin n → ℝ) →
  absᵣ (ℝSum.∑ V) ≤ᵣ ℝSum.∑ (absᵣ ∘ V)
abs∑≤∑absᵣ V =
  subst2 _≤ᵣ_
    (sym (abs-max (ℝSum.∑ V)))
    (sym (ℝSum.∑Ext (abs-max ∘ V)))
    (ℝSum.abs∑≤∑absFinVec V)

foldFin+ᵣ : ∀ n V (f : A → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) (x +ᵣ x') V ≡
   x +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x' V
foldFin+ᵣ n V f x x' =
  foldFin+≡+∑ n f (x +ᵣ x') V
  ∙ sym (+ᵣAssoc x x' _)
  ∙ cong (x +ᵣ_) (sym (foldFin+≡+∑ n f x' V))

foldFin+0ᵣ : ∀ n V (f : A → ℝ) x →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V ≡
   x +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) 0 V
foldFin+0ᵣ n V f x =
  foldFin+≡+∑ n f x V
  ∙ cong (x +ᵣ_) (sym (foldFin+≡∑ n f V))


foldFin+map : ∀ n x (f : A → ℝ) (g : B → A) V →
  foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x (g ∘ V)
    ≡ foldlFin {B = ℝ} {A = B} {n = n} (λ a y → a +ᵣ f (g y)) x V
foldFin+map zero x f g V = refl
foldFin+map (suc n) x f g V =
 foldFin+map n (x +ᵣ f ((g ∘ V) fzero)) f g (V ∘ fsuc)


zip-foldFin+ᵣ : ∀ n V V' (f : A → ℝ) (f' : A' → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
    +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V' ≡
   foldlFin {B = ℝ} {n = n} (λ a (y , y') → a +ᵣ (f y +ᵣ f' y')) (x +ᵣ x')
    λ x → V x , V' x
zip-foldFin+ᵣ n V V' f f' x x' =
  cong₂ _+ᵣ_
    (foldFin+≡+∑ n f x V)
    (foldFin+≡+∑ n f' x' V')
  ∙ Rℝ.+ShufflePairs x F x' F'
  ∙ cong ((x +ᵣ x') +ᵣ_)
      (sym (ℝSum.∑Split
        (Fin→FinVec {n = n} (f ∘ V))
        (Fin→FinVec {n = n} (f' ∘ V'))))
  ∙ sym (foldFin+≡+∑ n
      (λ (y , y') → f y +ᵣ f' y') (x +ᵣ x')
      (λ k → V k , V' k))
  where
  F = ℝSum.∑ (Fin→FinVec {n = n} (f ∘ V))
  F' = ℝSum.∑ (Fin→FinVec {n = n} (f' ∘ V'))

zip-foldFin+ᵣ' : ∀ n V (f : A → ℝ) (f' : A → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
    +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V ≡
   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ (f y +ᵣ f' y)) (x +ᵣ x')
    V
zip-foldFin+ᵣ' n V f f' x x' =
  zip-foldFin+ᵣ n V V f f' x x'
  ∙ foldFin+map n (x +ᵣ x')
      (λ (y , y') → f y +ᵣ f' y') (λ y → y , y) V


foldFin·DistL : ∀ n (f : A → ℝ) α x V →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ α ·ᵣ f y) (α ·ᵣ x) V
      ≡ α ·ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) (x) V
foldFin·DistL n f α x V =
  foldFin+≡+∑ n (λ y → α ·ᵣ f y) (α ·ᵣ x) V
  ∙ cong ((α ·ᵣ x) +ᵣ_)
      (sym (ℝSum.∑Mulrdist α
        (Fin→FinVec {n = n} (f ∘ V))))
  ∙ sym (·DistL+ α x _)
  ∙ cong (α ·ᵣ_) (sym (foldFin+≡+∑ n f x V))


foldFin+transpose : ∀ n n' (f : Fin n → Fin n' → ℝ) x →
  foldlFin {B = ℝ} {n = n} (λ a k → a +ᵣ
      foldlFin {B = ℝ} {n = n'} (λ a k' → a +ᵣ
      f k k') (fromNat zero) (idfun _)) x (idfun _)
      ≡ foldlFin {B = ℝ} {n = n'} (λ a k' → a +ᵣ
           foldlFin {B = ℝ} {n = n} (λ a k → a +ᵣ
           f k k') (fromNat zero) (idfun _)) x (idfun _)
foldFin+transpose n n' f x =
  foldFin+≡+∑ n
    (λ k → foldlFin {B = ℝ} {n = n'}
      (λ a k' → a +ᵣ f k k') 0 (idfun _))
    x (idfun _)
  ∙ cong (x +ᵣ_)
      (ℝSum.∑Ext (λ k →
        foldFin+≡∑ n' (f (FinP.FinData→Fin n k)) (idfun _))
      ∙ ℝSum.∑Exchange
          (λ k k' → f (FinP.FinData→Fin n k)
                         (FinP.FinData→Fin n' k'))
      ∙ ℝSum.∑Ext (λ k' →
        sym (foldFin+≡∑ n
          (λ k → f k (FinP.FinData→Fin n' k')) (idfun _))))
  ∙ sym (foldFin+≡+∑ n'
      (λ k' → foldlFin {B = ℝ} {n = n}
        (λ a k → a +ᵣ f k k') 0 (idfun _))
      x (idfun _))



foldFin·DistL' : ∀ n (f : A → ℝ) α V →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ α ·ᵣ f y) 0 V
      ≡ α ·ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) 0 V
foldFin·DistL' n f α V =
  foldFin+≡∑ n (λ y → α ·ᵣ f y) V
  ∙ sym (ℝSum.∑Mulrdist α
      (Fin→FinVec {n = n} (f ∘ V)))
  ∙ cong (α ·ᵣ_) (sym (foldFin+≡∑ n f V))



zip-foldFin-ᵣ : ∀ n V V' (f : A → ℝ) (f' : A' → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
    -ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V' ≡
   foldlFin {B = ℝ} {n = n} (λ a (y , y') → a +ᵣ (f y -ᵣ f' y')) (x -ᵣ x')
    λ x → V x , V' x
zip-foldFin-ᵣ n V V' f f' x x' =
  cong₂ _-ᵣ_
    (foldFin+≡+∑ n f x V)
    (foldFin+≡+∑ n f' x' V')
  ∙ cong ((x +ᵣ F) +ᵣ_) (sym (Rℝ.-Dist x' F'))
  ∙ Rℝ.+ShufflePairs x F (-ᵣ x') (-ᵣ F')
  ∙ cong ((x -ᵣ x') +ᵣ_)
      (sym (ℝRingSum.∑Split-
        (Fin→FinVec {n = n} (f ∘ V))
        (Fin→FinVec {n = n} (f' ∘ V'))))
  ∙ sym (foldFin+≡+∑ n
      (λ (y , y') → f y -ᵣ f' y') (x -ᵣ x')
      (λ k → V k , V' k))
  where
  F = ℝSum.∑ (Fin→FinVec {n = n} (f ∘ V))
  F' = ℝSum.∑ (Fin→FinVec {n = n} (f' ∘ V'))


foldFin+≤ : ∀ n x x' (f : A → ℝ) (f' : A' → ℝ) V V' →
   x ≤ᵣ x' →
  (∀ k → f (V k) ≤ᵣ f' (V' k)) →
  foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V
    ≤ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'

foldFin+≤ n x x' f f' V V' x≤x' f≤f' =
  subst2 _≤ᵣ_
    (sym (foldFin+≡+∑ n f x V))
    (sym (foldFin+≡+∑ n f' x' V'))
    (ℝOrder.+Mono≤ x x'
      (ℝSum.∑ (Fin→FinVec {n = n} (f ∘ V)))
      (ℝSum.∑ (Fin→FinVec {n = n} (f' ∘ V'))) x≤x'
      (ℝSum.∑Mono≤
        (Fin→FinVec {n = n} (f ∘ V))
        (Fin→FinVec {n = n} (f' ∘ V'))
        (f≤f' ∘ FinP.FinData→Fin n)))


foldFin+< : ∀ n x x' (f : A → ℝ) (f' : A' → ℝ) V V' →
   x ≤ᵣ x' →
  (∀ k → f (V k) <ᵣ f' (V' k)) →
  foldlFin {B = ℝ} {A = A} {n = (suc n)} (λ a y → a +ᵣ f y) x V
    <ᵣ foldlFin {B = ℝ} {A = A'} {n = (suc n)} (λ a y → a +ᵣ f' y) x' V'

foldFin+< n x x' f f' V V' x≤x' X =
  subst2 _<ᵣ_
    (sym (foldFin+≡+∑ (suc n) f x V))
    (sym (foldFin+≡+∑ (suc n) f' x' V'))
    (≤<ᵣMonotone+ᵣ _ _ _ _ x≤x'
      (ℝSum.∑Mono<
        (Fin→FinVec {n = suc n} (f ∘ V))
        (Fin→FinVec {n = suc n} (f' ∘ V'))
        ℕ.zero-<-suc (X ∘ FinP.FinData→Fin (suc n))))


foldFin+<-abs : ∀ n → zero ℕ.< n → ∀ x x' (f : A → ℝ) (f' : A' → ℝ) V V'  →
   absᵣ x ≤ᵣ x' →
  (∀ k → absᵣ (f (V k)) <ᵣ f' (V' k)) →
  absᵣ (foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V)
    <ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'

foldFin+<-abs n 0<n x x' f f' V V' x≤x' X =
  subst2 _<ᵣ_
    (cong absᵣ (sym (foldFin+≡+∑ n f x V)))
    (sym (foldFin+≡+∑ n f' x' V'))
    (isTrans≤<ᵣ _ _ _ (absᵣ-triangle _ _)
      (≤<ᵣMonotone+ᵣ _ _ _ _ x≤x'
        (isTrans≤<ᵣ _ _ _
          (abs∑≤∑absᵣ (Fin→FinVec {n = n} (f ∘ V)))
          (ℝSum.∑Mono<
            (Fin→FinVec {n = n} (absᵣ ∘ f ∘ V))
            (Fin→FinVec {n = n} (f' ∘ V')) 0<n
            (X ∘ FinP.FinData→Fin n)))))

foldFin+≤-abs : ∀ n → ∀ x x' (f : A → ℝ) (f' : A' → ℝ) V V'  →
   absᵣ x ≤ᵣ x' →
  (∀ k → absᵣ (f (V k)) ≤ᵣ f' (V' k)) →
  absᵣ (foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V)
    ≤ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'

foldFin+≤-abs n x x' f f' V V' x≤x' X =
  subst2 _≤ᵣ_
    (cong absᵣ (sym (foldFin+≡+∑ n f x V)))
    (sym (foldFin+≡+∑ n f' x' V'))
    (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
      (≤ᵣMonotone+ᵣ _ _ _ _ x≤x'
        (isTrans≤ᵣ _ _ _
          (abs∑≤∑absᵣ (Fin→FinVec {n = n} (f ∘ V)))
          (ℝSum.∑Mono≤
            (Fin→FinVec {n = n} (absᵣ ∘ f ∘ V))
            (Fin→FinVec {n = n} (f' ∘ V'))
            (X ∘ FinP.FinData→Fin n)))))


foldFin+Const : ∀ n x V →
  foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ x) 0 V
    ≡ fromNat n ·ᵣ x
foldFin+Const n x V =
  foldFin+≡∑ n (λ _ → x) V
  ∙ ℝRingSum.∑Const n x
  ∙ cong (_·ᵣ x) (fromℕ≡fromNatℝ n)

foldlFin-substN : ∀ {n n'} → (p : n ≡ n') → ∀ f b v →
            foldlFin {B = B} {A = A} {n} f b v ≡
              foldlFin {B = B} {A = A} {n'} f b (v ∘ substFin (sym p))
foldlFin-substN {n = n} = J (λ n' p → ∀ f b v →
            foldlFin {n = n} f b v ≡
              foldlFin {n = n'}  f b (v ∘ substFin (sym p)))
               λ f b v → cong (foldlFin {n = n} f b)
                 (funExt λ x → cong v (sym (transportRefl _)))


deltas-sum : ∀ n (f : Fin (suc n) → ℝ) →
 foldlFin {n = n} (λ a k → a +ᵣ (f (fsuc k) -ᵣ f (finj k))) 0 (idfun _) ≡
   f flast -ᵣ f fzero
deltas-sum n f =
  foldFin+≡∑ n (λ k → f (fsuc k) -ᵣ f (finj k)) (idfun _)
  ∙ ℝRingSum.∑Ext (λ k →
      cong (λ z → f (fsuc (FinP.FinData→Fin n k)) -ᵣ z)
        (cong f (sym (FinP.FinData→Fin-weakenFin k))))
  ∙ ℝRingSum.∑Telescoping (Fin→FinVec {n = suc n} f)
  ∙ cong₂ _-ᵣ_ (cong f (FinP.FinData→Fin-fromℕ n)) refl


ℕ^+ : ∀ k n m → k ℕ.^ (n ℕ.+ m) ≡ (k ℕ.^ n) ℕ.· (k ℕ.^ m)
ℕ^+ k n m = sym (ℕExponentiation.·-of-^-is-^-of-+ k n m)


2^ : ℕ → ℕ
2^ zero = 1
2^ (suc x) = (2^ x) ℕ.+ (2^ x)

2^-^ : ∀ n → 2^ n ≡ 2 ℕ.^ n
2^-^ zero = refl
2^-^ (suc n) = cong₂ ℕ._+_ (2^-^ n) (2^-^ n)
 ∙ cong ((2 ℕ.^ n) ℕ.+_) (sym (ℕ.+-zero _))

dyadicLevel : ℕ → ℕ
dyadicLevel n = ℕLog.log 2 (suc n)

dyadicLevel-lower : ∀ n → 2^ (dyadicLevel n) ℕ.≤ suc n
dyadicLevel-lower n =
  subst (ℕ._≤ suc n) (sym (2^-^ (dyadicLevel n)))
    (ℕLog.Logℕ.^log≤ (ℕLog.logℕ 0 n))

dyadicLevel-upper : ∀ n → suc n ℕ.< 2^ (suc (dyadicLevel n))
dyadicLevel-upper n =
  subst (suc n ℕ.<_) (sym (2^-^ (suc (dyadicLevel n))))
    (ℕLog.Logℕ.<^1+log (ℕLog.logℕ 0 n))

2^+ : ∀ n m → 2^ (n ℕ.+ m) ≡ (2^ n) ℕ.· (2^ m)
2^+ n m =
  2^-^ (n ℕ.+ m)
    ∙ ℕ^+ 2 n m
    ∙ cong₂ ℕ._·_ (sym (2^-^ n)) (sym (2^-^ m))

injectFin+ : {m n : ℕ} → Fin m → Fin (n ℕ.+ m)
injectFin+ {m} {n} x =
  Iso.inv (FinP.Fin+≅Fin⊎Fin n m) (inr x)


injectFin+' : {m n : ℕ} → Fin n → Fin (n ℕ.+ m)
injectFin+' {m} {n} x =
  Iso.inv (FinP.Fin+≅Fin⊎Fin n m) (inl x)

fsuc∘inj' : {n m : ℕ} → ∀ x → fsuc  {n ℕ.+ (suc m)} (injectFin+' {suc m} {n} x) ≡
                 injectFin+' {suc m} {suc n} (fsuc x)
fsuc∘inj' {n} {m} x = toℕ-injective {(suc n) ℕ.+ (suc m)} refl

finj∘inj' : {n m : ℕ} → ∀ x → finj (injectFin+' {m} {n} x) ≡
            injectFin+' {m} {suc n} (finj x)
finj∘inj' {n} {m} x = toℕ-injective {(suc n) ℕ.+ m} refl


fsuc∘inj : {n m : ℕ} → ∀ x p →
                 fsuc {n ℕ.+ m} (injectFin+ {m} {n} x) ≡
                 (fst (injectFin+ {suc m} {n} (fsuc x))
                   , p)
fsuc∘inj {n} {m} x p = toℕ-injective {suc (n ℕ.+ m)} (sym (+-suc _ _))

finj∘inj : {n m : ℕ} → ∀ x p → finj {n ℕ.+ m} (injectFin+ {m} {n} x) ≡
            (fst (injectFin+ {suc m} {n} (finj x)) , p)
finj∘inj {n} {m} x p = toℕ-injective {suc (n ℕ.+ m)} refl




Fin+→⊎ : ∀ n m → Fin (n ℕ.+ m) → (Fin n ⊎ Fin m)
Fin+→⊎ n m = Iso.fun (FinP.Fin+≅Fin⊎Fin n m)


rec⊎-injectFin+' : ∀ {A : Type} {m} {n} f g x →
  ⊎.rec {C = A} f g (Fin+→⊎ n m (injectFin+' {m} {n} x))
                       ≡ f x
rec⊎-injectFin+' {m = m} {n = n} f g x =
  cong (⊎.rec f g) (Iso.sec (FinP.Fin+≅Fin⊎Fin n m) (inl x))



Fin+→⊎∘injectFin+' : ∀ n m x → inl x ≡ Fin+→⊎ n m (injectFin+' {m} {n} x)
Fin+→⊎∘injectFin+' n m x =
  sym (Iso.sec (FinP.Fin+≅Fin⊎Fin n m) (inl x))

Fin+→⊎∘injectFin+ : ∀ n m x → inr x ≡ Fin+→⊎ n m (injectFin+ {m} {n} x)
Fin+→⊎∘injectFin+ n m x =
  sym (Iso.sec (FinP.Fin+≅Fin⊎Fin n m) (inr x))

rec⊎-injectFin+ : ∀ {A : Type} {m} {n} f g x →
  ⊎.rec {C = A} f g (Fin+→⊎ n m (injectFin+ {m} {n} x))
                       ≡ g x
rec⊎-injectFin+ {m = m} {n = n} f g x =
  cong (⊎.rec f g) (Iso.sec (FinP.Fin+≅Fin⊎Fin n m) (inr x))

injectFin+'-flast : ∀ n m k p p' →
  Fin+→⊎ n m (injectFin+' {m} {n} (k , p)) ≡
    inl (k , p')
injectFin+'-flast n m k p p' =
  Iso.sec (FinP.Fin+≅Fin⊎Fin n m) (inl (k , p))
  ∙ cong inl (toℕ-injective {n} refl)
   


Iso-Fin+⊎-leftInv : ∀ n m a → ⊎.rec (injectFin+' {m} {n}) (injectFin+ {m} {n}) (Fin+→⊎ n m a) ≡ a
Iso-Fin+⊎-leftInv n m a =
  cong (λ f → f (Fin+→⊎ n m a)) invCompat
  ∙ Iso.ret (FinP.Fin+≅Fin⊎Fin n m) a
  where
  invCompat :
    ⊎.rec (injectFin+' {m} {n}) (injectFin+ {m} {n})
      ≡ Iso.inv (FinP.Fin+≅Fin⊎Fin n m)
  invCompat = funExt λ
    { (inl x) → refl
    ; (inr x) → refl
    }

Iso-Fin+⊎ : ∀ n m → Iso (Fin (n ℕ.+ m)) (Fin n ⊎ Fin m)
Iso-Fin+⊎ = FinP.Fin+≅Fin⊎Fin

injectFin+'-flast≡injectFin+-fzero :
 ∀ n m →
  fst (injectFin+' {m} {suc n} flast) ≡
  fst (injectFin+ {suc m} {n} fzero)
injectFin+'-flast≡injectFin+-fzero n m = sym (+-zero _)

foldFin·2 : ∀ n m → (f : B → A → B) → (b : B) →
              (V : Fin (n ℕ.+ m) → A) →
             foldlFin {n = n ℕ.+ m} f b V ≡
               foldlFin {n = m} f
                 (foldlFin {n = n} f b (V ∘ injectFin+' {m} {n}))
                  (V ∘ injectFin+ {m} {n})
foldFin·2 zero m f b V =
 cong (foldlFin {n = m} f b)
  (funExt λ x → cong V ((toℕ-injective {m} {x} {injectFin+ {m} {zero} x} refl )) )
foldFin·2 {B = B} {A = A} (suc n) m f b V =
 foldFin·2 n m f (f b (V fzero)) (V ∘ fsuc)
  ∙ cong₂ (foldlFin {_} {B} {_} {A} {m} f)
    (cong₂ (foldlFin {_} {B} {_} {A} {n} f)
      (cong (f b) (cong V (toℕ-injective {suc (n ℕ.+ m)} refl)))
        (funExt λ x → cong V (toℕ-injective {suc (n ℕ.+ m)} refl)))
     (funExt λ x → cong V (toℕ-injective {suc (n ℕ.+ m)}  refl))


foldFin-sum-concat : ∀ n m → (f : Fin (n ℕ.+ m) → ℝ) →
     foldlFin {n = n ℕ.+ m} (λ a y → a +ᵣ f y) 0 (idfun (Fin (n ℕ.+ m)))
      ≡ foldlFin {n = n} (λ a y → a +ᵣ f (injectFin+' {m} {n} y)) 0 (idfun _)
      +ᵣ foldlFin {n = m} (λ a y → a +ᵣ f (injectFin+ {m} {n} y)) 0 (idfun _)

foldFin-sum-concat n m f =
  foldFin·2 n m (λ a y → a +ᵣ f y) 0 (idfun _)
   ∙ foldFin+0ᵣ m (idfun _  ∘ injectFin+ {m} {n}) f _
   ∙ cong₂ _+ᵣ_
     (foldFin+map n _ _ injectFin+' (idfun _))
     (foldFin+map m _ _ injectFin+ (idfun _))

0<2^ : ∀ n → 0 ℕ.< 2^ n
0<2^ n =
  subst (0 ℕ.<_) (sym (2^-^ n)) (ℕ.0<^ {m = 1} n)


Fin^2· : ∀ n m → (Fin (2^ n) × Fin (2^ m))
                      → (Fin (2^ (n ℕ.+ m)))
Fin^2· n m (l , k) =
  substFin (ℕ.·-comm (2^ m) (2^ n) ∙ sym (2^+ n m))
    (equivFun (FinP.factorEquiv {n = 2^ m} {m = 2^ n}) (k , l))

Fin^2·-fst : ∀ n m x y →
  fst (Fin^2· n m (x , y)) ≡ (2^ m ℕ.· fst x) ℕ.+ fst y
Fin^2·-fst n m x y =
  FinP.factorEquiv-fst {n = 2^ m} {m = 2^ n} y x
    ∙ cong (ℕ._+ fst y) (ℕ.·-comm (fst x) (2^ m))

Fin^2·-injectFin+' : ∀ n m x y →
  (injectFin+' {2^ (n ℕ.+ m) } {2^ (n ℕ.+ m) } (Fin^2· n m (x , y))) ≡
    (Fin^2· (suc n) m (injectFin+' {2^ n} {2^ n} x , y))
Fin^2·-injectFin+' n m x y =
  toℕ-injective {2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m)}
    {injectFin+' {2^ (n ℕ.+ m) } {2^ (n ℕ.+ m) } (Fin^2· n m (x , y))}
    {(Fin^2· (suc n) m (injectFin+' {2^ n} {2^ n} x , y))}
    (Fin^2·-fst n m x y
      ∙ sym (Fin^2·-fst (suc n) m
        (injectFin+' {2^ n} {2^ n} x) y))

Fin^2·-injectFin+ : ∀ n m x y → (injectFin+ {2^ (n ℕ.+ m)} {2^ (n ℕ.+ m)} (Fin^2· n m (x , y)))
    ≡ (Fin^2· (suc n) m (injectFin+ {2^ n } {2^ n } x , y))
Fin^2·-injectFin+ n m x y =
 toℕ-injective {2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m)} 
  (cong (2^ (n ℕ.+ m) ℕ.+_) (Fin^2·-fst n m x y)
    ∙ cong (ℕ._+ (2^ m ℕ.· x .fst ℕ.+ y .fst)) (2^+ n m ∙ ℕ.·-comm (2^ n) (2^ m) )
    ∙ (ℕ.+-assoc (2^ m ℕ.· 2^ n) _ (fst y) ∙
      cong (ℕ._+ fst y) (·-distribˡ (2^ m) _ _))
    ∙ sym (Fin^2·-fst (suc n) m
      (injectFin+ {2^ n} {2^ n} x) y))

foldFin·2^ : ∀ n m → (f : B → A → B) → (b : B) →
              (V : Fin (2^ (n ℕ.+ m)) → A) →
             foldlFin {n = (2^ (n ℕ.+ m))} f b V ≡
               foldlFin {n = 2^ n} (foldlFin {n = 2^ m} f)
                 b (curry (V ∘ Fin^2· n m ))
foldFin·2^ zero m f b V = cong (foldlFin {n = 2^ m} f b)
  (funExt λ x → cong V (toℕ-injective {2^ m}
    (cong (ℕ._+ fst x) (ℕ.0≡m·0 (2^ m))
      ∙ sym (Fin^2·-fst zero m fzero x))))
foldFin·2^ (suc n) m f b V =
  foldFin·2 (2^ (n ℕ.+ m)) (2^ (n ℕ.+ m)) f b V
   ∙ foldFin·2^ n m _ _ _
    ∙ cong {x = (foldlFin {n = 2^ (n ℕ.+ m)}
            f b (V ∘ injectFin+' {2^ (n ℕ.+ m)}
             {2^ (n ℕ.+ m)}))} (λ z → foldlFin {n = 2^ n} (foldlFin {n = 2^ m} f) z
         (curry ((V ∘ injectFin+ {2^ (n ℕ.+ m)} {2^ (n ℕ.+ m)}) ∘ Fin^2· n m)))
         (foldFin·2^ n m _ _ _)

    ∙ (λ i → foldlFin {n = 2^ n} ff'
       (foldlFin {n = 2^ n} ff' b
        (λ x y → V (Fin^2·-injectFin+' n m x y i)))
       (λ x y → V (Fin^2·-injectFin+ n m x y i))) ∙
      sym (foldFin·2 (2^ n) (2^ n) ff' _ _)
 where
 ff' = (foldlFin {n = 2^ m} f)

bounded∸-reflect : ∀ m n → m ℕ.≤ n → m ≡ n ∸ (n ∸ m)
bounded∸-reflect m n m≤n =
  ℕ.inj-+m
    (ℕ.+-comm m (n ∸ m)
      ∙ ℕ.[n-m]+m m n m≤n
      ∙ sym (ℕ.[n-m]+m (n ∸ m) n (ℕ.∸-≤ n m)))

lemFin[2+n-k] : ∀ n (k : Fin (2 ℕ.+ n)) → fst k ≡ (suc (suc n) ∸ (suc (suc n) ∸ fst k))
lemFin[2+n-k] n k =
  bounded∸-reflect (fst k) (suc (suc n))
    (ℕ.<-weaken (ℕ.<ᵗ→< (snd k)))
