module Cubical.HITs.CauchyReals.Exponentiation.RealPower.Infrastructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

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


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Extension public
  using (fromLipschitz'-rat)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring public
  using (+Groupℝ; x+n·x≡sn·x)
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness public
  using (ℝ₋₊; ℝ₋₊≡)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.AdditiveAutomorphism public
  using (module AutCont; Aut[_]ᵣ; module +GrAutomorphism)
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; fromSucℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Limit

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group

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

_·ᵣ₋₊_ : ℝ₋₊ → ℝ₋₊ → ℝ₋₊
x ·ᵣ₋₊ x₁ = (fst x ·ᵣ fst x₁) , 0＃· _ _ (snd x) (snd x₁)

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

intervalℙ→dist< : ∀ a b x y → x ∈ intervalℙ a b → y ∈ intervalℙ a b
                   → absᵣ (x -ᵣ y) ≤ᵣ b -ᵣ a
intervalℙ→dist< a b x y (a≤x , x≤b) (a≤y , y≤b) =
  isTrans≡≤ᵣ _ _ _
    (abs-max (x -ᵣ y))
    (max≤-lem (x -ᵣ y) (-ᵣ (x -ᵣ y)) (b -ᵣ a)
      (≤ᵣMonotone+ᵣ _ _ _ _ x≤b (-ᵣ≤ᵣ _ _ a≤y))
      (isTrans≡≤ᵣ _ _ _
        (-[x-y]≡y-x x y)
        (≤ᵣMonotone+ᵣ _ _ _ _ y≤b (-ᵣ≤ᵣ _ _ a≤x))))



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
     (AsContinuousWithPred posℙ (λ _ → 1)
       (IsContinuousConst 1))
        (contDiagNE₂WP maxR posℙ
          (λ x _ → x)
          (λ x 0<x → fst (invℝ₊ (x , 0<x)))
          (AsContinuousWithPred posℙ (λ x → x)
            IsContinuousId)
          IsContinuousWithPred-invℝ₊)
              λ u 0<u →
                let u₊ : ℚ₊
                    u₊ = u , <ᵣ→<ℚ 0 u 0<u

                    inverse-path :
                      rat (fst (invℚ₊ u₊)) ≡
                      fst (invℝ₊ (rat u , 0<u))
                    inverse-path =
                      sym (invℝ'-rat u (snd u₊) 0<u) ∙
                      sym (cong fst (invℝ₊-impl (rat u , 0<u)))

                    max-path :
                      rat (ℚ.max u (fst (invℚ₊ u₊))) ≡
                      maxᵣ (rat u) (fst (invℝ₊ (rat u , 0<u)))
                    max-path =
                      sym (maxᵣ-rat u (fst (invℚ₊ u₊))) ∙
                      cong (maxᵣ (rat u)) inverse-path
                in subst (1 ≤ᵣ_) max-path
                  (≤ℚ→≤ᵣ 1 (ℚ.max u (fst (invℚ₊ u₊)))
                    (ℚ1≤x⊔1/x u₊)))


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
     (AsContinuousWithPred posℙ (λ _ → 1)
       (IsContinuousConst 1))
        (contDiagNE₂WP sumR posℙ
          (λ x _ → x)
          (λ x 0<x → fst (invℝ₊ (x , 0<x)))
          (AsContinuousWithPred posℙ (λ x → x)
            IsContinuousId)
          IsContinuousWithPred-invℝ₊)
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
     ／ᵣ₊ ℚ₊→ℝ₊ (ℚ.<→ℚ₊ y₀ y₁ y₀<y₁))
 slope-lower-bound z B 1<z y₀ y₁ y₀<y₁ (-B≤y₀ , y₀≤B) (-B≤y₁ , y₁≤B) =
   isTrans<≡ᵣ _ _ _
     (≤<ᵣ₊Monotone·ᵣ
       ((z ^ℚ (ℚ.- (fst B)))) (fst (z ^ℚ y₀))
       (((fst z -ᵣ 1) ／ᵣ₊ z) ,
         isTrans≡≤ᵣ _ _ _ (sym (Rℝ.0LeftAnnihilates _))
            (≤ᵣ-·ᵣo 0 _ _
             (<ᵣWeaken≤ᵣ _ _ (snd (invℝ₊ (fst z , z .snd))))
              (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ 1<z))))
               ((fst (z ^ℚ (fst h₊)) -ᵣ 1) ／ᵣ₊ ℚ₊→ℝ₊ h₊)

       (^ℚ-MonotoneR {x = z} (ℚ.- (fst B)) y₀ -B≤y₀
         (<ᵣWeaken≤ᵣ _ _ 1<z))

        (invEq (z/y'<x/y≃y₊·z<y'₊·x _ _ _ _)
           brn )
        )
       (·ᵣAssoc _ _ _
        ∙ cong (_·ᵣ
         fst (invℝ₊ (ℚ₊→ℝ₊ h₊)))
          (sym (factor-xᵃ-xᵇ z y₁ y₀) ))

  where
   h₊ : ℚ₊
   h₊ = ℚ.<→ℚ₊ y₀ y₁ y₀<y₁

   brn : fst (ℚ₊→ℝ₊ h₊) ·ᵣ (fst z -ᵣ 1)   <ᵣ
         fst z ·ᵣ (fst (z ^ℚ fst h₊) -ᵣ rat [ pos 1 / 1+ 0 ])

   brn = isTrans<≡ᵣ _ _ _ (a+c<b⇒a<b-c _ _ _ (isTrans≡<ᵣ _ _ _ (sym (·DistR+ (fst (ℚ₊→ℝ₊ h₊)) 1 _))
          (a+c<b⇒a<b-c _ _ 1
           (isTrans≡<ᵣ _ _ _
            (cong (λ t → t ·ᵣ (fst z -ᵣ 1) +ᵣ 1) (+ᵣ-rat (fst h₊) 1)
             ∙ +ᵣComm (rat (fst h₊ ℚ.+ [ pos 1 / 1+ 0 ]) ·ᵣ
       (fst z -ᵣ rat [ pos 1 / 1+ 0 ])) 1) (bernoulli's-ineq-^ℚ z (fst h₊ ℚ.+ 1)
             1<z (subst (1 ℚ.<_) (ℚ.+Comm 1 (fst h₊))
              (ℚ≤→<+₊ 1 1 h₊ (ℚ.isRefl≤ 1))) )))))
             (sym (+ᵣAssoc (fst (z ^ℚ (fst h₊ ℚ.+ 1))) _ _) ∙
              cong₂ _+ᵣ_
                (cong fst (sym (^ℚ-+ z (fst h₊) 1))
                  ∙ ·ᵣComm _ _ ∙
                    cong (_·ᵣ (z ^ℚ fst h₊) .fst) (cong fst (^ℚ-1 z) ))
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
     (Rℝ.·IdR'
       (fst (z ^ℚ (fst B ℚ.+ 1)) -ᵣ fst (z ^ℚ fst B))
       (fst (invℝ₊ (ℚ₊→ℝ₊ Bstep₊)))
       invBstep≡1 ∙
        factor-xᵃ-xᵇ z (fst B ℚ.+ 1) (fst B) ∙
          cong (λ u → fst (z ^ℚ fst B) ·ᵣ (fst u -ᵣ 1))
           (cong (z ^ℚ_) B+1-B≡1 ∙ ^ℚ-1 z))

 where
  h₊ = ℚ.<→ℚ₊ _ _ y₀<y₁
  B<B+1 = ℚ≤→<+₊ _ _ 1 (ℚ.isRefl≤ (fst B))
  Bstep₊ : ℚ₊
  Bstep₊ = ℚ.<→ℚ₊ (fst B) (fst B ℚ.+ 1) B<B+1
  B+1-B≡1 : (fst B ℚ.+ 1) ℚ.- fst B ≡ 1
  B+1-B≡1 = ℚ!
  Bstep-rat≡1 : fst Bstep₊ ≡ 1
  Bstep-rat≡1 = B+1-B≡1
  invBstep≡1 : fst (invℝ₊ (ℚ₊→ℝ₊ Bstep₊)) ≡ 1
  invBstep≡1 = cong (fst ∘ invℝ₊)
    (ℝ₊≡ (cong rat Bstep-rat≡1)) ∙ cong fst invℝ₊1

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
        (^ℚ-MonotoneR {x = (rat u , 0<u)} q q'
           q≤q'
        (≤ℚ→≤ᵣ _ _ 1≤u)))
   (λ u<1 → isTrans≤ᵣ _ _ _
     (min≤ᵣ' (fst ((rat u , 0<u) ^ℚ q))
            (fst ((rat u , 0<u) ^ℚ q'')))
       let xx = (^ℚ-MonotoneR {x = invℝ₊ (rat u , 0<u)}
               (ℚ.- q'') (ℚ.- q') (ℚ.minus-≤ q' q'' q'≤q'')
                   (isTrans≤≡ᵣ _ _ _
                    (invEq (z≤x/y₊≃y₊·z≤x 1 1 (rat u , 0<u))
                      (isTrans≡≤ᵣ _ _ _ (·IdR _)
                        (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ u<1))))
                    (·IdLᵣ _)))
       in subst2 _≤ᵣ_
            (cong fst (sym (^ℚ-minus (rat u , 0<u) q'')))
            (cong fst (sym (^ℚ-minus (rat u , 0<u) q')))
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
     (contDiagNE₂WP minR posℙ
       (curry (fst ∘ (_^ℚ q)))
       (curry (fst ∘ (_^ℚ q'')))
       (IsContinuous^ℚ q)
       (IsContinuous^ℚ q''))
     (IsContinuous^ℚ q')
     λ u 0<u → monotone^ℚ' q q' q'' q≤q' q'≤q'' u 0<u)
