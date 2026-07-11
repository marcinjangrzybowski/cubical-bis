module Cubical.HITs.CauchyReals.Circle.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path

import Cubical.Functions.Logic as L
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding


open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Power
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative
open import Cubical.HITs.CauchyReals.Integration
open import Cubical.HITs.CauchyReals.IntegrationMore
open import Cubical.HITs.CauchyReals.MeanValue
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Uniform
open import Cubical.HITs.CauchyReals.PiNumber
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Summation

open import Cubical.Algebra.Ring.BigOps


open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.CommRing.Base
import Cubical.Data.FinData as FD

open import Cubical.HITs.CauchyReals.TrigonometricIdentities
open import Cubical.HITs.CauchyReals.ArcSin
open import Cubical.HITs.CauchyReals.LiftingExpr

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Circle.Angle public
sin-k-period-pos : (a a' : ℝ) → ∀ n → a -ᵣ a' ≡ rat [ pos n / 1 ] →
 sin (a ·ᵣ (2 ·ᵣ π-number)) ≡ sin (a' ·ᵣ (2 ·ᵣ π-number))
sin-k-period-pos a a' zero p =
  cong (sin ∘ (_·ᵣ (2 ·ᵣ π-number)))
   (𝐑'.equalByDifference _ _ p)
sin-k-period-pos a a' (suc n) p =
  (cong sin (sym (𝐑'.minusPlus _ (2 ·ᵣ π-number))
   ∙ cong₂ _+ᵣ_ (cong₂ _-ᵣ_ refl (sym (Rℝ.·IdL _)) ∙
    sym (𝐑'.·DistL- _ _ _))  refl) ∙ sin-period _) ∙
   sin-k-period-pos (a -ᵣ 1) a' n (
    ((sym (+ᵣAssoc _ _ _) ∙∙
     cong (a +ᵣ_) (+ᵣComm _ _)
     ∙∙ +ᵣAssoc _ _ _) ∙∙ cong (_-ᵣ 1) p ∙∙
     (-ᵣ-rat₂ _ _ ∙ cong rat
     (ℚ.ℤ-→ℚ- (pos (suc n)) (pos 1)))))


circle-rel : ℝ → ℝ → Type
circle-rel x y = Σ[ k ∈ ℤ.ℤ ] x -ᵣ y ≡ rat [ k / 1 ]


sin-k-period : (a a' : ℝ) → circle-rel a a' →
  sin (a ·ᵣ (2 ·ᵣ π-number)) ≡ sin (a' ·ᵣ (2 ·ᵣ π-number))
sin-k-period a a' (pos n , p) = sin-k-period-pos a a' n p

sin-k-period a a' (ℤ.negsuc n , p) =
 sym (sin-k-period-pos a' a (suc n)
  (sym (-[x-y]≡y-x _ _) ∙∙ cong -ᵣ_ p
    ∙∙ -ᵣ-rat _))

cos-k-period : (a a' : ℝ) → circle-rel a a' →
  cos (a ·ᵣ (2 ·ᵣ π-number)) ≡ cos (a' ·ᵣ (2 ·ᵣ π-number))
cos-k-period a a' (k , p) =
  (sym (sin[x+π/2]=cos[x] _) ∙
    sym (cong sin (·DistR+ _ _ _ ∙
      cong₂ _+ᵣ_ refl (·ᵣAssoc _ _ _ ∙
       ·ᵣAssoc _ _ _ ∙ 𝐑'.·IdL' _ _
        (cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)) refl ∙ sym (rat·ᵣrat _ _)
         ∙ decℚ≡ᵣ?)))))
   ∙∙ sin-k-period (a +ᵣ rat [ 1 / 4 ]) (a' +ᵣ rat [ 1 / 4 ])
      (k , ℝ! ∙ p)
   ∙∙
    (cong sin (·DistR+ _ _ _ ∙
      cong₂ _+ᵣ_ refl (·ᵣAssoc _ _ _ ∙
       ·ᵣAssoc _ _ _ ∙ 𝐑'.·IdL' _ _
        (cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _)) refl ∙ sym (rat·ᵣrat _ _)
         ∙ decℚ≡ᵣ?))) ∙ sin[x+π/2]=cos[x] _)




isPropCircle-rel : ∀ a b → isProp (circle-rel a b)
isPropCircle-rel a b (k , p) (k' , p') =
  Σ≡Prop (λ _ → isSetℝ  _ _)
   (injFromNatℚ _ _ (inj-rat _ _ (sym p ∙ p')))


isSymCircleRel : BinaryRelation.isSym circle-rel
isSymCircleRel x y (n , p) =
 ℤ.- n , (sym (-[x-y]≡y-x _ _) ∙∙ cong -ᵣ_ p ∙∙ -ᵣ-rat _)

isEquivRelCircleRel : BinaryRelation.isEquivRel circle-rel
isEquivRelCircleRel .BinaryRelation.isEquivRel.reflexive x =
  0 , +-ᵣ _
isEquivRelCircleRel .BinaryRelation.isEquivRel.symmetric = isSymCircleRel
isEquivRelCircleRel .BinaryRelation.isEquivRel.transitive
  x y z (n , p) (n' , p') =
   (n ℤ.+ n') ,
     (sym ℝ!
      ∙∙ cong₂ _+ᵣ_ p p' ∙∙
      (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℤ+→ℚ+ n n')))

Circle : Type
Circle = ℝ / circle-rel

fromCircle≡ : (a b : ℝ) → [ a ]/ ≡ [ b ]/ → circle-rel a b
fromCircle≡ = SQ.effective isPropCircle-rel isEquivRelCircleRel

isSetCircle : isSet Circle
isSetCircle = squash/

injCircle : ℝ → Circle
injCircle = [_]/


sinFromCircle : Circle → ℝ
sinFromCircle = SQ.Rec.go w
 where
 w : Rec ℝ
 w .Rec.isSetB = isSetℝ
 w .Rec.f a = sin (a ·ᵣ (2 ·ᵣ π-number))
 w .Rec.f∼ = sin-k-period

cosFromCircle : Circle → ℝ
cosFromCircle = SQ.Rec.go w
 where
 w : Rec ℝ
 w .Rec.isSetB = isSetℝ
 w .Rec.f a = cos (a ·ᵣ (2 ·ᵣ π-number))
 w .Rec.f∼ = cos-k-period


module _ (ε : ℝ₊) where
 circle-rel-overlap :
   (x y : (Σ[ x ∈ ℝ ] x ∈ ointervalℙ 0 (1 +ᵣ fst ε))) → Type
 circle-rel-overlap (x , _) (y , _) = circle-rel x y

 CircleOverlap[_] : Type
 CircleOverlap[_] =
  (Σ[ x ∈ ℝ ] x ∈ ointervalℙ 0 (1 +ᵣ fst ε))
   / circle-rel-overlap


 CircleOverlap[_]→Circle : CircleOverlap[_] → Circle
 CircleOverlap[_]→Circle = SQ.Rec.go w
  where
  w : Rec _
  w .Rec.isSetB = isSetCircle
  w .Rec.f (a , _) = [ a ]/
  w .Rec.f∼ _ _ = eq/ _ _


Intervalℝ : Type
Intervalℝ = Σ ℝ (_∈ (intervalℙ 0 1))



Circle→distCircle : Circle → distCircle
Circle→distCircle x = (cosFromCircle x , sinFromCircle x) ,
 SQ.ElimProp.go w x
 where
 w : ElimProp λ x → cosFromCircle x ·ᵣ cosFromCircle x +ᵣ
                     sinFromCircle x ·ᵣ sinFromCircle x ≡ rat [ pos 1 / 1 ]
 w .ElimProp.isPropB _ = isSetℝ _ _
 w .ElimProp.f x = +ᵣComm _ _ ∙ sin·sin+cos·cos=1 (x ·ᵣ (2 ·ᵣ π-number))




Circle→[cos,sin]-surj : isSurjection Circle→distCircle
Circle→[cos,sin]-surj ((x , y) , x²+y²≡1) =
  PT.map (λ (φ , _ , cosφ≡x , sinφ≡y ) →
    injCircle (φ ／ᵣ₊ (2 ₊·ᵣ π-number₊)) ,
      Σ≡Prop (λ _ → isSetℝ _ _)
      (cong₂ _,_
       (cong cos ([x/₊y]·yᵣ _ _) ∙ cosφ≡x)
       (cong sin ([x/₊y]·yᵣ _ _) ∙ sinφ≡y)))
    (distCircle→angle 1 x y (cong₂ _+ᵣ_ (x^²=x·x _) (x^²=x·x _) ∙ x²+y²≡1))



cosx≡1→sinx≡0 : ∀ x → cos x ≡ 1 → sin x ≡ 0
cosx≡1→sinx≡0 x cosx=1 =
  x²≡0→x≡0 (sin x)
    (((cong₂ _·ᵣ_ (sym (Rℝ.·IdL _)) refl
     ∙ sym (𝐑'.+IdR' _ _
      (𝐑'.+InvR' _ _ (cong (_^ⁿ 2) cosx=1 ∙ 1^ⁿ 2))))
      ∙ +ᵣAssoc _ _ _) ∙ cong (_-ᵣ 1) (sin²+cos²=1 x) ∙ +-ᵣ 1)


opaque
 scale-sym-ointervalℙ : ∀ a (K : ℝ₊) x
   → x ∈ ointervalℙ (-ᵣ a) a
   → x ·ᵣ fst K ∈  ointervalℙ (-ᵣ (a ·ᵣ fst K)) (a ·ᵣ fst K)
 scale-sym-ointervalℙ a K x (-a<x , x<a) =
   isTrans≡<ᵣ _ _ _ (sym (-ᵣ· _ _)) (<ᵣ-·ᵣo _ _ K -a<x)
    , <ᵣ-·ᵣo _ _ K x<a


⟨0,2π⟩→cos<1 : ∀ x → x ∈ ointervalℙ 0 (2 ·ᵣ π-number) → cos x <ᵣ 1
⟨0,2π⟩→cos<1 x (x<0 , x<2π) =
 let x/2 = ℚ₊→ℝ₊ ([ 1 / 2 ] , _ ) ₊·ᵣ (_ , x<0)
 in isTrans≡<ᵣ _ _ _
    (cong cos (sym (𝐑'.·IdL' _ _ (sym (rat·ᵣrat _ _) ∙ decℚ≡ᵣ?))
      ∙ sym (·ᵣAssoc _ _ _))
      ∙ cos[2φ]=2cos²[φ]-1 (rat [ 1 / 2 ] ·ᵣ x))
        (a<c+b⇒a-c<b _ _ _
         (isTrans<≡ᵣ _ _ _
           (<ᵣ-o·ᵣ _ _ 2
            (isTrans≡<ᵣ _ _ _
              (abs[x^²ⁿ] 1 _ ∙ absᵣ^ⁿ _ 2)
              (^<1 (absᵣ _) (0≤absᵣ _) 1
               (isTrans≡<ᵣ _ _ _
                 (cong absᵣ (cos[x]=-sin[x-π/2] _) ∙ sym (-absᵣ _))
                 ((ointerval→abs< _ _
                      (map-fst (isTrans≡<ᵣ _ _ _ (-ᵣ-rat 1)) (
                    ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _
                     (isTrans≡<ᵣ _ _ _ (sym (+IdL _))
                       (<ᵣ-+o _ _ _ (snd $ x/2) )
                       ,
                          isTrans<≡ᵣ _ _ _
                          (<ᵣ-+o _ _ (-ᵣ π-number/2)
                            (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ ([ 1 / 2 ] , _ )) x<2π))
                            (cong₂ _-ᵣ_
                              (((·ᵣAssoc _ _ _) ∙
                              𝐑'.·IdL' _ _ (sym (rat·ᵣrat  _ _) ∙
                                decℚ≡ᵣ?))
                               ∙ sym (x+x≡2x _)) refl
                             ∙ 𝐑'.plusMinus π-number/2 π-number/2)
                       )))

                       ))))))
           (sym (x+x≡2x 1))))


cos=1⇒ : ∀ x → cos (x ·ᵣ (2 ·ᵣ π-number)) ≡ 1 → circle-rel x 0
cos=1⇒ x p = PT.rec
  (isPropCircle-rel _ _)
  (λ (q , x<q , q<x+ε) →
    let ((z , q-z) , z+[q-z]=q , 0≤q-z , q-z<1) = ℚ.floor-frac q

        pp = sym (cos-k-period x _ (z , ℝ!))
        x≡z : x  ≡ rat [ z / 1+ 0 ]
        x≡z = ⊎.rec
            (λ ε≤q-z →
               ⊥.rec (≤ᵣ→≯ᵣ 1 (cos (x ·ᵣ (2 ·ᵣ π-number)))
                           (≡ᵣWeaken≤ᵣ _ _ (sym p))
                            (isTrans≡<ᵣ _ _ _ (sym pp)
                              (⟨0,2π⟩→cos<1
                               ((x -ᵣ rat [ z / 1 ]) ·ᵣ (2 ·ᵣ π-number) )
                               ((isTrans<≡ᵣ _ _ _
                                 (fst (z/y<x₊≃z<y₊·x _ _ (2 ₊·ᵣ π-number₊))
                                (isTrans≡<ᵣ _ _ _
                                 (𝐑'.0LeftAnnihilates _)
                                 (x<y→0<y-x _ _
                                   (<-+o-cancel _ _ _ (isTrans≡<ᵣ _ _ _
                                  (+ᵣ-rat [ z / 1 ] q-z ∙ cong rat z+[q-z]=q)
                                  (isTrans<≤ᵣ _ _ _
                                   q<x+ε (≤ᵣ-o+ _ _ _
                                      (≤ℚ→≤ᵣ _ q-z ε≤q-z))))))))
                                (·ᵣComm _ _))
                               ,
                               isTrans<≡ᵣ _ _ _
                                (<ᵣ-·ᵣo _ _ (2 ₊·ᵣ π-number₊)
                                  (isTrans≤<ᵣ _ _ _
                                    (a≤c+b⇒a-c≤b _ _ _
                                     (isTrans≤≡ᵣ _ _ _ (<ᵣWeaken≤ᵣ _ _ x<q)
                                      (cong rat (sym z+[q-z]=q) ∙
                                       sym (+ᵣ-rat _ _))))
                                    (<ℚ→<ᵣ q-z 1 q-z<1)))
                                 (Rℝ.·IdL _ ))))))
            (λ q-z<ε →
               let x-z∈ = subst (λ X → (x -ᵣ rat [ z / 1+ 0 ])
                        ·ᵣ (rat [ pos 2 / 1+ 0 ] ·ᵣ π-number)
                          ∈ ointervalℙ (-ᵣ X) X)
                          (·ᵣAssoc _ _ _ ∙∙ ·ᵣAssoc _ _ _ ∙∙
                            𝐑'.·IdL' _ _  (cong₂ _·ᵣ_ (sym (rat·ᵣrat _ _))
                               refl  ∙
                              sym (rat·ᵣrat _ _) ∙
                               decℚ≡ᵣ?))
                          (scale-sym-ointervalℙ (rat [ 1 / 4 ]) (2 ₊·ᵣ π-number₊)
                         (x -ᵣ rat [ z / 1+ 0 ])
                          (isTrans<≤ᵣ _ _ _
                            (a+c<b⇒a<b-c _ _ _ (isTrans≡<ᵣ _ _ _ (+ᵣComm _ _)
                              (a<c+b⇒a-b<c _ _ _ q<x+ε)))
                              (≤ᵣ-o+ _ _ _
                                (-ᵣ≤ᵣ _ _ (isTrans≡≤ᵣ _ _ _
                                  (sym (+IdR _))
                                  (isTrans≤≡ᵣ _ _ _
                                  (≤ᵣ-o+ _ _
                                  (rat [ z / 1 ])
                                   (≤ℚ→≤ᵣ 0 q-z 0≤q-z))
                                   (+ᵣ-rat _ _ ∙ cong rat z+[q-z]=q)))))
                                   , isTrans<ᵣ _ _ _
                            (isTrans<≡ᵣ _ _ _ (<ᵣ-+o _ _ (-ᵣ rat [ z / 1+ 0 ])
                             (isTrans<≡ᵣ _ _ _ x<q (cong rat (sym z+[q-z]=q)
                               ∙ sym (+ᵣ-rat [ z / 1 ] q-z) ∙ +ᵣComm _ _)))
                            (𝐑'.plusMinus _ _)) (<ℚ→<ᵣ q-z _ q-z<ε)))
                   uu = fst (invEquiv
                        (congEquiv
                          {x = (x -ᵣ rat [ z / 1+ 0 ]) ·ᵣ (2 ·ᵣ π-number) ,
                          x-z∈}
                          {y = 0 , isTrans<≡ᵣ _ _ _
                             (-ᵣ<ᵣ _ _ 0<π-number/2) (-ᵣ-rat 0) , 0<π-number/2}
                           equivSin⟨⟩))
                          (Σ≡Prop (∈-isProp (ointervalℙ -1 1))
                            (cosx≡1→sinx≡0 _
                             (sym (cos-k-period x _
                              (z , ℝ!)) ∙ p) ∙ sym sin0=0))
               in 𝐑'.equalByDifference _ _
                   ( ((x·y≡z→x≡z/₊y _ _ (2 ₊·ᵣ π-number₊) (cong fst uu))) ∙
                     𝐑'.0LeftAnnihilates _))

                (ℚ.Dichotomyℚ (fst ε) q-z)

    in z , (𝐑'.+IdR' _ _ (-ᵣ-rat 0)) ∙ x≡z)
  (denseℚinℝ x (x +ᵣ rat (fst ε))
    (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
      (<ᵣ-o+ _ _ x (snd (ℚ₊→ℝ₊ ε)))))

 where
 ε : ℚ₊
 ε = [ 1 / 4 ] , _


cDist : Circle → Circle → ℝ
cDist = SQ.Rec2.go w
 where

 zzz :  (x a a' : ℝ) →
      circle-rel a a' →
         cos ((x -ᵣ a) ·ᵣ 2 ·ᵣ π-number)
       ≡ cos ((x -ᵣ a') ·ᵣ 2 ·ᵣ π-number)
 zzz x a a' (n , p) =
     cong cos (sym (·ᵣAssoc _ _ _))
   ∙∙ cos-k-period _ _ (ℤ.- n ,
     ℝ!
      ∙ sym (-[x-y]≡y-x _ _) ∙ cong -ᵣ_ p ∙ -ᵣ-rat _)
  ∙∙ cong cos (·ᵣAssoc _ _ _)

 w : Rec2 ℝ
 w .Rec2.isSetB = isSetℝ
 w .Rec2.f x y = 1 -ᵣ cos ((x -ᵣ y) ·ᵣ 2 ·ᵣ π-number)
 w .Rec2.f∼ x a a' r =
    cong₂ _-ᵣ_ refl (zzz x a a' r)
 w .Rec2.∼f a a' x r =
    cong₂ _-ᵣ_ refl (
          sym (cong cos
        (sym (·ᵣAssoc _ _ _)
         ∙∙ cong₂ _·ᵣ_ (sym (-[x-y]≡y-x _ _)) refl ∙ -ᵣ· _ _
         ∙∙ cong -ᵣ_ (·ᵣAssoc _ _ _))
           ∙ sym (cos-even _))
       ∙∙ zzz x a a' r
       ∙∙ (cong cos
        (sym (·ᵣAssoc _ _ _)
         ∙∙ cong₂ _·ᵣ_ (sym (-[x-y]≡y-x _ _)) refl ∙ -ᵣ· _ _
         ∙∙ cong -ᵣ_ (·ᵣAssoc _ _ _))
           ∙ sym (cos-even _)))
