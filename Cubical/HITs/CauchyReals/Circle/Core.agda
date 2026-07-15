module Cubical.HITs.CauchyReals.Circle.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Functions.Surjection


open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos ; ℤ)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad


open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ hiding (x+x≡2x)
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)


open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊ ; [_/_]₊)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi

open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  ( sin
  ; cos
  ; sin·sin+cos·cos=1
  ; sin·sin=1-cos·cos
  ; sin²+cos²=1
  ; cos0=1
  ; sin0=0
  ; cos-even
  )
open import Cubical.HITs.CauchyReals.Trigonometry.Identities
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds using (ointerval→abs<)
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Inverse using
  ( equivSin⟨⟩
  ; ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩
  )

open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.Relation.Binary.Base
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Circle.Base public
open import Cubical.HITs.CauchyReals.Circle.Angle.CaseSplit public using (distCircle→angle)

private
 pos-suc-minus-one : ∀ n → pos (suc n) ℤ.- pos 1 ≡ pos n
 pos-suc-minus-one zero = refl
 pos-suc-minus-one (suc n) = refl

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
     (ℚ.ℤ-→ℚ- (pos (suc n)) (pos 1)
      ∙ cong [_/ 1 ] (pos-suc-minus-one n)))))


circle-rel : ℝ → ℝ → Type
circle-rel x y = Σ[ k ∈ ℤ.ℤ ] x -ᵣ y ≡ rat [ k / 1 ]


sin-k-period : (a a' : ℝ) → circle-rel a a' →
  sin (a ·ᵣ (2 ·ᵣ π-number)) ≡ sin (a' ·ᵣ (2 ·ᵣ π-number))
sin-k-period a a' (pos n , p) = sin-k-period-pos a a' n p

sin-k-period a a' (ℤ.negsuc n , p) =
 sym (sin-k-period-pos a' a (suc n)
  (sym (-[x-y]≡y-x _ _) ∙∙ cong -ᵣ_ p
    ∙∙ (-ᵣ-rat _ ∙ cong rat (sym (ℚ.-[/] 1 (ℤ.negsuc n))))))

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
 ℤ.- n , (sym (-[x-y]≡y-x _ _) ∙∙ cong -ᵣ_ p
   ∙∙ (-ᵣ-rat _ ∙ cong rat (sym (ℚ.-[/] 1 n))))

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
    (sin·sin=1-cos·cos x
     ∙ cong (λ z → 1 -ᵣ z) (cong₂ _·ᵣ_ cosx=1 cosx=1 ∙ Rℝ.·IdR 1)
     ∙ +-ᵣ 1)


opaque
 scale-sym-ointervalℙ : ∀ a (K : ℝ₊) x
   → x ∈ ointervalℙ (-ᵣ a) a
   → x ·ᵣ fst K ∈  ointervalℙ (-ᵣ (a ·ᵣ fst K)) (a ·ᵣ fst K)
 scale-sym-ointervalℙ a K x (-a<x , x<a) =
   isTrans≡<ᵣ _ _ _ (sym (-ᵣ· _ _)) (<ᵣ-·ᵣo _ _ K -a<x)
    , <ᵣ-·ᵣo _ _ K x<a


⟨0,2π⟩→cos<1 : ∀ x → x ∈ ointervalℙ 0 (2 ·ᵣ π-number) → cos x <ᵣ 1
⟨0,2π⟩→cos<1 x (x<0 , x<2π) =
 let x/2 = ℚ₊→ℝ₊ ([ 1 / 2 ]₊) ₊·ᵣ (x , x<0)
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
                            (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ ([ 1 / 2 ]₊)) x<2π))
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
 ε = [ 1 / 4 ]₊


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
      ∙ sym (-[x-y]≡y-x _ _) ∙ cong -ᵣ_ p
      ∙ (-ᵣ-rat _ ∙ cong rat (sym (ℚ.-[/] 1 n))))
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
