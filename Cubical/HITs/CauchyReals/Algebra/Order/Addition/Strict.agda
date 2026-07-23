module Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using (𝕣-lim-self)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base


𝕣-lim-dist : ∀ x y ε →
  absᵣ (x (ε /2₊) +ᵣ (-ᵣ lim x y)) <ᵣ rat (fst ε)
𝕣-lim-dist x y ε =
  fst (∼≃abs<ε _ _ ε)
    (subst∼ ℚ!! (𝕣-lim-self x y (ε /2₊) (ε /2₊)))


opaque
 unfolding absᵣ _≤ᵣ_

 ≤absᵣ : ∀ x → x ≤ᵣ absᵣ x
 ≤absᵣ = ≡Continuous
   (λ x → maxᵣ x (absᵣ x))
   (λ x → absᵣ x)
   (cont₂maxᵣ _ _ IsContinuousId IsContinuousAbsᵣ)
   IsContinuousAbsᵣ
   λ x →
     cong (maxᵣ (rat x) ∘ rat) (sym (ℚ.abs'≡abs x))
     ∙∙ cong rat (ℚ.≤→max _ _ (≤abs x))
     ∙∙ cong rat (ℚ.abs'≡abs x)


from-abs< : ∀ x y z → absᵣ (x +ᵣ (-ᵣ y)) <ᵣ z
  → (x +ᵣ (-ᵣ y) <ᵣ z)
  × (y +ᵣ (-ᵣ x) <ᵣ z)
  × ((-ᵣ y) +ᵣ x <ᵣ z)
from-abs< x y z p =
  isTrans≤<ᵣ _ _ _ (≤absᵣ _) p
  , isTrans≤<ᵣ _ _ _ (≤absᵣ _)
      (subst (_<ᵣ z) (minusComm-absᵣ x y) p)
  , isTrans≤<ᵣ _ _ _ (≤absᵣ _)
      (subst (((_<ᵣ z) ∘ absᵣ)) (+ᵣComm x (-ᵣ y)) p)


opaque

 ∃rationalApprox≤ : ∀ u → (ε : ℚ₊) →
   ∃[ q ∈ ℚ ] (rat q +ᵣ (-ᵣ u) ≤ᵣ rat (fst ε)) × (u ≤ᵣ rat q)
 ∃rationalApprox≤ = Elimℝ-Prop.go w
  where
  w : Elimℝ-Prop λ u → (ε : ℚ₊) →
    ∃[ q ∈ ℚ ] (rat q +ᵣ (-ᵣ u) ≤ᵣ rat (fst ε)) × (u ≤ᵣ rat q)
  w .Elimℝ-Prop.ratA r ε =
    let zzz : (r ℚ.+ fst (ε /2₊)) ℚ.- r ℚ.≤ fst ε
        zzz = <≤ℚ!
    in ∣ r ℚ.+ fst (ε /2₊) ,
         isTrans≡≤ᵣ _ _ _ (-ᵣ-rat₂ _ _) (≤ℚ→≤ᵣ _ _ zzz)
         , ≤ℚ→≤ᵣ _ _ <≤ℚ! ∣₁
  w .Elimℝ-Prop.limA x y R ε =
    PT.map
      (λ (q , z , z') →
        let (_ , Xzz' , Xzz) =
              from-abs< _ _ _ (𝕣-lim-dist x y (ε /4₊))

            zz : -ᵣ (lim x y) +ᵣ x ((ε /4₊) /2₊)
              ≤ᵣ rat (fst (ε /4₊))
            zz = <ᵣWeaken≤ᵣ _ _ Xzz

            zz' : lim x y +ᵣ (-ᵣ x ((ε /4₊) /2₊))
              ≤ᵣ rat (fst (ε /4₊))
            zz' = <ᵣWeaken≤ᵣ _ _ Xzz'

            zzzzz : q ℚ.+ fst (ε /4₊)
              ℚ.≤ q ℚ.+ (fst (ε /2₊) ℚ.+ fst ((ε /4₊) /2₊))
            zzzzz = <≤ℚ!
        in q ℚ.+ fst (ε /2₊) ℚ.+ fst ((ε /4₊) /2₊) ,
          let zzz = ≤ᵣ-+o _ _
                (rat (fst (ε /2₊) ℚ.+ fst ((ε /4₊) /2₊)))
                (≤ᵣMonotone+ᵣ _ _ _ _ z zz)
          in subst2 _≤ᵣ_
               (cong (_+ᵣ rat (fst (ε /2₊) ℚ.+ fst ((ε /4₊) /2₊)))
                  (sym (+ᵣAssoc (rat q) _ _))
                ∙ +ᵣComm _ _
                ∙ +ᵣAssoc _ _ _
                ∙ cong₂ _+ᵣ_
                    (+ᵣComm _ _ ∙ +ᵣ-rat _ _ ∙ cong rat ℚ!!)
                    (cong₂ _+ᵣ_ refl (+ᵣComm _ _)
                      ∙ +ᵣAssoc _ _ _
                      ∙ cong₂ _+ᵣ_ (+ᵣComm _ _ ∙ +-ᵣ _) refl
                      ∙ +IdL _))
               (_∙_
                 {x = rat (fst ((ε /4₊) /2₊))
                    +ᵣ rat (fst (ε /4₊))
                    +ᵣ rat (fst (ε /2₊) ℚ.+ fst ((ε /4₊) /2₊))}
                 {y = rat
                    (fst ((ε /4₊) /2₊) ℚ.+ fst (ε /4₊)
                      ℚ.+ (fst (ε /2₊) ℚ.+ fst ((ε /4₊) /2₊)))}
                 ℚℝ!
                 (cong rat ℚ!!))
               zzz
          , isTrans≤ᵣ _ _ _
              (subst (_≤ᵣ (rat q +ᵣ rat (fst (ε /4₊))))
                (cong (x ((ε /4₊) /2₊) +ᵣ_) (+ᵣComm _ _)
                  ∙ +ᵣAssoc _ _ _
                  ∙ cong (_+ᵣ (lim x y)) (+-ᵣ _)
                  ∙ +IdL _)
                (≤ᵣMonotone+ᵣ _ _ _ _ z' zz'))
              (isTrans≡≤ᵣ _ _ _ (+ᵣ-rat _ _)
                (≤ℚ→≤ᵣ _ _
                  (subst (q ℚ.+ fst (ε /4₊) ℚ.≤_)
                    (ℚ.+Assoc q _ _) zzzzz))))
      (R ((ε /4₊) /2₊) ((ε /4₊) /2₊))
  w .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → squash₁


opaque

 ∃rationalApprox : ∀ u → (ε : ℚ₊) →
   ∃[ (q , q') ∈ (ℚ × ℚ) ]
     (q' ℚ.- q ℚ.< fst ε) × (rat q <ᵣ u) × (u <ᵣ rat q')
 ∃rationalApprox u ε =
   PT.map2
     (uncurry λ q (x , x') →
       uncurry λ q' (y , y') →
         (ℚ.- (q ℚ.+ fst (ε /4₊)) , q' ℚ.+ fst (ε /4₊)) ,
         let zz = ℚ.≤-+o (q ℚ.+ q') _
                    (fst (ε /4₊) ℚ.+ fst (ε /4₊))
                    (≤ᵣ→≤ℚ _ _
                      (subst2 _≤ᵣ_
                        (sym (+ᵣAssoc (rat q) _ _)
                          ∙ cong (rat q +ᵣ_)
                              (cong₂ _+ᵣ_ (-ᵣInvol u) (+ᵣComm _ _)
                                ∙ +ᵣAssoc u (-ᵣ u) _
                                ∙ cong (_+ᵣ rat q') (+-ᵣ u)
                                ∙ +IdL (rat q'))
                          ∙ +ᵣ-rat q q')
                        (+ᵣ-rat _ _)
                        (≤ᵣMonotone+ᵣ _ _ _ _ x y)))

             zzz : fst ((ε /4₊) /2₊) ℚ.+ fst ((ε /4₊) /2₊)
               ℚ.+ (fst (ε /4₊) ℚ.+ fst (ε /4₊)) ℚ.< fst ε
             zzz = <≤ℚ!
         in ℚ.isTrans≤< _ _ _ (subst (ℚ._≤ _) ℚ!! zz) zzz
            , (let zzz' : q ℚ.< q ℚ.+ fst (ε /4₊)
                   zzz' = <≤ℚ!
               in subst2 _<ᵣ_
                    (-ᵣ-rat (q ℚ.+ fst (ε /4₊)))
                    (-ᵣInvol u)
                    (-ᵣ<ᵣ _ _
                      (isTrans≤<ᵣ _ _ _ x' (<ℚ→<ᵣ _ _ zzz'))))
            , isTrans≤<ᵣ _ _ _ y' (<ℚ→<ᵣ _ _ <≤ℚ!))
     (∃rationalApprox≤ (-ᵣ u) ((ε /4₊) /2₊))
     (∃rationalApprox≤ u ((ε /4₊) /2₊))

 ∃rationalApprox< : ∀ u → (ε : ℚ₊) →
   ∃[ q ∈ ℚ ] (rat q +ᵣ (-ᵣ u) <ᵣ rat (fst ε)) × (u <ᵣ rat q)
 ∃rationalApprox< u ε =
   PT.map
     (uncurry λ q (x , x') →
       q ℚ.+ fst (ε /4₊) ,
       subst (_<ᵣ rat (fst ε))
         (sym (+ᵣAssoc (rat q) (-ᵣ u) _)
           ∙ cong (rat q +ᵣ_) (+ᵣComm (-ᵣ u) (rat (fst (ε /4₊))))
           ∙∙ +ᵣAssoc (rat q) (rat (fst (ε /4₊))) (-ᵣ u)
           ∙∙ ℚℝ!)
         (isTrans≤<ᵣ _ _ (rat (fst ε))
           (≤ᵣ-+o _ _ (rat (fst (ε /4₊))) x)
           (isTrans≡<ᵣ _ _ _ (+ᵣ-rat _ _)
             (<ℚ→<ᵣ (fst (ε /2₊) ℚ.+ fst (ε /4₊)) (fst ε) <≤ℚ!)))
       , isTrans≤<ᵣ _ _ _ x'
           (<ℚ→<ᵣ q (q ℚ.+ fst (ε /4₊)) <≤ℚ!))
     (∃rationalApprox≤ u (ε /2₊))


opaque

 <ᵣ-+o-pre : ∀ m n o → m ℚ.< n → rat m +ᵣ o <ᵣ rat n +ᵣ o
 <ᵣ-+o-pre m n o m<n =
  let Δ : ℚ₊
      Δ = ℚ.<→ℚ₊ m n m<n
  in PT.rec2 (isProp<ᵣ _ _)
    (λ (q , x , x') ((q' , q'') , y , y' , y'') →
      let x* : rat q ≤ᵣ rat (fst (Δ /4₊)) +ᵣ (rat m +ᵣ o)
          x* = subst (_≤ᵣ rat (fst (Δ /4₊)) +ᵣ (rat m +ᵣ o))
            (sym (+ᵣAssoc (rat q) _ _)
              ∙ cong (rat q +ᵣ_) (+ᵣComm _ _ ∙ +-ᵣ _)
              ∙ +IdR (rat q))
            (≤ᵣ-+o _ _ (rat m +ᵣ o) (<ᵣWeaken≤ᵣ _ _ x))

          y* : rat (fst (Δ /4₊)) +ᵣ (rat m +ᵣ o)
            ≤ᵣ -ᵣ (rat (fst (Δ /4₊)) +ᵣ (-ᵣ (rat n +ᵣ o)))
          y* = subst2
            {x = rat (fst (Δ /2₊))
              +ᵣ (rat m +ᵣ (o +ᵣ (-ᵣ rat (fst (Δ /4₊)))))}
            _≤ᵣ_
            ((λ i → +ᵣComm (rat (fst (Δ /2₊)))
                (+ᵣAssoc (rat m) o (-ᵣ rat (fst (Δ /4₊))) i) i)
              ∙ sym (+ᵣAssoc _ _ _)
              ∙ cong ((rat m +ᵣ o) +ᵣ_)
                  (+ᵣComm _ _ ∙ -ᵣ-rat₂ _ _ ∙ cong rat ℚ!!)
              ∙ +ᵣComm _ _)
            (+ᵣAssoc _ _ _
              ∙ cong (_+ᵣ (o +ᵣ (-ᵣ rat (fst (Δ /4₊)))))
                  (+ᵣ-rat (n ℚ.- m) _ ∙ cong rat ℚ!!)
              ∙ +ᵣAssoc _ _ _
              ∙ (λ i → +ᵣComm (-ᵣInvol (rat n +ᵣ o) (~ i))
                    (-ᵣ rat (fst (Δ /4₊))) i)
              ∙ sym (-ᵣDistr (rat (fst (Δ /4₊))) (-ᵣ (rat n +ᵣ o))))
            (≤ᵣ-+o _ _
              (rat m +ᵣ (o +ᵣ (-ᵣ rat (fst (Δ /4₊)))))
              (≤ℚ→≤ᵣ _ _ <≤ℚ![ m<n ]))

          z* : -ᵣ (rat (fst (Δ /4₊)) +ᵣ (-ᵣ (rat n +ᵣ o))) ≤ᵣ rat q'
          z* = subst
            ((-ᵣ (rat (fst (Δ /4₊)) +ᵣ (-ᵣ (rat n +ᵣ o)))) ≤ᵣ_)
            (cong (-ᵣ_)
              (sym (+ᵣAssoc (rat q'') (-ᵣ rat q') _)
                ∙ _∙_ {y = rat (q'' ℚ.+ (ℚ.- q' ℚ.+ ℚ.- q''))}
                    ℚℝ! (cong rat ℚ!! ∙ sym (-ᵣ-rat q')))
              ∙ -ᵣInvol (rat q'))
            (-ᵣ≤ᵣ _ _
              (≤ᵣMonotone+ᵣ _ _ _ _
                (isTrans≡≤ᵣ _ _ _ (-ᵣ-rat₂ _ _)
                  (≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ y)))
                (<ᵣWeaken≤ᵣ _ _ (-ᵣ<ᵣ _ _ y''))))

          z : rat q ≤ᵣ rat q'
          z = isTrans≤ᵣ _ _ _ (isTrans≤ᵣ _ _ _ x* y*) z*
      in isTrans<ᵣ _ _ _ x' (isTrans≤<ᵣ _ _ _ z y'))
    (∃rationalApprox< (rat m +ᵣ o) (Δ /4₊))
    (∃rationalApprox (rat n +ᵣ o) (Δ /4₊))


opaque
 unfolding _<ᵣ_

 <ᵣ-+o : ∀ m n o → m <ᵣ n → m +ᵣ o <ᵣ n +ᵣ o
 <ᵣ-+o m n o = PT.rec (isProp<ᵣ (m +ᵣ o) _)
   λ ((q , q') , x , x' , x'') →
    let y : m +ᵣ o ≤ᵣ rat q +ᵣ o
        y = ≤ᵣ-+o m (rat q) o x

        y'' : rat q' +ᵣ o ≤ᵣ n +ᵣ o
        y'' = ≤ᵣ-+o (rat q') n o x''

        y' : rat q +ᵣ o <ᵣ rat q' +ᵣ o
        y' = <ᵣ-+o-pre q q' o x'
    in isTrans<≤ᵣ _ _ _ (isTrans≤<ᵣ _ _ _ y y') y''


<ᵣ-o+ : ∀ m n o → m <ᵣ n → o +ᵣ m <ᵣ o +ᵣ n
<ᵣ-o+ m n o =
  subst2 _<ᵣ_ (+ᵣComm m o) (+ᵣComm n o) ∘ <ᵣ-+o m n o


a<b-c⇒c<b-a-bootstrap : ∀ a b c → a <ᵣ b -ᵣ c → c <ᵣ b -ᵣ a
a<b-c⇒c<b-a-bootstrap a b c p =
  subst2 _<ᵣ_
    (cong (a +ᵣ_) (+ᵣComm _ _)
      ∙∙ +ᵣAssoc _ _ _
      ∙ cong (_+ᵣ c) (+-ᵣ a)
      ∙∙ +IdL c)
    (sym (+ᵣAssoc _ _ _)
      ∙ cong (b +ᵣ_)
          (+ᵣAssoc _ _ _
            ∙∙ cong (_-ᵣ a) (+ᵣComm _ _ ∙ +-ᵣ c)
            ∙∙ +IdL _))
    (<ᵣ-+o _ _ (c -ᵣ a) p)


a<b-c⇒a+c<b-bootstrap : ∀ a b c → a <ᵣ b -ᵣ c → a +ᵣ c <ᵣ b
a<b-c⇒a+c<b-bootstrap a b c p =
  subst ((a +ᵣ c) <ᵣ_)
    (sym (+ᵣAssoc _ _ _)
      ∙∙ cong (b +ᵣ_) (+ᵣComm _ _ ∙ +-ᵣ c)
      ∙∙ +IdR b)
    (<ᵣ-+o _ _ c p)


a+c<b⇒a<b-c-bootstrap : ∀ a b c → a +ᵣ c <ᵣ b → a <ᵣ b -ᵣ c
a+c<b⇒a<b-c-bootstrap a b c p =
  subst (_<ᵣ b -ᵣ c)
    (sym (+ᵣAssoc _ _ _)
      ∙ cong (a +ᵣ_) (+-ᵣ c)
      ∙ +IdR a)
    (<ᵣ-+o _ _ (-ᵣ c) p)


a-b<c⇒a-c<b-bootstrap : ∀ a b c → a -ᵣ b <ᵣ c → a -ᵣ c <ᵣ b
a-b<c⇒a-c<b-bootstrap a b c p =
  subst2 _<ᵣ_
    (sym (+ᵣAssoc _ _ _)
      ∙ cong (a +ᵣ_)
          (+ᵣAssoc _ _ _
            ∙∙ cong (_+ᵣ (-ᵣ c)) (+ᵣComm _ _ ∙ +-ᵣ b)
            ∙∙ +IdL (-ᵣ c)))
    (cong (c +ᵣ_) (+ᵣComm _ _)
      ∙ +ᵣAssoc _ _ _
      ∙∙ cong (_+ᵣ b) (+-ᵣ c)
      ∙∙ +IdL b)
    (<ᵣ-+o _ _ (b -ᵣ c) p)


x<y→0<y-x-bootstrap : ∀ x y → x <ᵣ y → 0 <ᵣ y -ᵣ x
x<y→0<y-x-bootstrap x y p =
  subst (_<ᵣ y -ᵣ x) (+-ᵣ x) (<ᵣ-+o x y (-ᵣ x) p)


a-b<c⇒a<c+b-bootstrap : ∀ a b c → a -ᵣ b <ᵣ c → a <ᵣ c +ᵣ b
a-b<c⇒a<c+b-bootstrap a b c p =
  subst (_<ᵣ (c +ᵣ b))
    (sym (+ᵣAssoc _ _ _)
      ∙∙ cong (a +ᵣ_) (+ᵣComm _ _ ∙ +-ᵣ b)
      ∙∙ +IdR a)
    (<ᵣ-+o _ _ b p)
