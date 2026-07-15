module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Injectivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

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

module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; fromSucℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Limit

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR

open import Cubical.Algebra.Group.DirProd
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction

open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.StrictMonotonicity

opaque
  invLipPreLn : ∀ Z → ∃[ K ∈ ℚ₊ ]
                InverseLipschitz-ℝ→ℝℙ K
                 ((intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
                (fromNat (suc (suc Z)))))
                λ x (≤x , x≤) →
                  expPreDer.expPreDer'.preLn Z
                    (x , isTrans<≤ᵣ 0
                      (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
                      (<ℚ→<ᵣ [ pos 0 / 1 ]
                        [ pos 1 / fromNat (suc (suc Z)) ]
                        (0<pos 0 (fromNat (suc (suc Z))))) ≤x)
                   x≤ ≤x
  invLipPreLn Z =
     PT.map
       ww
       (denseℚinℝ _ _ (snd Kᵣ))

    where


     Z<SZ : fst (fromSucℚ₊ (suc Z)) ℚ.<
         fst (fromSucℚ₊ (suc (suc Z)))
     Z<SZ =
                  (<ℤ→<ℚ (pos (suc (suc Z))) (pos (suc (suc (suc Z))))
                  (ℤ.ℕ<→pos-<-pos _ _
                    (ℕ.≤-refl {(suc (suc (suc Z)))})))
     1<Z : [ pos 1 / 1+ 0 ] ℚ.< [ pos (suc (suc Z)) / 1+ 0 ]
     1<Z =
                  (<ℤ→<ℚ (pos (suc zero)) (pos (suc (suc Z)))
                  (ℤ.ℕ<→pos-<-pos _ _
                    (ℕ.suc-≤-suc (ℕ.suc-≤-suc ℕ.zero-≤))))

     [1/3+Z]≤[2+Z] : rat [ pos 1 / 2+ suc Z ] ≤ᵣ rat [ pos (suc (suc Z)) / 1+ 0 ]
     [1/3+Z]≤[2+Z] = isTrans≤ᵣ _ 1 _
       (≤ℚ→≤ᵣ _ _ (ℚ.invℚ₊≤invℚ₊ (fromSucℚ₊ (suc (suc Z))) 1
         ((ℚ.<Weaken≤ _ _
          (ℚ.isTrans< 1 (fst (fromSucℚ₊ (suc Z))) _ 1<Z (Z<SZ))))
         ))
       (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ 1<Z))

     2+Z∈ : (fromNat (suc (suc Z))) ∈
              ((intervalℙ (rat [ 1 / fromNat (suc (suc (suc Z))) ])
                 (fromNat (suc (suc (suc Z))))))
     2+Z∈ = [1/3+Z]≤[2+Z] , (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ Z<SZ))


     3+Z∈ : rat ([ (pos (suc (suc (suc Z)))) / 1 ]) ∈
              ((intervalℙ (rat [ 1 / fromNat (suc (suc (suc Z))) ])
                 (fromNat (suc (suc (suc Z))))))
     3+Z∈ =
               (≤ℚ→≤ᵣ _ _
                  (ℚ.isTrans≤ _ 1 [ pos (suc (suc (suc Z))) / (1+ 0) ]
                    (ℚ.invℚ₊≤invℚ₊ (fromSucℚ₊ (suc (suc Z))) 1
                     ((≤ℤ→≤ℚ _ (pos _) (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                  (ℕ.suc-≤-suc ℕ.zero-≤)))))
                    ((≤ℤ→≤ℚ _ (pos (suc (suc (suc Z)))) (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
                  (ℕ.suc-≤-suc ℕ.zero-≤)))))) , (≤ᵣ-refl _)



     SSSZℚ₊ SSZℚ₊ : ℚ₊
     SSSZℚ₊ = [ (pos (suc (suc (suc Z)))) / 1 ] , 0<pos (suc (suc Z)) 1
     SSZℚ₊ = [ (pos (suc (suc Z))) / 1 ] , 0<pos (suc Z) 1

     SSSZ₊ SSZ₊ : ℝ₊
     SSSZ₊ = ℚ₊→ℝ₊ SSSZℚ₊
     SSZ₊ = ℚ₊→ℝ₊ SSZℚ₊

     Kᵣ : ℝ₊
     Kᵣ =
           BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
            +ᵣ -ᵣ

            BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈)
            ,
            x<y→0<y-x
             (BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈))
             (BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈)
           (fst 3+Z∈))
             (monotoneStrictPreLn (suc Z)
               SSZ₊
               SSSZ₊
               (<ℚ→<ᵣ _ _ 1<Z)
               (snd 2+Z∈) (fst 2+Z∈)
               (snd 3+Z∈) (fst 3+Z∈)
               (<ℚ→<ᵣ _ _ Z<SZ))

     ww : Σ ℚ (λ q → (rat [ pos 0 / 1+ 0 ] <ᵣ rat q) × (rat q <ᵣ Kᵣ .fst)) →
           Σ ℚ₊
           (λ K →
              InverseLipschitz-ℝ→ℝℙ K
              (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
               (fromNat (suc (suc Z))))
              λ x (≤x , x≤) → expPreDer.expPreDer'.preLn Z
                    (x , isTrans<≤ᵣ 0
                      (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
                      (<ℚ→<ᵣ [ pos 0 / 1 ]
                        [ pos 1 / fromNat (suc (suc Z)) ]
                        (0<pos 0 (fromNat (suc (suc Z))))) ≤x)
                   x≤ ≤x)
     ww (K , 0<K , K<Kᵣ) = (invℚ₊ K₊) , zzz

      where
      K₊ : ℚ₊
      K₊ = (K , <ᵣ→<ℚ _ _ 0<K)
      zzz : InverseLipschitz-ℝ→ℝℙ (invℚ₊ K₊)
        (intervalℙ (rat [ 1 / fromNat (suc (suc Z)) ])
         (fromNat (suc (suc Z))))
        (λ x (≤x , x≤) → expPreDer.expPreDer'.preLn Z
          (x , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z))))) ≤x)
          x≤ ≤x)
      zzz u u∈ v v∈ ε lnU∼lnV =
        invEq (∼≃abs<ε u v (invℚ₊ K₊ ·₊ ε)) abs-bound-rat
       where
        u₊ v₊ : ℝ₊
        u₊ =
          u ,
          isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst u∈)
        v₊ =
          v ,
          isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst v∈)

        lnU lnV : ℝ
        lnU = expPreDer.expPreDer'.preLn Z
          (u , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst u∈))
          (snd u∈) (fst u∈)
        lnV = expPreDer.expPreDer'.preLn Z
          (v , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc Z)) ]
              (0<pos 0 (fromNat (suc (suc Z)))))
            (fst v∈))
          (snd v∈) (fst v∈)




        clp : ℝ → ℝ
        clp = clampᵣ (rat [ 1 / (1+  (suc Z)) ])
                     (rat [ pos (suc (suc Z)) / 1 ])

        1/SSZ<SSZ : fst (invℚ₊ SSZℚ₊) ℚ.< fst SSZℚ₊
        1/SSZ<SSZ =
          ℚ.isTrans< _ 1 _
            (fst (ℚ.invℚ₊-<-invℚ₊ 1 SSZℚ₊) 1<Z)
            1<Z


        1/SSZ≤SSZ : rat (fst (invℚ₊ SSZℚ₊)) ≤ᵣ rat (fst SSZℚ₊)
        1/SSZ≤SSZ = ≤ℚ→≤ᵣ _ _ (ℚ.<Weaken≤ _ _ 1/SSZ<SSZ)

        0<clp : ∀ x → 0 <ᵣ clp x
        0<clp x = isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ (0<pos _ _))
           (≤clampᵣ (rat [ 1 / (1+  (suc Z)) ]) _ x 1/SSZ≤SSZ)

        clpCount : IsContinuous clp
        clpCount = IsContinuousClamp
           (rat [ 1 / (1+  (suc Z)) ])
                     (rat [ pos (suc (suc Z)) / 1 ])

        lnX' : ℝ → ℝ
        lnX' x = ln (clp x , 0<clp x)

        lnX'ₙ : ∀ (x : ℝ₊) 0<x
                (x∈ : fst x ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                          (rat [ pos (suc (suc (suc Z))) / 1 ]))) →
                  ln x ≡ BDL.preLn
                           (fst x , 0<x) (suc Z) (snd x∈) (fst x∈)
        lnX'ₙ x 0<x x∈ =
          cong snd (Seq-^-FI.∩$-∈ₙ (fst x) (snd x) (suc Z) x∈)
          ∙ Seq-^-fun-snd≡BDL-with (fst x) (suc Z) x∈ 0<x

        clp≡ : ∀ u → u ∈ ((intervalℙ (rat [ 1 /  (1+ (suc Z)) ])
                 (rat [ pos (suc (suc Z)) / 1 ]))) → clp u ≡ u
        clp≡ u u∈ = sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)

        lnX'Cont : IsContinuous lnX'
        lnX'Cont = IsContinuousWithPred∘IsContinuous
         pred0< (curry ln) clp 0<clp
         ln-cont clpCount

        lnuv< : absᵣ (lnU -ᵣ lnV) <ᵣ rat (fst ε)
        lnuv< = fst (∼≃abs<ε lnU lnV ε) lnU∼lnV

        zzzz= : ∀ x y → clp (rat x) ≡ clp (rat y) →
         fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
         absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
        zzzz= x y p =
         ≡ᵣWeaken≤ᵣ
                   (fst Kᵣ ·ᵣ
                     absᵣ (clp (rat x) -ᵣ clp (rat y)))
                   (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
                   (Rℝ.0RightAnnihilates'
                     (fst Kᵣ)
                     (absᵣ (clp (rat x) -ᵣ clp (rat y)))
                     (cong absᵣ
                       (Rℝ.+InvR'
                         (clp (rat x)) (clp (rat y)) p)
                     ∙ absᵣ-rat 0)
                     ∙ sym (absᵣ-rat 0) ∙
                     cong absᵣ (sym (Rℝ.+InvR'
                       (lnX' (rat x)) (lnX' (rat y))
                       (ll))))

           where

           ll : ln (clp (rat x) , 0<clp (rat x))  ≡ ln (clp (rat y) , 0<clp (rat y))
           ll = cong ln
             (ℝ₊≡
               {x = (clp (rat x) , 0<clp (rat x))}
               {y = (clp (rat y) , 0<clp (rat y))} p)

        zzzz< : ∀ x y → clp (rat x) <ᵣ clp (rat y) →
         fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
         absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
        zzzz< x y x<y =
         isTrans≡≤ᵣ
           (fst Kᵣ ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)))
           (absᵣ (clp (rat x) -ᵣ clp (rat y)) ·ᵣ fst Kᵣ)
           (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
          (·ᵣComm
            (fst Kᵣ) (absᵣ (clp (rat x) -ᵣ clp (rat y))))
          (fst (z≤x/y₊≃y₊·z≤x
            (absᵣ (lnX' (rat x) -ᵣ lnX' (rat y)))
            (fst Kᵣ) abs-diff₊)
            (subst2 _≤ᵣ_
              fixed-slope-path log-slope-path zzWW))
           where

           hhA : pos (suc (suc Z)) ℤ.+negsuc Z ≡ pos 1
           hhA = sym (ℤStdP.pos- (suc (suc Z)) (suc Z)) ∙ hhNat Z
            where
            hhNat : ∀ Z → (suc (suc Z) ℤStd.ℕ- suc Z) ≡ pos 1
            hhNat zero = refl
            hhNat (suc Z) = hhNat Z

           hhhh : 1 ℤ.+ ℤ.predℤ (pos (suc (suc Z)) ℤ.+negsuc Z) ≡ pos 1
           hhhh = cong (1 ℤ.+_) (cong ℤ.predℤ hhA) ∙ refl

           SSZ≤SSSZ : [ pos (suc (suc Z)) / 1 ] ℚ.≤ [ pos (suc (suc (suc Z))) / 1 ]
           SSZ≤SSSZ = (ℚ.<Weaken≤ [ pos (suc (suc Z)) / 1 ] [ pos (suc (suc (suc Z))) / 1 ] Z<SZ)

           1/SSSZ≤1/SSZ : rat [ pos 1 / 2+ suc Z ] ≤ᵣ rat [ pos 1 / 2+ Z ]
           1/SSSZ≤1/SSZ = ≤ℚ→≤ᵣ _ _
            (ℚ.invℚ≤invℚ SSSZℚ₊ SSZℚ₊ SSZ≤SSSZ)

           x*∈ : clp (rat x) ∈  (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                          (rat [ pos (suc (suc (suc Z))) / 1 ]))
           x*∈ =
            let (≤x , x≤) = ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat x)))
            in isTrans≤ᵣ _ _ _ 1/SSSZ≤1/SSZ ≤x , isTrans≤ᵣ _ _ _ x≤
              (≤ℚ→≤ᵣ _ _ SSZ≤SSSZ)

           y*∈ : clp (rat y) ∈ (intervalℙ (rat [ 1 /  (2+ (suc Z)) ])
                          (rat [ pos (suc (suc (suc Z))) / 1 ]))
           y*∈ =
            let (≤y , y≤) = ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat y)))
            in (isTrans≤ᵣ _ _ _ 1/SSSZ≤1/SSZ ≤y) ,
                 isTrans≤ᵣ _ _ _ y≤ ((≤ℚ→≤ᵣ _ _ SSZ≤SSSZ))



           zzWW :
             ((BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
               -ᵣ BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈))
               ／ᵣ₊ (fst SSSZ₊ -ᵣ fst SSZ₊ ,
                 x<y→0<y-x (fst SSZ₊) (fst SSSZ₊) (<ℚ→<ᵣ _ _ Z<SZ)))
             ≤ᵣ
             ((BDL.preLn (clp (rat y) , 0<clp (rat y)) (suc Z) (snd y*∈) (fst y*∈)
               -ᵣ BDL.preLn (clp (rat x) , 0<clp (rat x)) (suc Z) (snd x*∈) (fst x*∈))
               ／ᵣ₊ (clp (rat y) -ᵣ clp (rat x) ,
                 x<y→0<y-x (clp (rat x)) (clp (rat y)) x<y))
           zzWW =
            (expPreDer.slope-monotone-preLn
               (suc Z) (clp (rat x) , 0<clp (rat x)) (clp (rat y) , 0<clp (rat y))
                SSZ₊ SSSZ₊
                (snd x*∈) (fst x*∈)
                (snd y*∈) (fst y*∈)
                (snd 2+Z∈) (fst 2+Z∈)
                (snd 3+Z∈) (fst 3+Z∈)
                x<y (<ℚ→<ᵣ _ _ Z<SZ) (snd ((clampᵣ∈ℚintervalℙ _ _ 1/SSZ≤SSZ (rat x)))) (snd y*∈))

           positive-diff :
             0 <ᵣ clp (rat y) -ᵣ clp (rat x)
           positive-diff = x<y→0<y-x
             (clp (rat x)) (clp (rat y)) x<y

           abs-diff-positive :
             0 <ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y))
           abs-diff-positive = isTrans<≤ᵣ
             0 (clp (rat y) -ᵣ clp (rat x))
             (absᵣ (clp (rat x) -ᵣ clp (rat y)))
             positive-diff
             (isTrans≤≡ᵣ
               (clp (rat y) -ᵣ clp (rat x))
               (absᵣ (clp (rat y) -ᵣ clp (rat x)))
               (absᵣ (clp (rat x) -ᵣ clp (rat y)))
               (≤absᵣ (clp (rat y) -ᵣ clp (rat x)))
               (minusComm-absᵣ (clp (rat y)) (clp (rat x))))

           abs-diff₊ : ℝ₊
           abs-diff₊ =
             absᵣ (clp (rat x) -ᵣ clp (rat y)) , abs-diff-positive

           fixed-slope-path :
             ((BDL.preLn SSSZ₊ (suc Z) (snd 3+Z∈) (fst 3+Z∈)
               -ᵣ BDL.preLn SSZ₊ (suc Z) (snd 2+Z∈) (fst 2+Z∈))
               ／ᵣ₊ (fst SSSZ₊ -ᵣ fst SSZ₊ ,
                 x<y→0<y-x (fst SSZ₊) (fst SSSZ₊)
                   (<ℚ→<ᵣ _ _ Z<SZ)))
             ≡ fst Kᵣ
           fixed-slope-path =
             cong₂ _·ᵣ_ refl
               (cong (fst ∘ invℝ₊)
                 (ℝ₊≡ {_ , _} {_ , isTrans<≡ᵣ _ _ _ decℚ<ᵣ?
                   (sym (cong (rat ∘ [_/ 1 ]) hhhh))}
                   (-ᵣ-rat₂
                     [ pos (suc (suc (suc Z))) / 1 ]
                     [ pos (suc (suc Z)) / 1 ]
                   ∙ cong rat (ℚ.ℤ-→ℚ-
                     (pos (suc (suc (suc Z))))
                     (pos (suc (suc Z)))
                   ∙ cong ([_/ 1 ])
                     (cong
                       (λ t → t ℤ.+ ℤ.- (pos (suc (suc Z))))
                       (ℤ.pos+ 1 (suc (suc Z)))
                     ∙ sym (ℤ.+Assoc (pos 1) (pos (suc (suc Z)))
                         (ℤ.- (pos (suc (suc Z)))))
                     ∙ 𝐙'.+IdR' (pos 1)
                         (pos (suc (suc Z)) ℤ.+
                           ℤ.- (pos (suc (suc Z))))
                         (ℤ.-Cancel (pos (suc (suc Z))))
                     ∙ sym hhhh))))
               ∙ cong (fst ∘ invℝ₊)
                   (ℝ₊≡ (cong rat (cong [_/ 1 ] hhhh)))
               ∙ cong fst invℝ₊1)
             ∙ ·IdR _

           log-slope-path :
             ((BDL.preLn (clp (rat y) , 0<clp (rat y))
                 (suc Z) (snd y*∈) (fst y*∈)
               -ᵣ BDL.preLn (clp (rat x) , 0<clp (rat x))
                 (suc Z) (snd x*∈) (fst x*∈))
               ／ᵣ₊ (clp (rat y) -ᵣ clp (rat x) , positive-diff))
             ≡ absᵣ (lnX' (rat x) -ᵣ lnX' (rat y))
                 ·ᵣ fst (invℝ₊ abs-diff₊)
           log-slope-path =
             cong₂ _·ᵣ_
               (sym (absᵣNonNeg
                 (BDL.preLn (clp (rat y) , 0<clp (rat y))
                    (suc Z) (snd y*∈) (fst y*∈)
                  -ᵣ BDL.preLn (clp (rat x) , 0<clp (rat x))
                    (suc Z) (snd x*∈) (fst x*∈))
                 (x≤y→0≤y-x _ _
                   (expPreDer.monotonePreLn (suc Z)
                     (clp (rat x) , 0<clp (rat x))
                     (clp (rat y) , 0<clp (rat y))
                     (snd x*∈) (fst x*∈) (snd y*∈) (fst y*∈)
                     (<ᵣWeaken≤ᵣ _ _ x<y))))
               ∙ cong absᵣ
                   (cong₂ (λ u v → u +ᵣ -ᵣ v)
                     (sym (lnX'ₙ
                       (clp (rat y) , 0<clp (rat y))
                       (0<clp (rat y)) y*∈))
                     (sym (lnX'ₙ
                       (clp (rat x) , 0<clp (rat x))
                       (0<clp (rat x)) x*∈)))
               ∙ minusComm-absᵣ (lnX' (rat y)) (lnX' (rat x)))
               (cong (fst ∘ invℝ₊)
                 (ℝ₊≡
                   {x = (clp (rat y) -ᵣ clp (rat x) , positive-diff)}
                   {y = abs-diff₊}
                   (sym (absᵣPos
                     (clp (rat y) -ᵣ clp (rat x)) positive-diff)
                   ∙ minusComm-absᵣ (clp (rat y)) (clp (rat x)))))

        opaque
         unfolding _+ᵣ_
         zzzz* : fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v) ≤ᵣ absᵣ (lnX' u -ᵣ lnX' v)
         zzzz* =
           ≤Cont₂
              {λ u v → fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v)}
              {λ u v → absᵣ (lnX' u -ᵣ lnX' v)}
              (cont∘₂ (IsContinuous∘ _ _
                 (IsContinuous·ᵣL (fst Kᵣ))
                 IsContinuousAbsᵣ)
                (cont₂∘  (contNE₂ sumR)
                  clpCount
                  (IsContinuous∘ _ _
                    IsContinuous-ᵣ clpCount)) )
              (cont∘₂ IsContinuousAbsᵣ
                (cont₂∘  (contNE₂ sumR)
                  lnX'Cont
                  (IsContinuous∘ _ _
                    IsContinuous-ᵣ lnX'Cont)
                  ))
              (ℚ.elimBy≡⊎<'
                 (λ x y X →
                   subst2 (_≤ᵣ_ ∘ (fst Kᵣ ·ᵣ_))
                     ((minusComm-absᵣ (clp (rat x)) (clp (rat y))))
                     (minusComm-absᵣ (lnX' (rat x)) (lnX' (rat y)))
                     X)
                 (λ x → ≡ᵣWeaken≤ᵣ _ _
                      (Rℝ.0RightAnnihilates' _ _ (cong absᵣ (+-ᵣ _)
                        ∙ absᵣ-rat 0)
                       ∙∙ sym (absᵣ-rat 0)
                       ∙∙ cong absᵣ ((sym (+-ᵣ (lnX' (rat x)))))))
                 λ x h₊ →
                   let
                     y = x ℚ.+ fst h₊
                     x<y = ℚ≤→<+₊ x x h₊ (ℚ.isRefl≤ x)
                   in
                    ⊎.rec
                     (zzzz= x y)
                     (zzzz< x y)
                     (ℚ-clamp-<-casesᵣ ([ 1 /  (1+ (suc Z)) ])
                            ([ pos (suc (suc Z)) / 1 ])
                            x y 1/SSZ<SSZ x<y))
              u v

        lnX'-u≡ln-u₊ : lnX' u ≡ ln u₊
        lnX'-u≡ln-u₊ =
          cong ln
            (ℝ₊≡
              {x = (clp u , 0<clp u)} {y = u₊}
              (sym (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)))

        ln-u₊≡seq-u : ln u₊ ≡ Seq⊆→.fun Seq-^ u Z u∈ .snd
        ln-u₊≡seq-u =
          cong snd (Seq-^-FI.∩$-∈ₙ u (snd u₊) Z u∈)

        seq-u≡preLn-u₊ :
          Seq⊆→.fun Seq-^ u Z u∈ .snd ≡
            expPreDer.expPreDer'.preLn Z
              (u , isTrans<≤ᵣ 0
                (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
                (<ℚ→<ᵣ [ pos 0 / 1 ]
                  [ pos 1 / fromNat (suc (suc Z)) ]
                  (0<pos 0 (fromNat (suc (suc Z)))))
                (fst u∈))
              (snd u∈) (fst u∈)
        seq-u≡preLn-u₊ =
          Seq-^-fun-snd≡preLn-with u Z u∈
            (isTrans<≤ᵣ 0
              (rat [ pos 1 / fromNat (suc (suc Z)) ]) u
              (<ℚ→<ᵣ [ pos 0 / 1 ]
                [ pos 1 / fromNat (suc (suc Z)) ]
                (0<pos 0 (fromNat (suc (suc Z)))))
              (fst u∈))

        lnX'-u≡lnU : lnX' u ≡ lnU
        lnX'-u≡lnU =
          lnX'-u≡ln-u₊ ∙ ln-u₊≡seq-u ∙ seq-u≡preLn-u₊

        lnX'-v≡ln-v₊ : lnX' v ≡ ln v₊
        lnX'-v≡ln-v₊ =
          cong ln
            (ℝ₊≡
              {x = (clp v , 0<clp v)} {y = v₊}
              (sym (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈)))

        ln-v₊≡seq-v : ln v₊ ≡ Seq⊆→.fun Seq-^ v Z v∈ .snd
        ln-v₊≡seq-v =
          cong snd (Seq-^-FI.∩$-∈ₙ v (snd v₊) Z v∈)

        seq-v≡preLn-v₊ :
          Seq⊆→.fun Seq-^ v Z v∈ .snd ≡
            expPreDer.expPreDer'.preLn Z
              (v , isTrans<≤ᵣ 0
                (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
                (<ℚ→<ᵣ [ pos 0 / 1 ]
                  [ pos 1 / fromNat (suc (suc Z)) ]
                  (0<pos 0 (fromNat (suc (suc Z)))))
                (fst v∈))
              (snd v∈) (fst v∈)
        seq-v≡preLn-v₊ =
          Seq-^-fun-snd≡preLn-with v Z v∈
            (isTrans<≤ᵣ 0
              (rat [ pos 1 / fromNat (suc (suc Z)) ]) v
              (<ℚ→<ᵣ [ pos 0 / 1 ]
                [ pos 1 / fromNat (suc (suc Z)) ]
                (0<pos 0 (fromNat (suc (suc Z)))))
              (fst v∈))

        lnX'-v≡lnV : lnX' v ≡ lnV
        lnX'-v≡lnV =
          lnX'-v≡ln-v₊ ∙ ln-v₊≡seq-v ∙ seq-v≡preLn-v₊

        weighted-clamp-path :
          fst Kᵣ ·ᵣ absᵣ (u -ᵣ v) ≡
            fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v)
        weighted-clamp-path = cong₂
          (λ u' v' → fst Kᵣ ·ᵣ absᵣ (u' -ᵣ v'))
          (∈ℚintervalℙ→clampᵣ≡ _ _ u u∈)
          (∈ℚintervalℙ→clampᵣ≡ _ _ v v∈)

        log-abs-path :
          absᵣ (lnX' u -ᵣ lnX' v) ≡ absᵣ (lnU -ᵣ lnV)
        log-abs-path = cong absᵣ
          (cong₂ _-ᵣ_ lnX'-u≡lnU lnX'-v≡lnV)

        zzzz : absᵣ (u -ᵣ v) ≤ᵣ
               invℝ₊ Kᵣ .fst ·ᵣ absᵣ (lnU -ᵣ lnV)
        zzzz =
          let weighted-bound :
                fst Kᵣ ·ᵣ absᵣ (u -ᵣ v) ≤ᵣ absᵣ (lnU -ᵣ lnV)
              weighted-bound = isTrans≤≡ᵣ
                (fst Kᵣ ·ᵣ absᵣ (u -ᵣ v))
                (absᵣ (lnX' u -ᵣ lnX' v))
                (absᵣ (lnU -ᵣ lnV))
                (isTrans≡≤ᵣ
                  (fst Kᵣ ·ᵣ absᵣ (u -ᵣ v))
                  (fst Kᵣ ·ᵣ absᵣ (clp u -ᵣ clp v))
                  (absᵣ (lnX' u -ᵣ lnX' v))
                  weighted-clamp-path zzzz*)
                log-abs-path
              quotient-bound :
                absᵣ (u -ᵣ v) ≤ᵣ
                  absᵣ (lnU -ᵣ lnV) ·ᵣ fst (invℝ₊ Kᵣ)
              quotient-bound = invEq
                (z≤x/y₊≃y₊·z≤x
                  (absᵣ (lnU -ᵣ lnV)) (absᵣ (u -ᵣ v)) Kᵣ)
                weighted-bound
          in isTrans≤≡ᵣ
            (absᵣ (u -ᵣ v))
            (absᵣ (lnU -ᵣ lnV) ·ᵣ fst (invℝ₊ Kᵣ))
            (fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV))
            quotient-bound
            (·ᵣComm (absᵣ (lnU -ᵣ lnV)) (fst (invℝ₊ Kᵣ)))

        invKᵣ<invK :
          fst (invℝ₊ Kᵣ) <ᵣ fst (invℝ₊ (ℚ₊→ℝ₊ K₊))
        invKᵣ<invK =
          invEq (invℝ₊-<-invℝ₊ Kᵣ (ℚ₊→ℝ₊ K₊)) K<Kᵣ

        product-bound :
          fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV) <ᵣ
            fst (invℝ₊ (ℚ₊→ℝ₊ K₊)) ·ᵣ rat (fst ε)
        product-bound =
          <ᵣ₊Monotone·ᵣ
            (fst (invℝ₊ Kᵣ))
            (fst (invℝ₊ (ℚ₊→ℝ₊ K₊)))
            (absᵣ (lnU -ᵣ lnV))
            (rat (fst ε))
            (<ᵣWeaken≤ᵣ 0 (fst (invℝ₊ Kᵣ)) (snd (invℝ₊ Kᵣ)))
            (0≤absᵣ (lnU -ᵣ lnV))
            invKᵣ<invK lnuv<

        product-rat-bound :
          fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV) <ᵣ
            rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε)
        product-rat-bound =
          isTrans<≡ᵣ
            (fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV))
            (fst (invℝ₊ (ℚ₊→ℝ₊ K₊)) ·ᵣ rat (fst ε))
            (rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε))
            product-bound
            (cong₂ _·ᵣ_ (invℝ₊-rat K₊) refl)

        abs-bound-product :
          absᵣ (u -ᵣ v) <ᵣ
            rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε)
        abs-bound-product =
          isTrans≤<ᵣ
            (absᵣ (u -ᵣ v))
            (fst (invℝ₊ Kᵣ) ·ᵣ absᵣ (lnU -ᵣ lnV))
            (rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε))
            zzzz product-rat-bound

        abs-bound-rat :
          absᵣ (u -ᵣ v) <ᵣ rat (fst (invℚ₊ K₊ ·₊ ε))
        abs-bound-rat =
          isTrans<≡ᵣ
            (absᵣ (u -ᵣ v))
            (rat (fst (invℚ₊ K₊)) ·ᵣ rat (fst ε))
            (rat (fst (invℚ₊ K₊ ·₊ ε)))
            abs-bound-product
            (sym (rat·ᵣrat (fst (invℚ₊ K₊)) (fst ε)))

inj-ln : ∀ x y → ln x ≡ ln y → x ≡ y
inj-ln (x , 0<x) (y , 0<y) =
  Seq-^-FI.∩$-elimProp2 x 0<x y 0<y
   {λ (_ , ln-x) (_ , ln-y) → ln-x ≡ ln-y → (x , 0<x) ≡ (y , 0<y) }
   (λ _ _ → isPropΠ λ _ → isSetℝ₊ _ _)
   λ Z x∈ y∈ p →
     let
       seq-x-path :
         Seq⊆→.fun Seq-^ x Z x∈ .snd ≡
           expPreDer.expPreDer'.preLn Z
             (x , isTrans<≤ᵣ 0
               (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
               (<ℚ→<ᵣ [ pos 0 / 1 ]
                 [ pos 1 / fromNat (suc (suc Z)) ]
                 (0<pos 0 (fromNat (suc (suc Z)))))
               (fst x∈))
             (snd x∈) (fst x∈)
       seq-x-path =
         Seq-^-fun-snd≡preLn-with x Z x∈
           (isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst x∈))

       seq-y-path :
         Seq⊆→.fun Seq-^ y Z y∈ .snd ≡
           expPreDer.expPreDer'.preLn Z
             (y , isTrans<≤ᵣ 0
               (rat [ pos 1 / fromNat (suc (suc Z)) ]) y
               (<ℚ→<ᵣ [ pos 0 / 1 ]
                 [ pos 1 / fromNat (suc (suc Z)) ]
                 (0<pos 0 (fromNat (suc (suc Z)))))
               (fst y∈))
             (snd y∈) (fst y∈)
       seq-y-path =
         Seq-^-fun-snd≡preLn-with y Z y∈
           (isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) y
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst y∈))

       preLn-path :
         expPreDer.expPreDer'.preLn Z
           (x , isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) x
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst x∈))
           (snd x∈) (fst x∈)
         ≡ expPreDer.expPreDer'.preLn Z
           (y , isTrans<≤ᵣ 0
             (rat [ pos 1 / fromNat (suc (suc Z)) ]) y
             (<ℚ→<ᵣ [ pos 0 / 1 ]
               [ pos 1 / fromNat (suc (suc Z)) ]
               (0<pos 0 (fromNat (suc (suc Z)))))
             (fst y∈))
           (snd y∈) (fst y∈)
       preLn-path = sym seq-x-path ∙ p ∙ seq-y-path
     in PT.rec (isSetℝ₊ _ _)
       (λ (K , isLip) →
         ℝ₊≡
           (InverseLipschitz-ℝ→ℝℙ→injective K
             (Seq⊆.𝕡 seq-^-intervals Z)
             (λ z (≤z , z≤) → expPreDer.expPreDer'.preLn Z
               (z , isTrans<≤ᵣ 0
                 (rat [ pos 1 / fromNat (suc (suc Z)) ]) z
                 (<ℚ→<ᵣ [ pos 0 / 1 ]
                   [ pos 1 / fromNat (suc (suc Z)) ]
                   (0<pos 0 (fromNat (suc (suc Z)))))
                 ≤z)
               z≤ ≤z)
             isLip x x∈ y y∈ preLn-path))
       (invLipPreLn Z)
