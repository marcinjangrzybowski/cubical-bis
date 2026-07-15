module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Delta where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (seqΣ ; seqΣ' ; _^ⁿ_ ; _ℚ₊^ⁿ_)
open import Cubical.Data.Rationals.Inverse as ℚ using
  ( invℚ
  ; _⁻¹₊
  ; x/y<z→x<y·z
  )

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0< ; _ℚ₊·_)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Algebra.Expression.Lifting

open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Convexity
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Inequalities

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.CommRing.Properties as CR

private
 opaque
  powered-growth-base-path : ∀ Z (ε : ℚ₊) n →
    fst
      (ℚ₊→ℝ₊
        (((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1)
          ℚ₊^ⁿ (suc (suc n)))
        ^ℚ fst (stepℚ₊ n))
      ≡ rat (fst ε)
          ·ᵣ fst (ℚ₊→ℝ₊ (((fromSucℚ₊ Z) ℚ₊· 2) ⁻¹₊))
          +ᵣ 1
  powered-growth-base-path Z ε n =
    power-coercion
    ∙ exponent-composition
    ∙ exponent-cancellation
    ∙ exponent-one
    ∙ expose-addition
    ∙ expose-multiplication
   where
   count : ℕ
   count = suc (suc n)

   denominator : ℚ₊
   denominator = (fromSucℚ₊ Z) ℚ₊· 2

   increment : ℚ₊
   increment = ε ℚ₊· invℚ₊ denominator

   base : ℚ₊
   base = increment +₊ 1

   real-base : ℝ₊
   real-base = ℚ₊→ℝ₊ base

   powered-base : ℝ₊
   powered-base = ℚ₊→ℝ₊ (base ℚ₊^ⁿ count)

   exponent : ℚ
   exponent = fst (stepℚ₊ n)

   power-coercion :
     fst (powered-base ^ℚ exponent) ≡
     fst ((real-base ^ℚ fromNat count) ^ℚ exponent)
   power-coercion =
     cong (fst ∘ _^ℚ exponent)
       (ℝ₊≡ (sym (^ⁿ-ℚ^ⁿ count (fst base))))

   exponent-composition :
     fst ((real-base ^ℚ fromNat count) ^ℚ exponent) ≡
     fst (real-base ^ℚ (fromNat count ℚ.· exponent))
   exponent-composition =
     cong fst (^ℚ-· real-base (fromNat count) exponent)

   exponent-cancellation :
     fst (real-base ^ℚ (fromNat count ℚ.· exponent)) ≡
     fst (real-base ^ℚ 1)
   exponent-cancellation =
     cong (fst ∘ real-base ^ℚ_)
       (ℚ.x·invℚ₊[x] (fromNat count))

   exponent-one : fst (real-base ^ℚ 1) ≡ fst real-base
   exponent-one = cong fst (^ℚ-1 real-base)

   expose-addition :
     fst real-base ≡
     rat (fst ε ℚ.· fst (invℚ₊ denominator)) +ᵣ 1
   expose-addition =
     sym (+ᵣ-rat (fst ε ℚ.· fst (invℚ₊ denominator)) 1)

   expose-multiplication :
     rat (fst ε ℚ.· fst (invℚ₊ denominator)) +ᵣ 1 ≡
     rat (fst ε) ·ᵣ fst (ℚ₊→ℝ₊ (denominator ⁻¹₊)) +ᵣ 1
   expose-multiplication =
     cong (_+ᵣ 1)
       (rat·ᵣrat (fst ε) (fst (invℚ₊ denominator)))

  growth-root-bound : ∀ Z (ε : ℚ₊) n →
    fromNat (suc (suc Z)) ℚ.<
      ((fst (ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) ℚ.+ 1)
        ℚ^ⁿ suc (suc n)) →
    fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1 <ᵣ
      rat (fst ε) ·ᵣ
        fst (invℝ₊ (ℚ₊→ℝ₊ ((fromSucℚ₊ Z) ℚ₊· 2)))
  growth-root-bound Z ε n growth =
    isTrans<≡ᵣ
      (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1)
      (rat (fst ε) ·ᵣ
        fst (ℚ₊→ℝ₊ (((fromSucℚ₊ Z) ℚ₊· 2) ⁻¹₊)))
      (rat (fst ε) ·ᵣ
        fst (invℝ₊ (ℚ₊→ℝ₊ ((fromSucℚ₊ Z) ℚ₊· 2))))
      (a<c+b⇒a-b<c
        (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)))
        1
        (rat (fst ε) ·ᵣ
          fst (ℚ₊→ℝ₊ (((fromSucℚ₊ Z) ℚ₊· 2) ⁻¹₊)))
        (isTrans<≡ᵣ
          (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)))
          (fst
            (ℚ₊→ℝ₊
              (((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1)
                ℚ₊^ⁿ suc (suc n))
              ^ℚ fst (stepℚ₊ n)))
          (rat (fst ε) ·ᵣ
            fst (ℚ₊→ℝ₊ (((fromSucℚ₊ Z) ℚ₊· 2) ⁻¹₊)) +ᵣ 1)
          (^ℚ-StrictMonotone
            {fromNat (suc (suc Z))}
            {ℚ₊→ℝ₊
              (((ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) +₊ 1)
                ℚ₊^ⁿ suc (suc n))}
            (stepℚ₊ n)
            (<ℚ→<ᵣ
              (fromNat (suc (suc Z)))
              ((fst (ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2)) ℚ.+ 1)
                ℚ^ⁿ suc (suc n))
              growth))
          (powered-growth-base-path Z ε n)))
      (cong (rat (fst ε) ·ᵣ_)
        (sym (invℝ₊-rat ((fromSucℚ₊ Z) ℚ₊· 2))))

  rational-scaled-growth-bound : ∀ Z (ε : ℚ₊) n →
    fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1 <ᵣ
      rat (fst ε) ·ᵣ
        fst (invℝ₊ (ℚ₊→ℝ₊ ((fromSucℚ₊ Z) ℚ₊· 2))) →
    rat
        (([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ]) ℚ.· 2)
      ·ᵣ (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1)
      <ᵣ rat (fst ε)
  rational-scaled-growth-bound Z ε n root-bound =
    isTrans≡<ᵣ
      (rat
          (([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ]) ℚ.· 2)
        ·ᵣ root-difference)
      (fst (ℚ₊→ℝ₊ denominator) ·ᵣ root-difference)
      (rat (fst ε))
      coefficient-path
      (fst
        (z<x/y₊≃y₊·z<x
          (rat (fst ε)) root-difference (ℚ₊→ℝ₊ denominator))
        root-bound)
   where
   denominator : ℚ₊
   denominator = (fromSucℚ₊ Z) ℚ₊· 2

   root-difference : ℝ
   root-difference =
     fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1

   coefficient-path :
     rat
         (([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ]) ℚ.· 2)
       ·ᵣ root-difference ≡
     fst (ℚ₊→ℝ₊ denominator) ·ᵣ root-difference
   coefficient-path =
     cong (_·ᵣ root-difference)
       (cong rat
         (cong {y = fromNat (suc Z)} (ℚ._· 2)
           (ℚ.ℤ-→ℚ- (pos (suc (suc Z))) (pos 1)
           ∙ cong [_/ 1 ]
               (sym (ℤ.pos- (suc (suc Z)) 1)))))

  sequence-gap-path : ∀ z n →
    lnSeq z n -ᵣ lnSeq' z n ≡
      ((fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1)
        -ᵣ (1 -ᵣ fst (invℝ₊ (z ^ℚ fst (stepℚ₊ n)))))
      ·ᵣ fromNat (suc (suc n))
  sequence-gap-path z n =
    cong
      (λ inverse-root →
        lnSeq z n
          -ᵣ (1 -ᵣ inverse-root) ·ᵣ fromNat (suc (suc n)))
      (cong fst (^ℚ-minus' z (fst (stepℚ₊ n)))
      ∙ cong fst (invℝ₊^ℚ z (fst (stepℚ₊ n))))
    ∙ sym
        (Rℝ.·DistL-
          (fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1)
          (1 -ᵣ fst (invℝ₊ (z ^ℚ fst (stepℚ₊ n))))
          (fromNat (suc (suc n))))

  sequence-gap-quadratic-bound : ∀ z n → 1 ≤ᵣ fst z →
    lnSeq z n -ᵣ lnSeq' z n ≤ᵣ
      (2 ·ᵣ (fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1)) ·ᵣ lnSeq z n
  sequence-gap-quadratic-bound z n 1≤z =
    isTrans≡≤ᵣ
      (lnSeq z n -ᵣ lnSeq' z n)
      (root-gap ·ᵣ scale)
      ((2 ·ᵣ root-difference) ·ᵣ lnSeq z n)
      (sequence-gap-path z n)
      (isTrans≤≡ᵣ
        (root-gap ·ᵣ scale)
        (((2 ·ᵣ root-difference) ·ᵣ root-difference) ·ᵣ scale)
        ((2 ·ᵣ root-difference) ·ᵣ lnSeq z n)
        (≤ᵣ-·ᵣo
          root-gap
          ((2 ·ᵣ root-difference) ·ᵣ root-difference)
          scale
          scale-nonnegative
          (x+1/x-bound positive-root half≤root))
        (sym (·ᵣAssoc (2 ·ᵣ root-difference) root-difference scale)))
   where
   positive-root : ℝ₊
   positive-root = z ^ℚ fst (stepℚ₊ n)

   root-difference : ℝ
   root-difference = fst positive-root -ᵣ 1

   root-gap : ℝ
   root-gap = root-difference -ᵣ (1 -ᵣ fst (invℝ₊ positive-root))

   scale : ℝ
   scale = fromNat (suc (suc n))

   scale-nonnegative : 0 ≤ᵣ scale
   scale-nonnegative =
     ≤ℚ→≤ᵣ
       0 [ pos (suc (suc n)) / 1 ]
       (ℚ.0≤pos (suc (suc n)) 1)

   half≤root : rat [ pos 1 / 2 ] ≤ᵣ fst positive-root
   half≤root =
     isTrans≤ᵣ
       (rat [ pos 1 / 2 ]) 1 (fst positive-root)
       (decℚ≤ᵣ? {[ pos 1 / 2 ]} {1})
       (1≤^ℚ z (stepℚ₊ n) 1≤z)

  sequence-product-upper-bound : ∀ z Z n →
    1 ≤ᵣ fst z → fst z ≤ᵣ fromNat (suc (suc Z)) →
    (2 ·ᵣ (fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1)) ·ᵣ lnSeq z n
      ≤ᵣ
    (2 ·ᵣ
      (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1))
      ·ᵣ (fromNat (suc (suc Z)) -ᵣ 1)
  sequence-product-upper-bound z Z n 1≤z z≤upper =
    ≤ᵣ₊Monotone·ᵣ
      (2 ·ᵣ root-difference)
      (2 ·ᵣ upper-root-difference)
      (lnSeq z n)
      (fromNat (suc (suc Z)) -ᵣ 1)
      upper-factor-nonnegative
      (lnSeq-nonnegative z 1≤z n)
      root-factor-monotone
      sequence-upper-bound
   where
   root-difference : ℝ
   root-difference = fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1

   upper-root-difference : ℝ
   upper-root-difference =
     fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1

   one≤upper : 1 ≤ᵣ fromNat (suc (suc Z))
   one≤upper =
     isTrans≤ᵣ 1 (fst z) (fromNat (suc (suc Z))) 1≤z z≤upper

   upper-root-difference-nonnegative : 0 ≤ᵣ upper-root-difference
   upper-root-difference-nonnegative =
     x≤y→0≤y-x
       1
       (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)))
       (1≤^ℚ (fromNat (suc (suc Z))) (stepℚ₊ n) one≤upper)

   upper-factor-nonnegative : 0 ≤ᵣ 2 ·ᵣ upper-root-difference
   upper-factor-nonnegative =
     isTrans≡≤ᵣ
       0 (2 ·ᵣ 0) (2 ·ᵣ upper-root-difference)
       (sym (Rℝ.0RightAnnihilates 2))
       (≤ᵣ-o·ᵣ
         0 upper-root-difference 2
         (decℚ≤ᵣ? {0} {2})
         upper-root-difference-nonnegative)

   root-factor-monotone :
     2 ·ᵣ root-difference ≤ᵣ 2 ·ᵣ upper-root-difference
   root-factor-monotone =
     ≤ᵣ-o·ᵣ
       root-difference upper-root-difference 2
       (decℚ≤ᵣ? {0} {2})
       (≤ᵣ-+o
         (fst (z ^ℚ fst (stepℚ₊ n)))
         (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)))
         (-ᵣ 1)
         (^ℚ-Monotone
           {z} {fromNat (suc (suc Z))}
           (stepℚ₊ n) z≤upper))

   sequence-upper-bound :
     lnSeq z n ≤ᵣ fromNat (suc (suc Z)) -ᵣ 1
   sequence-upper-bound =
     isTrans≤ᵣ
       (lnSeq z n)
       (fst z -ᵣ 1)
       (fromNat (suc (suc Z)) -ᵣ 1)
       (lnSeq≤ z n)
       (≤ᵣ-+o
         (fst z) (fromNat (suc (suc Z))) (-ᵣ 1) z≤upper)

  upper-product-coefficient-path : ∀ Z n →
    (2 ·ᵣ
      (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1))
      ·ᵣ (fromNat (suc (suc Z)) -ᵣ 1)
      ≡
    rat (([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ]) ℚ.· 2)
      ·ᵣ (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1)
  upper-product-coefficient-path Z n =
    ·ᵣComm
      (2 ·ᵣ upper-root-difference)
      (fromNat (suc (suc Z)) -ᵣ 1)
    ∙ ·ᵣAssoc
        (fromNat (suc (suc Z)) -ᵣ 1)
        2 upper-root-difference
    ∙ cong (_·ᵣ upper-root-difference)
        (cong (_·ᵣ 2)
          (-ᵣ-rat₂
            [ pos (suc (suc Z)) / 1 ] [ pos 1 / 1 ])
        ∙ sym
            (rat·ᵣrat
              ([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ])
              2))
   where
   upper-root-difference : ℝ
   upper-root-difference =
     fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1

opaque
 unfolding -ᵣ_ _+ᵣ_

 seqΔ-pos : ∀ z Z → (z<Z : fst z ≤ᵣ fromNat (suc (suc Z))) →
    1 ≤ᵣ fst z → ∀ (ε : ℚ₊) →
    (∀ n → (fst (seqΔ-δ Z ε)) ℕ.< n →
       lnSeq z n -ᵣ lnSeq' z n <ᵣ (rat (fst ε)))

 seqΔ-pos z Z z≤Z 1≤z ε =
  let (N , growth) = x^→∞ (suc (suc Z))
        (ε ℚ₊· invℚ₊ ((fromSucℚ₊ Z) ℚ₊· 2))
  in λ n N<n →
    let
      growth-at-n = growth (suc (suc n))
        (ℕ.≤-trans N<n (ℕ.≤SumRight {k = 2}))

      root-growth-bound = growth-root-bound Z ε n growth-at-n

      scaled-growth-bound =
        rational-scaled-growth-bound Z ε n root-growth-bound

    in
    isTrans≤<ᵣ
      (lnSeq z n -ᵣ lnSeq' z n)
      ((2 ·ᵣ (fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1)) ·ᵣ lnSeq z n)
      (rat (fst ε))
      (sequence-gap-quadratic-bound z n 1≤z)
      (isTrans≤<ᵣ
        ((2 ·ᵣ (fst (z ^ℚ fst (stepℚ₊ n)) -ᵣ 1)) ·ᵣ lnSeq z n)
        ((2 ·ᵣ
          (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1))
          ·ᵣ (fromNat (suc (suc Z)) -ᵣ 1))
        (rat (fst ε))
        (sequence-product-upper-bound z Z n 1≤z z≤Z)
        (isTrans≡<ᵣ
          ((2 ·ᵣ
            (fst (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1))
            ·ᵣ (fromNat (suc (suc Z)) -ᵣ 1))
          (rat
              (([ pos (suc (suc Z)) / 1 ] ℚ.- [ pos 1 / 1 ]) ℚ.· 2)
            ·ᵣ
              (fst
                (fromNat (suc (suc Z)) ^ℚ fst (stepℚ₊ n)) -ᵣ 1))
          (rat (fst ε))
          (upper-product-coefficient-path Z n)
          scaled-growth-bound))
