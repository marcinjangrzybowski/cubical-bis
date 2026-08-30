module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕO
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Translation
  as Translation

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition

private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace


rationalAddition : ℚ → ℚ → ℚ
rationalAddition x y = x ℚR.+ y

private
  atom : ℚ₊ → ℚ₊
  atom ε = (ε /4₊) /4₊

  threeAtoms : ℚ₊ → ℚ₊
  threeAtoms ε = atom ε +₊ (atom ε +₊ atom ε)

  eightAtoms : ℚ₊ → ℚ₊
  eightAtoms ε =
    (atom ε +₊ (threeAtoms ε +₊ threeAtoms ε)) +₊ atom ε

  eight-reassociate : ∀ a →
    (a ℚR.+ ((a ℚR.+ (a ℚR.+ a)) ℚR.+
      (a ℚR.+ (a ℚR.+ a)))) ℚR.+ a ≡
    ((a ℚR.+ a) ℚR.+ (a ℚR.+ a)) ℚR.+
      ((a ℚR.+ a) ℚR.+ (a ℚR.+ a))
  eight-reassociate a = ℚ!

  fourAtoms≡quarter : ∀ ε →
    ((fst (atom ε) ℚR.+ fst (atom ε)) ℚR.+
      (fst (atom ε) ℚR.+ fst (atom ε))) ≡
    fst (ε /4₊)
  fourAtoms≡quarter ε =
    cong₂ ℚR._+_
      (/4+/4≡/2 (fst (ε /4₊)))
      (/4+/4≡/2 (fst (ε /4₊)))
    ∙ /2+/2≡id (fst (ε /4₊))

  eightAtoms≡half : ∀ ε →
    fst (eightAtoms ε) ≡ fst (ε /2₊)
  eightAtoms≡half ε =
    eight-reassociate (fst (atom ε))
    ∙ cong₂ ℚR._+_
        (fourAtoms≡quarter ε) (fourAtoms≡quarter ε)
    ∙ /4+/4≡/2 (fst ε)

  eightAtoms< : ∀ ε → eightAtoms ε <₊ ε
  eightAtoms< ε = begin<
    fst (eightAtoms ε)
      ≡→≤⟨ eightAtoms≡half ε ⟩
    fst (ε /2₊)
      <⟨ /2₊<id ε ⟩
    fst ε ◾


opaque
 rationalAddition-presCauchyGraphs :
   ∀ (x y z : ℕ → Real.ℝ) →
   (∀ n → B.BaseGraphClosure rationalAddition
     (x n) (y n) (z n)) →
   Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y → Real.Base.IsCauchySequence z
 rationalAddition-presCauchyGraphs
    x y z joint gx gy ε =
  PT.rec squash₁ withLeft (gx (atom ε))
  where
  withLeft : Real.Base.CauchyTail x (atom ε) →
    ∥ Real.Base.CauchyTail z ε ∥₁
  withLeft (K , xc) =
    PT.map (withRight K xc) (gy (atom ε))
    where
    withRight :
      (K : ℕ) →
      (∀ m n → K ℕO.≤ m → K ℕO.≤ n →
        x m Real.Base.≈ᶜ[ atom ε ] x n) →
      Real.Base.CauchyTail y (atom ε) →
      Real.Base.CauchyTail z ε
    close :
      (K : ℕ) →
      (∀ m n → K ℕO.≤ m → K ℕO.≤ n →
        x m Real.Base.≈ᶜ[ atom ε ] x n) →
      (L : ℕ) →
      (∀ m n → L ℕO.≤ m → L ℕO.≤ n →
        y m Real.Base.≈ᶜ[ atom ε ] y n) →
      ∀ m n → ℕ.max K L ℕO.≤ m → ℕ.max K L ℕO.≤ n →
      (Σ[ p ∈ ℚ ]
        Σ[ q ∈ ℚ ]
          (Real.ιℚ p Real.Base.≈ᶜ[ atom ε ] x m) ×
          (Real.ιℚ q Real.Base.≈ᶜ[ atom ε ] y m) ×
          (Real.ιℚ (rationalAddition p q)
            Real.Base.≈ᶜ[ atom ε ] z m)) →
      (Σ[ p ∈ ℚ ]
        Σ[ q ∈ ℚ ]
          (Real.ιℚ p Real.Base.≈ᶜ[ atom ε ] x n) ×
          (Real.ιℚ q Real.Base.≈ᶜ[ atom ε ] y n) ×
          (Real.ιℚ (rationalAddition p q)
            Real.Base.≈ᶜ[ atom ε ] z n)) →
      z m Real.Base.≈ᶜ[ ε ] z n
    close K xc L yc m n KL≤m KL≤n
      (p , q , p∼xm , q∼ym , sum∼zm)
      (p' , q' , p'∼xn , q'∼zn , sum'∼zn) =
      Real.Base.isMonotone≈ᶜ< (z m) (z n)
        (eightAtoms ε) ε (eightAtoms< ε)
        (Real.Premetric.tri≈ᶜ (z m)
          (Real.ιℚ (rationalAddition p' q')) (z n)
          (atom ε +₊ (threeAtoms ε +₊ threeAtoms ε))
          (atom ε)
          (Real.Premetric.tri≈ᶜ (z m)
            (Real.ιℚ (rationalAddition p q))
            (Real.ιℚ (rationalAddition p' q'))
            (atom ε) (threeAtoms ε +₊ threeAtoms ε)
            (Real.Base.sym≈ᶜ _ _ (atom ε) sum∼zm)
            (Real.Premetric.tri≈ᶜ
              (Real.ιℚ (rationalAddition p q))
              (Real.ιℚ (rationalAddition p' q))
              (Real.ιℚ (rationalAddition p' q'))
              (threeAtoms ε) (threeAtoms ε)
              p-sums-close q-sums-close))
          sum'∼zn)
      where
      K≤m : K ℕO.≤ m
      K≤m = ℕO.≤-trans
        (ℕO.left-≤-max {K} {L}) KL≤m

      K≤n : K ℕO.≤ n
      K≤n = ℕO.≤-trans
        (ℕO.left-≤-max {K} {L}) KL≤n

      L≤m : L ℕO.≤ m
      L≤m = ℕO.≤-trans
        (ℕO.right-≤-max {L} {K}) KL≤m

      L≤n : L ℕO.≤ n
      L≤n = ℕO.≤-trans
        (ℕO.right-≤-max {L} {K}) KL≤n

      p-close :
        Real.ιℚ p Real.Base.≈ᶜ[ threeAtoms ε ] Real.ιℚ p'
      p-close =
        Real.Premetric.tri≈ᶜ (Real.ιℚ p) (x m) (Real.ιℚ p')
          (atom ε) (atom ε +₊ atom ε) p∼xm
          (Real.Premetric.tri≈ᶜ (x m) (x n) (Real.ιℚ p')
            (atom ε) (atom ε)
            (xc m n K≤m K≤n)
            (Real.Base.sym≈ᶜ _ _ (atom ε) p'∼xn))

      q-close :
        Real.ιℚ q Real.Base.≈ᶜ[ threeAtoms ε ] Real.ιℚ q'
      q-close =
        Real.Premetric.tri≈ᶜ (Real.ιℚ q) (y m) (Real.ιℚ q')
          (atom ε) (atom ε +₊ atom ε) q∼ym
          (Real.Premetric.tri≈ᶜ (y m) (y n) (Real.ιℚ q')
            (atom ε) (atom ε)
            (yc m n L≤m L≤n)
            (Real.Base.sym≈ᶜ _ _ (atom ε) q'∼zn))

      p-sums-close :
        Real.ιℚ (rationalAddition p q)
          Real.Base.≈ᶜ[ threeAtoms ε ]
        Real.ιℚ (rationalAddition p' q)
      p-sums-close =
        Translation.translationⁿ q .snd
          .IsNonExpanding.pres≈
          (Real.ιℚ p) (Real.ιℚ p') (threeAtoms ε) p-close

      q-sums-close :
        Real.ιℚ (rationalAddition p' q)
          Real.Base.≈ᶜ[ threeAtoms ε ]
        Real.ιℚ (rationalAddition p' q')
      q-sums-close =
        subst2 (Real.Base._≈ᶜ[ threeAtoms ε ]_)
          (cong Real.ιℚ (ℚR.+Comm q p'))
          (cong Real.ιℚ (ℚR.+Comm q' p'))
          (Translation.translationⁿ p' .snd
            .IsNonExpanding.pres≈
            (Real.ιℚ q) (Real.ιℚ q') (threeAtoms ε) q-close)

    withRight K xc (L , yc) =
      ℕ.max K L , λ m n KL≤m KL≤n →
        PT.rec2 (Real.Base.isProp≈ᶜ (z m) ε (z n))
          (close K xc L yc m n KL≤m KL≤n)
          (joint m (atom ε) (atom ε) (atom ε))
          (joint n (atom ε) (atom ε) (atom ε))


rationalAddition-preservesCauchyGraphs :
  B.PreservesBaseCauchyGraphs rationalAddition
rationalAddition-preservesCauchyGraphs =
  B.preservesCauchyGraphs rationalAddition-presCauchyGraphs


addition : Real.ℝ → Real.ℝ → Real.ℝ
addition = B.extendBase
  rationalAddition rationalAddition-preservesCauchyGraphs

infixl 6 _+_

_+_ : Real.ℝ → Real.ℝ → Real.ℝ
_+_ = addition

add-diagonalIsCauchySequence : ∀ {x y} →
  Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y →
  Real.Base.IsCauchySequence (λ n → x n + y n)
add-diagonalIsCauchySequence {x} {y} =
  B.extend-preservesDiagonalCauchy
    (λ p q → Real.Base.ι (rationalAddition p q))
    rationalAddition-preservesCauchyGraphs x y

addition-joint : ∀ x y →
  B.BaseGraphClosure rationalAddition x y (x + y)
addition-joint =
  B.extend-graph
    (λ p q → Real.Base.ι (rationalAddition p q))
    rationalAddition-preservesCauchyGraphs

add-ι-ι : ∀ p q →
  Real.ιℚ p + Real.ιℚ q ≡ Real.ιℚ (p ℚR.+ q)
add-ι-ι p q = refl

add-ι-lim : ∀ p y gy →
  Real.ιℚ p + Real.Base.lim y gy ≡
  Real.Base.lim (λ n → Real.ιℚ p + y n) _
add-ι-lim p y gy = refl

add-lim-ι : ∀ x gx q →
  Real.Base.lim x gx + Real.ιℚ q ≡
  Real.Base.lim (λ n → x n + Real.ιℚ q) _
add-lim-ι x gx q = refl

add-lim-lim : ∀ x gx y gy →
  Real.Base.lim x gx + Real.Base.lim y gy ≡
  Real.Base.lim (λ n → x n + y n)
    (add-diagonalIsCauchySequence gx gy)
add-lim-lim x gx y gy =
  B.extend-lim-lim
    (λ p q → Real.Base.ι (rationalAddition p q))
    rationalAddition-preservesCauchyGraphs x gx y gy
