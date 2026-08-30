module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals as ℚData
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Translation
  as Tr
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding
  as NonExpandingDefinition

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing

private
  module L = NonExpandingDefinition ℚPremetricSpace ℚPremetricSpace


-- Only max with a rational right endpoint is needed to turn a metric ball
-- around zero into an order bound.  It is obtained by lifting rational max,
-- then identified with the independently developed lattice formula.

rationalMaxRightⁿ : ℚData.ℚ → NE[ ℚPremetricSpace , ℚPremetricSpace ]
rationalMaxRightⁿ r .fst q = ℚData.max q r
rationalMaxRightⁿ r .snd .IsNonExpanding.pres≈ q q′ ε q≈q′ =
  subst (ℚ._< fst ε)
    (cong abs
      (cong₂ ℚData._-_
        (ℚData.maxComm r q) (ℚData.maxComm r q′)))
    (ℚ.isTrans≤< _ _ _ (ℚ.maxDist r q′ q) q≈q′)

maxRightⁿ : ℚData.ℚ →
  NE[ Real.ℝPremetricSpace , Real.ℝPremetricSpace ]
maxRightⁿ r = L.liftNonExpanding (rationalMaxRightⁿ r)


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  maxRightPathElim : ∀ r → Real.Base.ElimCompletion-Prop
    (λ x → fst (maxRightⁿ r) x ≡ x ⊔ℝ Real.ιℚ r)
  maxRightPathElim r .Real.Base.ElimCompletion-Prop.ιA q = sym (max-ι q r)
  maxRightPathElim r .Real.Base.ElimCompletion-Prop.limA x gx IH =
      lim-cong _ _ (funExt IH)
    ∙ sym (max-lim-left x gx (Real.ιℚ r))
  maxRightPathElim r .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _


maxRightPath : ∀ r x → fst (maxRightⁿ r) x ≡ x ⊔ℝ Real.ιℚ r
maxRightPath r = Real.Base.ElimCompletion-Prop.go (maxRightPathElim r)

maxRational-pres≈₁ : ∀ r x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  (x ⊔ℝ Real.ιℚ r) Real.Base.≈ᶜ[ ε ] (y ⊔ℝ Real.ιℚ r)
maxRational-pres≈₁ r x y ε x∼y =
  subst2 (Real.Base._≈ᶜ[ ε ]_)
    (maxRightPath r x) (maxRightPath r y)
    (maxRightⁿ r .snd .IsNonExpanding.pres≈ x y ε x∼y)


-- The rational-endpoint estimate extends to an arbitrary completed
-- endpoint without choosing a common Cauchy modulus.  In the limit case we
-- first use roundedness to move the input closeness to a strictly smaller
-- radius.  The pointwise induction hypotheses then pass to the two limits;
-- the truncated smaller-radius witness is eliminated only into closeness.

private
  constantIsCauchySequence : ∀ x →
    Real.Base.IsCauchySequence (λ _ → x)
  constantIsCauchySequence x ε =
    ∣ 0 , (λ _ _ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁

  maxRightSequenceWitness : ∀ {a} →
    Real.Base.IsCauchySequence a → ∀ x →
    Real.Base.IsCauchySequence (λ n → a n ⊔ℝ x)
  maxRightSequenceWitness ga x =
    max-diagonalIsCauchySequence ga (constantIsCauchySequence x)

  maxLimitRightPath : ∀ a ga x →
    Real.Base.lim a ga ⊔ℝ x ≡
    Real.Base.lim (λ n → a n ⊔ℝ x)
      (maxRightSequenceWitness ga x)
  maxLimitRightPath a ga x =
      max-lim-left a ga x
    ∙ cong (Real.Base.lim (λ n → a n ⊔ℝ x))
        (Real.Base.isPropIsCauchySequence
          (λ n → a n ⊔ℝ x) _ _)

  maxIsNonExpanding₂Elim : Real.Base.ElimCompletion-Prop
    (λ a → IsNonExpanding
      (snd Real.ℝPremetricSpace) (a ⊔ℝ_)
      (snd Real.ℝPremetricSpace))
  maxIsNonExpanding₂Elim .Real.Base.ElimCompletion-Prop.ιA p
    .IsNonExpanding.pres≈ x y ε x≈y =
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (max-comm x (Real.ιℚ p))
        (max-comm y (Real.ιℚ p))
        (maxRational-pres≈₁ p x y ε x≈y)
  maxIsNonExpanding₂Elim .Real.Base.ElimCompletion-Prop.limA
    a ga IH .IsNonExpanding.pres≈ x y ε x≈y =
      PT.rec (Real.Base.isProp≈ᶜ _ ε _) passToLimits
        (Real.Approximation.isRounded≈ᶜ x y ε x≈y)
    where
    passToLimits :
      Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x Real.Base.≈ᶜ[ δ ] y) →
      (Real.Base.lim a ga ⊔ℝ x)
        Real.Base.≈ᶜ[ ε ] (Real.Base.lim a ga ⊔ℝ y)
    passToLimits (δ , δ<ε , x≈δy) =
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (sym (maxLimitRightPath a ga x))
        (sym (maxLimitRightPath a ga y))
        (limits-preserve-closeness-below
          (maxRightSequenceWitness ga x)
          (maxRightSequenceWitness ga y)
          δ ε δ<ε
          (λ n → IH n .IsNonExpanding.pres≈ x y δ x≈δy))
  maxIsNonExpanding₂Elim .Real.Base.ElimCompletion-Prop.isPropA a =
    isPropIsNonExpanding
      (snd Real.ℝPremetricSpace) (a ⊔ℝ_)
      (snd Real.ℝPremetricSpace)


maxIsNonExpanding₂ : ∀ a →
  IsNonExpanding
    (snd Real.ℝPremetricSpace) (a ⊔ℝ_)
    (snd Real.ℝPremetricSpace)
maxIsNonExpanding₂ =
  Real.Base.ElimCompletion-Prop.go maxIsNonExpanding₂Elim


max-pres≈₂ : ∀ a x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  (a ⊔ℝ x) Real.Base.≈ᶜ[ ε ] (a ⊔ℝ y)
max-pres≈₂ a x y ε =
  maxIsNonExpanding₂ a .IsNonExpanding.pres≈ x y ε


maxIsNonExpanding₁ : ∀ b →
  IsNonExpanding
    (snd Real.ℝPremetricSpace) (λ a → a ⊔ℝ b)
    (snd Real.ℝPremetricSpace)
maxIsNonExpanding₁ b .IsNonExpanding.pres≈ a a' ε a≈a' =
  subst2 (Real.Base._≈ᶜ[ ε ]_)
    (max-comm b a) (max-comm b a')
    (max-pres≈₂ b a a' ε a≈a')


max-pres≈₁ : ∀ a a' b ε →
  a Real.Base.≈ᶜ[ ε ] a' →
  (a ⊔ℝ b) Real.Base.≈ᶜ[ ε ] (a' ⊔ℝ b)
max-pres≈₁ a a' b ε =
  maxIsNonExpanding₁ b .IsNonExpanding.pres≈ a a' ε


minIsNonExpanding₂ : ∀ a →
  IsNonExpanding
    (snd Real.ℝPremetricSpace) (a ⊓ℝ_)
    (snd Real.ℝPremetricSpace)
minIsNonExpanding₂ a .IsNonExpanding.pres≈ x y ε x≈y =
  Neg.neg-pres≈
    ((Neg.- a) ⊔ℝ (Neg.- x))
    ((Neg.- a) ⊔ℝ (Neg.- y)) ε
    (max-pres≈₂ (Neg.- a) (Neg.- x) (Neg.- y) ε
      (Neg.neg-pres≈ x y ε x≈y))


min-pres≈₂ : ∀ a x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  (a ⊓ℝ x) Real.Base.≈ᶜ[ ε ] (a ⊓ℝ y)
min-pres≈₂ a x y ε =
  minIsNonExpanding₂ a .IsNonExpanding.pres≈ x y ε


minIsNonExpanding₁ : ∀ b →
  IsNonExpanding
    (snd Real.ℝPremetricSpace) (λ a → a ⊓ℝ b)
    (snd Real.ℝPremetricSpace)
minIsNonExpanding₁ b .IsNonExpanding.pres≈ a a' ε a≈a' =
  subst2 (Real.Base._≈ᶜ[ ε ]_)
    (min-comm b a) (min-comm b a')
    (min-pres≈₂ b a a' ε a≈a')


min-pres≈₁ : ∀ a a' b ε →
  a Real.Base.≈ᶜ[ ε ] a' →
  (a ⊓ℝ b) Real.Base.≈ᶜ[ ε ] (a' ⊓ℝ b)
min-pres≈₁ a a' b ε =
  minIsNonExpanding₁ b .IsNonExpanding.pres≈ a a' ε


opaque
  closeZero→upperBound : ∀ z ε →
    z Real.Base.≈ᶜ[ ε ] Real.ιℚ 0 → z ≤ℝ Real.ιℚ (fst ε)
  closeZero→upperBound z ε z∼ε0 =
    PT.rec (isProp≤ℝ z (Real.ιℚ (fst ε))) proveAtSmallerRadius
      (Real.Approximation.isRounded≈ᶜ z (Real.ιℚ 0) ε z∼ε0)
    where
    proveAtSmallerRadius :
      Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) ×
        (z Real.Base.≈ᶜ[ κ ] Real.ιℚ 0) →
      z ≤ℝ Real.ιℚ (fst ε)
    proveAtSmallerRadius (κ , κ<ε , z∼κ0) =
      Real.Base.eqCompletion (z ⊔ℝ Real.ιℚ (fst ε)) (Real.ιℚ (fst ε))
        proveCloseness
      where
      proveCloseness : ∀ θ →
        (z ⊔ℝ Real.ιℚ (fst ε))
          Real.Base.≈ᶜ[ θ ] Real.ιℚ (fst ε)
      proveCloseness θ =
        PT.rec (Real.Base.isProp≈ᶜ _ θ _) proveFromApproximation
          (Real.rationalsDense z α)
        where
        gap : ℚ₊
        gap = [ ε -₊ κ ]⟨ κ<ε ⟩

        α : ℚ₊
        α = min₊ θ gap /2₊

        α<θ : α <₊ θ
        α<θ = min/2₊<L θ gap

        α<gap : α <₊ gap
        α<gap = min/2₊<R θ gap

        α+κ<ε : (α +₊ κ) <₊ ε
        α+κ<ε =
          subst (fst (α +₊ κ) ℚ.<_)
            (minusPlus₊ ε κ)
            (ℚ.<-+o (fst α) (fst gap) (fst κ) α<gap)

        proveFromApproximation :
          Σ[ q ∈ ℚData.ℚ ] (Real.ιℚ q Real.Base.≈ᶜ[ α ] z) →
          (z ⊔ℝ Real.ιℚ (fst ε))
            Real.Base.≈ᶜ[ θ ] Real.ιℚ (fst ε)
        proveFromApproximation (q , ιq∼αz) =
          Real.Base.isMonotone≈ᶜ< _ _ α θ α<θ
            (subst
              ((z ⊔ℝ Real.ιℚ (fst ε)) Real.Base.≈ᶜ[ α ]_)
              maxRatPath
              (maxRational-pres≈₁ (fst ε) z (Real.ιℚ q) α
                (Real.Base.sym≈ᶜ (Real.ιℚ q) z α ιq∼αz)))
          where
          embeddedClose :
            Real.ιℚ q Real.Base.≈ᶜ[ α +₊ κ ] Real.ιℚ 0
          embeddedClose =
            Real.Premetric.tri≈ᶜ (Real.ιℚ q) z (Real.ιℚ 0) α κ ιq∼αz z∼κ0

          qMinusZero : q ℚData.- 0 ≡ q
          qMinusZero = ℚ!

          absq<α+κ : abs q ℚ.< fst (α +₊ κ)
          absq<α+κ =
            subst2 ℚ._<_ (cong abs qMinusZero) refl
              (Real.Approximation.ι-ι→≈ q 0 (α +₊ κ) embeddedClose)

          q<ε : q ℚ.< fst ε
          q<ε =
            ℚ.isTrans≤< q (abs q) (fst ε)
              (≤abs q)
              (ℚ.isTrans< (abs q) (fst (α +₊ κ)) (fst ε)
                absq<α+κ α+κ<ε)

          maxRatPath :
            Real.ιℚ q ⊔ℝ Real.ιℚ (fst ε) ≡ Real.ιℚ (fst ε)
          maxRatPath =
              max-ι q (fst ε)
            ∙ cong Real.ιℚ
                (ℚ.≤→max q (fst ε) (ℚ.<Weaken≤ q (fst ε) q<ε))


closeZero→lowerBound : ∀ z ε →
  z Real.Base.≈ᶜ[ ε ] Real.ιℚ 0 → Real.ιℚ (ℚData.- fst ε) ≤ℝ z
closeZero→lowerBound z ε z∼ε0 =
  subst2 _≤ℝ_
    (Neg.neg-ι (fst ε)) (Neg.neg-involutive z)
    (neg-reverses≤ (Neg.- z) (Real.ιℚ (fst ε))
      (closeZero→upperBound (Neg.- z) ε
        (subst ((Neg.- z) Real.Base.≈ᶜ[ ε ]_)
          neg-zero (Neg.neg-pres≈ z (Real.ιℚ 0) ε z∼ε0))))


private
  translateBackPath : ∀ p x →
    Tr.translate (ℚData.- p) x Add.+ Real.ιℚ p ≡ x
  translateBackPath p x =
      cong (Add._+ Real.ιℚ p) (translate-as-add (ℚData.- p) x)
    ∙ sym (add-assoc x (Real.ιℚ (ℚData.- p)) (Real.ιℚ p))
    ∙ cong (x Add.+_) (Add.add-ι-ι (ℚData.- p) p)
    ∙ cong (x Add.+_) (cong Real.ιℚ ℚ!)
    ∙ add-zero-right x

  translateCloseToZero : ∀ p x ε →
    x Real.Base.≈ᶜ[ ε ] Real.ιℚ p →
    Tr.translate (ℚData.- p) x Real.Base.≈ᶜ[ ε ] Real.ιℚ 0
  translateCloseToZero p x ε x∼p =
    subst (Tr.translate (ℚData.- p) x Real.Base.≈ᶜ[ ε ]_)
      (Tr.translate-ι (ℚData.- p) p ∙ cong Real.ιℚ ℚ!)
      (Tr.translate-pres≈ (ℚData.- p) x (Real.ιℚ p) ε x∼p)


closeToRational→upperBound : ∀ p x ε →
  x Real.Base.≈ᶜ[ ε ] Real.ιℚ p →
  x ≤ℝ Real.ιℚ (p ℚData.+ fst ε)
closeToRational→upperBound p x ε x∼p =
  subst2 _≤ℝ_
    (translateBackPath p x)
    (Add.add-ι-ι (fst ε) p ∙ cong Real.ιℚ (ℚData.+Comm (fst ε) p))
    (add-preserves≤-right
      (Tr.translate (ℚData.- p) x) (Real.ιℚ (fst ε)) (Real.ιℚ p)
      (closeZero→upperBound
        (Tr.translate (ℚData.- p) x) ε
        (translateCloseToZero p x ε x∼p)))

closeToRational→lowerBound : ∀ p x ε →
  x Real.Base.≈ᶜ[ ε ] Real.ιℚ p →
  Real.ιℚ (p ℚData.- fst ε) ≤ℝ x
closeToRational→lowerBound p x ε x∼p =
  subst2 _≤ℝ_
    (Add.add-ι-ι (ℚData.- fst ε) p ∙ cong Real.ιℚ ℚ!)
    (translateBackPath p x)
    (add-preserves≤-right
      (Real.ιℚ (ℚData.- fst ε))
      (Tr.translate (ℚData.- p) x) (Real.ιℚ p)
      (closeZero→lowerBound
        (Tr.translate (ℚData.- p) x) ε
        (translateCloseToZero p x ε x∼p)))


rationalClose→upperBound : ∀ p x ε →
  Real.ιℚ p Real.Base.≈ᶜ[ ε ] x →
  Real.ιℚ p ≤ℝ (x Add.+ Real.ιℚ (fst ε))
rationalClose→upperBound p x ε p∼x =
  subst (λ z → z ≤ℝ (x Add.+ Real.ιℚ (fst ε))) leftPath
    (add-preserves≤-right
      (Real.ιℚ (p ℚData.- fst ε)) x (Real.ιℚ (fst ε))
      (closeToRational→lowerBound p x ε
        (Real.Base.sym≈ᶜ (Real.ιℚ p) x ε p∼x)))
  where
  leftPath :
    Real.ιℚ (p ℚData.- fst ε) Add.+ Real.ιℚ (fst ε) ≡ Real.ιℚ p
  leftPath = Add.add-ι-ι (p ℚData.- fst ε) (fst ε) ∙ cong Real.ιℚ ℚ!

rationalClose→lowerBound : ∀ p x ε →
  Real.ιℚ p Real.Base.≈ᶜ[ ε ] x →
  x ≤ℝ Real.ιℚ (p ℚData.+ fst ε)
rationalClose→lowerBound p x ε p∼x =
  closeToRational→upperBound p x ε
    (Real.Base.sym≈ᶜ (Real.ιℚ p) x ε p∼x)


-- Arbitrary translation is now known to be nonexpanding, so the
-- zero-centred estimate extends without loss to arbitrary centres.

close→upperBound : ∀ x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  x ≤ℝ (y Add.+ Real.ιℚ (fst ε))
close→upperBound x y ε x∼y =
  subst2 _≤ℝ_
    (sub-add-cancel x y)
    (add-comm (Real.ιℚ (fst ε)) y)
    (add-preserves≤-right
      (x Group.- y) (Real.ιℚ (fst ε)) y
      (closeZero→upperBound (x Group.- y) ε
        (subst ((x Group.- y) Real.Base.≈ᶜ[ ε ]_)
          (sub-self y)
          (add-pres≈₁ x y (Neg.- y) ε x∼y))))


close→lowerBound : ∀ x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  (y Group.- Real.ιℚ (fst ε)) ≤ℝ x
close→lowerBound x y ε x∼y =
  subst ((y Group.- Real.ιℚ (fst ε)) ≤ℝ_)
    (add-sub-cancel x (Real.ιℚ (fst ε)))
    (add-preserves≤-right
      y (x Add.+ Real.ιℚ (fst ε))
      (Neg.- Real.ιℚ (fst ε))
      (close→upperBound y x ε
        (Real.Base.sym≈ᶜ x y ε x∼y)))


closeness→absDifference< : ∀ x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  Abs.absℝ (x Group.- y) <ℝ Real.ιℚ (fst ε)
closeness→absDifference< x y ε x∼y =
  PT.rec (isProp<ℝ (Abs.absℝ (x Group.- y)) (Real.ιℚ (fst ε)))
    proveAtSmallerRadius
    (Real.Approximation.isRounded≈ᶜ x y ε x∼y)
  where
  proveAtSmallerRadius :
    Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) ×
      (x Real.Base.≈ᶜ[ κ ] y) →
    Abs.absℝ (x Group.- y) <ℝ Real.ιℚ (fst ε)
  proveAtSmallerRadius (κ , κ<ε , x∼κy) =
    ≤<ℝ-trans
      (Abs.absℝ (x Group.- y))
      (Real.ιℚ (fst κ))
      (Real.ιℚ (fst ε))
      (closeZero→upperBound (Abs.absℝ (x Group.- y)) κ
        (subst (Abs.absℝ (x Group.- y) Real.Base.≈ᶜ[ κ ]_)
          Abs.absℝ-zero
          (Abs.absℝ-pres≈ (x Group.- y) (Real.ιℚ 0) κ
            (subst ((x Group.- y) Real.Base.≈ᶜ[ κ ]_)
              (sub-self y)
              (add-pres≈₁ x y (Neg.- y) κ x∼κy)))))
      (<ℚ→<ℝ (fst κ) (fst ε) κ<ε)


-- A closed absolute-value bound at a smaller rational radius is enough for
-- primitive closeness.  Rational density is eliminated only into the
-- proposition `z ≈ 0`; no rational approximation is selected globally.

absBound→closeZeroAbove : ∀ z ρ ε →
  ρ <₊ ε →
  Abs.absℝ z ≤ℝ Real.ιℚ (fst ρ) →
  z Real.Base.≈ᶜ[ ε ] Real.ιℚ 0
absBound→closeZeroAbove z ρ ε ρ<ε absz≤ρ =
  PT.rec (Real.Base.isProp≈ᶜ z ε (Real.ιℚ 0))
    proveFromApproximation (Real.rationalsDense z α)
  where
  gap : ℚ₊
  gap = [ ε -₊ ρ ]⟨ ρ<ε ⟩

  α : ℚ₊
  α = gap /4₊

  β : ℚ₊
  β = ρ +₊ (α +₊ α)

  threeα<gap : (α +₊ (α +₊ α)) <₊ gap
  threeα<gap =
    subst2 ℚ._<_
      ℚ!
      (1/2∈ℚ./2+/2≡id (fst gap))
      (ℚ.<-o+
        (fst α) (fst (gap /2₊)) (fst (gap /2₊))
        (/4₊</2₊ gap))

  α+β<ε : (α +₊ β) <₊ ε
  α+β<ε =
    subst2 ℚ._<_
      ℚ!
      (minusPlus₊ ε ρ)
      (ℚ.<-+o
        (fst (α +₊ (α +₊ α))) (fst gap) (fst ρ)
        threeα<gap)

  proveFromApproximation :
    Σ[ q ∈ ℚData.ℚ ]
      (Real.ιℚ q Real.Base.≈ᶜ[ α ] z) →
    z Real.Base.≈ᶜ[ ε ] Real.ιℚ 0
  proveFromApproximation (q , ιq∼αz) =
    Real.Base.isMonotone≈ᶜ< z (Real.ιℚ 0)
      (α +₊ β) ε α+β<ε
      (Real.Premetric.tri≈ᶜ z (Real.ιℚ q) (Real.ιℚ 0) α β
        (Real.Base.sym≈ᶜ (Real.ιℚ q) z α ιq∼αz)
        (Real.Base.ι-ι q 0 β
          (subst (ℚ._< fst β)
            (sym (cong abs qMinusZero))
            absq<β)))
    where
    qMinusZero : q ℚData.- 0 ≡ q
    qMinusZero = ℚ!

    embeddedAbsPath :
      Abs.absℝ (Real.ιℚ q) ≡ Real.ιℚ (abs q)
    embeddedAbsPath = Abs.absℝ-ι q

    ratAbsq≤absz+α :
      Real.ιℚ (abs q) ≤ℝ
      (Abs.absℝ z Add.+ Real.ιℚ (fst α))
    ratAbsq≤absz+α =
      subst (_≤ℝ (Abs.absℝ z Add.+ Real.ιℚ (fst α)))
        embeddedAbsPath
        (close→upperBound
          (Abs.absℝ (Real.ιℚ q)) (Abs.absℝ z) α
          (Abs.absℝ-pres≈ (Real.ιℚ q) z α ιq∼αz))

    ratAbsq≤ρ+α :
      Real.ιℚ (abs q) ≤ℝ
      Real.ιℚ (fst ρ ℚData.+ fst α)
    ratAbsq≤ρ+α =
      ≤ℝ-trans
        (Real.ιℚ (abs q))
        (Abs.absℝ z Add.+ Real.ιℚ (fst α))
        (Real.ιℚ (fst ρ ℚData.+ fst α))
        ratAbsq≤absz+α
        (subst
          ((Abs.absℝ z Add.+ Real.ιℚ (fst α)) ≤ℝ_)
          (Add.add-ι-ι (fst ρ) (fst α))
          (add-monotone
            (Abs.absℝ z) (Real.ιℚ (fst ρ))
            (Real.ιℚ (fst α)) (Real.ιℚ (fst α))
            absz≤ρ (≤ℝ-refl (Real.ιℚ (fst α)))))

    absq≤ρ+α : abs q ℚ.≤ (fst ρ ℚData.+ fst α)
    absq≤ρ+α =
      rationalOrderReflects
        (abs q) (fst ρ ℚData.+ fst α) ratAbsq≤ρ+α

    absq<β : abs q ℚ.< fst β
    absq<β =
      ℚ.isTrans≤<
        (abs q) (fst ρ ℚData.+ fst α) (fst β)
        absq≤ρ+α
        (subst2 ℚ._<_
          (ℚData.+Comm (fst α) (fst ρ))
          (ℚData.+Comm (fst (α +₊ α)) (fst ρ))
          (ℚ.<-+o
            (fst α) (fst (α +₊ α)) (fst ρ)
            (<₊SumLeft α α)))


absDifference<→closeness : ∀ x y ε →
  Abs.absℝ (x Group.- y) <ℝ Real.ιℚ (fst ε) →
  x Real.Base.≈ᶜ[ ε ] y
absDifference<→closeness x y ε =
  PT.rec (Real.Base.isProp≈ᶜ x ε y) proveFromGap
  where
  proveFromGap :
    PositiveGap (Abs.absℝ (x Group.- y)) (Real.ιℚ (fst ε)) →
    x Real.Base.≈ᶜ[ ε ] y
  proveFromGap w =
    subst2 (Real.Base._≈ᶜ[ ε ]_)
      (sub-add-cancel x y)
      (add-zero-left y)
      (add-pres≈₁ (x Group.- y) (Real.ιℚ 0) y ε
        (absBound→closeZeroAbove
          (x Group.- y) ρ ε ρ<ε absDiff≤ρ))
    where
    δ : ℚ₊
    δ = width w

    absDiff+δ≤ε :
      Abs.absℝ (x Group.- y) Add.+ Real.ιℚ (fst δ) ≤ℝ
      Real.ιℚ (fst ε)
    absDiff+δ≤ε = bound w

    δ≤ε : fst δ ℚ.≤ fst ε
    δ≤ε =
      rationalOrderReflects (fst δ) (fst ε)
        (≤ℝ-trans
          (Real.ιℚ (fst δ))
          (Abs.absℝ (x Group.- y) Add.+ Real.ιℚ (fst δ))
          (Real.ιℚ (fst ε))
          (subst
            (_≤ℝ (Abs.absℝ (x Group.- y) Add.+ Real.ιℚ (fst δ)))
            (add-zero-left (Real.ιℚ (fst δ)))
            (add-monotone
              (Real.ιℚ 0) (Abs.absℝ (x Group.- y))
              (Real.ιℚ (fst δ)) (Real.ιℚ (fst δ))
              (zero≤abs (x Group.- y))
              (≤ℝ-refl (Real.ιℚ (fst δ)))))
          absDiff+δ≤ε)

    δ/2<ε : (δ /2₊) <₊ ε
    δ/2<ε =
      ℚ.isTrans<≤
        (fst (δ /2₊)) (fst δ) (fst ε)
        (/2₊<id δ) δ≤ε

    ρ : ℚ₊
    ρ = [ ε -₊ (δ /2₊) ]⟨ δ/2<ε ⟩

    ρ<ε : ρ <₊ ε
    ρ<ε =
      subst (fst ρ ℚ.<_)
        (minusPlus₊ ε (δ /2₊))
        (<₊SumLeft ρ (δ /2₊))

    halfδ≤δ : fst (δ /2₊) ℚ.≤ fst δ
    halfδ≤δ =
      ℚ.<Weaken≤ _ _ (/2₊<id δ)

    absDiff+halfδ≤ε :
      Abs.absℝ (x Group.- y) Add.+ Real.ιℚ (fst (δ /2₊)) ≤ℝ
      Real.ιℚ (fst ε)
    absDiff+halfδ≤ε =
      ≤ℝ-trans
        (Abs.absℝ (x Group.- y) Add.+ Real.ιℚ (fst (δ /2₊)))
        (Abs.absℝ (x Group.- y) Add.+ Real.ιℚ (fst δ))
        (Real.ιℚ (fst ε))
        (add-preserves≤-left
          (Real.ιℚ (fst (δ /2₊))) (Real.ιℚ (fst δ))
          (Abs.absℝ (x Group.- y))
          (≤ℚ→≤ℝ (fst (δ /2₊)) (fst δ) halfδ≤δ))
        absDiff+δ≤ε

    ρ+halfδPath :
      Real.ιℚ (fst ρ) Add.+ Real.ιℚ (fst (δ /2₊)) ≡
      Real.ιℚ (fst ε)
    ρ+halfδPath =
      Add.add-ι-ι (fst ρ) (fst (δ /2₊))
      ∙ cong Real.ιℚ (minusPlus₊ ε (δ /2₊))

    absDiff≤ρ :
      Abs.absℝ (x Group.- y) ≤ℝ Real.ιℚ (fst ρ)
    absDiff≤ρ =
      add-reflects≤-right
        (Abs.absℝ (x Group.- y)) (Real.ιℚ (fst ρ))
        (Real.ιℚ (fst (δ /2₊)))
        (subst
          ((Abs.absℝ (x Group.- y) Add.+
            Real.ιℚ (fst (δ /2₊))) ≤ℝ_)
          (sym ρ+halfδPath)
          absDiff+halfδ≤ε)


closeness≃absDifference< : ∀ x y ε →
  (x Real.Base.≈ᶜ[ ε ] y) ≃
  (Abs.absℝ (x Group.- y) <ℝ Real.ιℚ (fst ε))
closeness≃absDifference< x y ε =
  propBiimpl→Equiv
    (Real.Base.isProp≈ᶜ x ε y)
    (isProp<ℝ (Abs.absℝ (x Group.- y)) (Real.ιℚ (fst ε)))
    (closeness→absDifference< x y ε)
    (absDifference<→closeness x y ε)
