module Cubical.Analysis.Real.Order.Metric.AbsoluteDifference where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using (_≃_; equivFun; invEq; propBiimpl→Equiv)

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
import Cubical.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Relation.Premetric.Base using (PremetricStr)

open import Cubical.Analysis.Real.Base
  using
    ( ℝ; rat; ℝPremetricSpace; _∼[_]_; rat-rat; rat-rat-reflects
    ; rat-dense; refl∼; sym∼; triangle∼
    )
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Addition
  using (_+_; rat+rat; add-pres∼₁)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addIdL; addIdR; addComm; addAssoc)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
  using (_-_; addInvL; subSelf)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
  using (absℝ; abs-rat; abs-pres∼; absZero)
open import Cubical.Analysis.Real.Order.Base
  using (_≤ℝ_; isProp≤ℝ; ≤ℝ-refl; ≤ℝ-trans; rat≤rat≃)
open import Cubical.Analysis.Real.Order.Addition
  using (addPres≤R; addPres≤L; addReflects≤R)
open import Cubical.Analysis.Real.Order.AbsoluteValue
  using (absNonnegative)
open import Cubical.Analysis.Real.Order.Metric
  using (closeZero→upperBound; close→upperBound)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties using (≤<ℝ-trans)

open ℚInstance.PositiveRationals
  using
    ( ℚ₊; _+₊_; [_-₊_]⟨_⟩; minusPlus₊; <₊SumLeft )
open ℚInstance.PositiveRationals.PositiveHalvesℚ
  using (_/2₊; _/4₊; /2₊<id; /4₊</2₊)

private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)
  module ℚOrdered =
    OrderedProperties.OrderedCommRingTheory ℚInstance.ℚOrderedCommRing

  rationalSubZero : ∀ q → q ℚ.- 0 ≡ q
  rationalSubZero q =
    cong (q ℚ.+_) (ℚ.·AnnihilR (ℚ.- 1))
    ∙ ℚ.+IdR q

  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x


closeness→absDifference< : ∀ x y ε →
  x ∼[ ε ] y → absℝ (x - y) <ℝ rat (fst ε)
closeness→absDifference< x y ε x∼εy =
  PT.rec (isProp<ℝ (absℝ (x - y)) (rat (fst ε)))
    proveAtSmallerRadius
    (Pℝ.isRounded≈ x y ε x∼εy)
  where
  proveAtSmallerRadius :
    Σ[ κ ∈ ℚ₊ ]
      (fst κ ℚOrder.< fst ε) × (x ∼[ κ ] y) →
    absℝ (x - y) <ℝ rat (fst ε)
  proveAtSmallerRadius (κ , κ<ε , x∼κy) =
    ≤<ℝ-trans
      (absℝ (x - y)) (rat (fst κ)) (rat (fst ε))
      (closeZero→upperBound (absℝ (x - y)) κ
        (subst (absℝ (x - y) ∼[ κ ]_) absZero
          (abs-pres∼ (x - y) 0ℝ κ
            (subst ((x - y) ∼[ κ ]_) (subSelf y)
              (add-pres∼₁ x y (- y) κ x∼κy)))))
      (<ℚ→<ℝ (fst κ) (fst ε) κ<ε)

absBound→closeZeroAbove : ∀ z ρ ε →
  fst ρ ℚOrder.< fst ε →
  absℝ z ≤ℝ rat (fst ρ) →
  z ∼[ ε ] 0ℝ
absBound→closeZeroAbove z ρ ε ρ<ε absz≤ρ =
  PT.rec (Pℝ.isProp≈ z 0ℝ ε) proveFromApproximation
    (rat-dense z α)
  where
  gap : ℚ₊
  gap = [ ε -₊ ρ ]⟨ ρ<ε ⟩

  α : ℚ₊
  α = gap /4₊

  β : ℚ₊
  β = ρ +₊ (α +₊ α)

  threeα<gap :
    fst (α +₊ (α +₊ α)) ℚOrder.< fst gap
  threeα<gap = subst2 ℚOrder._<_
    (ℚ.+Comm (fst (gap /2₊)) (fst α)
    ∙ cong (fst α ℚ.+_)
        (sym (ℚInstance.1/2∈ℚ./4+/4≡/2 (fst gap))))
    (ℚInstance.1/2∈ℚ./2+/2≡id (fst gap))
    (ℚOrder.<-o+
      (fst α) (fst (gap /2₊)) (fst (gap /2₊))
      (/4₊</2₊ gap))

  reassociateαβ :
    fst (α +₊ β) ≡
    fst (α +₊ (α +₊ α)) ℚ.+ fst ρ
  reassociateαβ =
    ℚ.+Assoc (fst α) (fst ρ) (fst (α +₊ α))
    ∙ cong (ℚ._+ fst (α +₊ α))
        (ℚ.+Comm (fst α) (fst ρ))
    ∙ sym (ℚ.+Assoc (fst ρ) (fst α) (fst (α +₊ α)))
    ∙ ℚ.+Comm (fst ρ) (fst (α +₊ (α +₊ α)))

  α+β<ε : fst (α +₊ β) ℚOrder.< fst ε
  α+β<ε = subst2 ℚOrder._<_
    (sym reassociateαβ) (minusPlus₊ ε ρ)
    (ℚOrder.<-+o
      (fst (α +₊ (α +₊ α)))
      (fst gap) (fst ρ) threeα<gap)

  proveFromApproximation :
    Σ[ q ∈ ℚ ] rat q ∼[ α ] z → z ∼[ ε ] 0ℝ
  proveFromApproximation (q , ratq∼αz) =
    Pℝ.isMonotone≈< z 0ℝ (α +₊ β) ε α+β<ε
      (triangle∼ z (rat q) 0ℝ α β
        (sym∼ (rat q) z α ratq∼αz)
        (rat-rat q 0 β
          (subst
            (λ u → ℚOrdered.abs u ℚOrder.< fst β)
            (sym (rationalSubZero q)) absq<β)))
    where
    ratAbsq≤absz+α :
      rat (ℚOrdered.abs q) ≤ℝ absℝ z + rat (fst α)
    ratAbsq≤absz+α =
      subst (_≤ℝ (absℝ z + rat (fst α))) (abs-rat q)
        (close→upperBound
          (absℝ (rat q)) (absℝ z) α
          (abs-pres∼ (rat q) z α ratq∼αz))

    ratAbsq≤ρ+α :
      rat (ℚOrdered.abs q) ≤ℝ rat (fst ρ ℚ.+ fst α)
    ratAbsq≤ρ+α = ≤ℝ-trans
      (rat (ℚOrdered.abs q))
      (absℝ z + rat (fst α))
      (rat (fst ρ ℚ.+ fst α))
      ratAbsq≤absz+α
      (subst ((absℝ z + rat (fst α)) ≤ℝ_)
        (rat+rat (fst ρ) (fst α))
        (addPres≤R
          (absℝ z) (rat (fst ρ)) (rat (fst α)) absz≤ρ))

    absq≤ρ+α :
      ℚOrdered.abs q ℚOrder.≤ fst ρ ℚ.+ fst α
    absq≤ρ+α = equivFun
      (rat≤rat≃ (ℚOrdered.abs q) (fst ρ ℚ.+ fst α))
      ratAbsq≤ρ+α

    absq<β : ℚOrdered.abs q ℚOrder.< fst β
    absq<β = ℚOrder.isTrans≤<
      (ℚOrdered.abs q) (fst ρ ℚ.+ fst α) (fst β)
      absq≤ρ+α
      (ℚOrder.<-o+
        (fst α) (fst (α +₊ α)) (fst ρ)
        (<₊SumLeft α α))

absDifference<→closeness : ∀ x y ε →
  absℝ (x - y) <ℝ rat (fst ε) → x ∼[ ε ] y
absDifference<→closeness x y ε =
  PT.rec (Pℝ.isProp≈ x y ε) proveFromGap
  where
  proveFromGap :
    PositiveGap (absℝ (x - y)) (rat (fst ε)) → x ∼[ ε ] y
  proveFromGap (δ , absDiff+δ≤ε) =
    subst2 (_∼[ ε ]_)
      (subAddCancel x y) (addIdL y)
      (add-pres∼₁ (x - y) 0ℝ y ε
        (absBound→closeZeroAbove
          (x - y) ρ ε ρ<ε absDiff≤ρ))
    where
    δ≤ε : fst δ ℚOrder.≤ fst ε
    δ≤ε = equivFun (rat≤rat≃ (fst δ) (fst ε))
      (≤ℝ-trans
        (rat (fst δ))
        (absℝ (x - y) + rat (fst δ))
        (rat (fst ε))
        (subst (_≤ℝ (absℝ (x - y) + rat (fst δ)))
          (addIdL (rat (fst δ)))
          (addPres≤R 0ℝ (absℝ (x - y))
            (rat (fst δ)) (absNonnegative (x - y))))
        absDiff+δ≤ε)

    δ/2<ε : fst (δ /2₊) ℚOrder.< fst ε
    δ/2<ε = ℚOrder.isTrans<≤
      (fst (δ /2₊)) (fst δ) (fst ε)
      (/2₊<id δ) δ≤ε

    ρ : ℚ₊
    ρ = [ ε -₊ (δ /2₊) ]⟨ δ/2<ε ⟩

    ρ<ε : fst ρ ℚOrder.< fst ε
    ρ<ε = subst (fst ρ ℚOrder.<_)
      (minusPlus₊ ε (δ /2₊)) (<₊SumLeft ρ (δ /2₊))

    halfδ≤δ : fst (δ /2₊) ℚOrder.≤ fst δ
    halfδ≤δ = ℚOrder.<Weaken≤ _ _ (/2₊<id δ)

    absDiff+halfδ≤ε :
      absℝ (x - y) + rat (fst (δ /2₊)) ≤ℝ rat (fst ε)
    absDiff+halfδ≤ε = ≤ℝ-trans
      (absℝ (x - y) + rat (fst (δ /2₊)))
      (absℝ (x - y) + rat (fst δ))
      (rat (fst ε))
      (addPres≤L
        (rat (fst (δ /2₊))) (rat (fst δ)) (absℝ (x - y))
        (invEq (rat≤rat≃ (fst (δ /2₊)) (fst δ)) halfδ≤δ))
      absDiff+δ≤ε

    ρ+halfδPath :
      rat (fst ρ) + rat (fst (δ /2₊)) ≡ rat (fst ε)
    ρ+halfδPath =
      rat+rat (fst ρ) (fst (δ /2₊))
      ∙ cong rat (minusPlus₊ ε (δ /2₊))

    absDiff≤ρ : absℝ (x - y) ≤ℝ rat (fst ρ)
    absDiff≤ρ = addReflects≤R
      (absℝ (x - y)) (rat (fst ρ)) (rat (fst (δ /2₊)))
      (subst
        ((absℝ (x - y) + rat (fst (δ /2₊))) ≤ℝ_)
        (sym ρ+halfδPath) absDiff+halfδ≤ε)

closeness≃absDifference< : ∀ x y ε →
  (x ∼[ ε ] y) ≃ (absℝ (x - y) <ℝ rat (fst ε))
closeness≃absDifference< x y ε = propBiimpl→Equiv
  (Pℝ.isProp≈ x y ε)
  (isProp<ℝ (absℝ (x - y)) (rat (fst ε)))
  (closeness→absDifference< x y ε)
  (absDifference<→closeness x y ε)
