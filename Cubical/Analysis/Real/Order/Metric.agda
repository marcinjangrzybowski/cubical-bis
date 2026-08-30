module Cubical.Analysis.Real.Order.Metric where

open import Cubical.Foundations.Prelude

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
    ( ℝ; rat; ℝPremetricSpace; _∼[_]_; eqℝ; rat-rat-reflects
    ; rat-dense; sym∼; triangle∼
    )
open import Cubical.Analysis.Real.Algebra.Addition
  using (_+_; add-pres∼₁)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addComm; addIdR; addAssoc)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
  using (_-_; addInvR; addInvL; subSelf)
open import Cubical.Analysis.Real.Algebra.Lattice.Base
  using (maxℝ; max-rat; max-pres∼₁)
open import Cubical.Analysis.Real.Order.Base
  using (_≤ℝ_; isProp≤ℝ)
open import Cubical.Analysis.Real.Order.Addition using (addPres≤R)

open ℚInstance.PositiveRationals
  using
    ( ℚ₊; min₊; min/2₊<L; min/2₊<R
    ; [_-₊_]⟨_⟩; minusPlus₊; _+₊_
    )
open ℚInstance.PositiveRationals.PositiveHalvesℚ using (_/2₊)

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

  addCancelR : ∀ x y → (x + y) + (- y) ≡ x
  addCancelR x y =
    sym (addAssoc x y (- y))
    ∙ cong (x +_) (addInvR y)
    ∙ addIdR x


opaque
  closeZero→upperBound : ∀ z ε →
    z ∼[ ε ] 0ℝ → z ≤ℝ rat (fst ε)
  closeZero→upperBound z ε z∼ε0 =
    PT.rec (isProp≤ℝ z (rat (fst ε))) proveAtSmallerRadius
      (Pℝ.isRounded≈ z 0ℝ ε z∼ε0)
    where
    proveAtSmallerRadius :
      Σ[ κ ∈ ℚ₊ ] (fst κ ℚOrder.< fst ε) × (z ∼[ κ ] 0ℝ) →
      z ≤ℝ rat (fst ε)
    proveAtSmallerRadius (κ , κ<ε , z∼κ0) =
      eqℝ (maxℝ z (rat (fst ε))) (rat (fst ε)) proveCloseness
      where
      proveCloseness : ∀ θ →
        maxℝ z (rat (fst ε)) ∼[ θ ] rat (fst ε)
      proveCloseness θ =
        PT.rec
          (Pℝ.isProp≈ (maxℝ z (rat (fst ε)))
            (rat (fst ε)) θ)
          proveFromApproximation
          (rat-dense z α)
        where
        gap : ℚ₊
        gap = [ ε -₊ κ ]⟨ κ<ε ⟩

        α : ℚ₊
        α = min₊ θ gap /2₊

        α<θ : fst α ℚOrder.< fst θ
        α<θ = min/2₊<L θ gap

        α<gap : fst α ℚOrder.< fst gap
        α<gap = min/2₊<R θ gap

        α+κ<ε : fst (α +₊ κ) ℚOrder.< fst ε
        α+κ<ε =
          subst (fst (α +₊ κ) ℚOrder.<_)
            (minusPlus₊ ε κ)
            (ℚOrder.<-+o (fst α) (fst gap) (fst κ) α<gap)

        proveFromApproximation :
          Σ[ q ∈ ℚ ] rat q ∼[ α ] z →
          maxℝ z (rat (fst ε)) ∼[ θ ] rat (fst ε)
        proveFromApproximation (q , ratq∼αz) =
          Pℝ.isMonotone≈< _ _ α θ α<θ
            (subst
              (maxℝ z (rat (fst ε)) ∼[ α ]_)
              maxRatPath
              (max-pres∼₁ z (rat q) (rat (fst ε)) α
                (sym∼ (rat q) z α ratq∼αz)))
          where
          absqMinusZero<α+κ :
            ℚOrdered.abs (q ℚ.- 0) ℚOrder.<
              fst (α +₊ κ)
          absqMinusZero<α+κ =
            rat-rat-reflects q 0
              (α +₊ κ)
              (triangle∼ (rat q) z 0ℝ α κ ratq∼αz z∼κ0)

          q≤absqMinusZero : q ℚOrder.≤ ℚOrdered.abs (q ℚ.- 0)
          q≤absqMinusZero =
            subst (λ u → u ℚOrder.≤ ℚOrdered.abs (q ℚ.- 0))
              (rationalSubZero q)
              (ℚOrdered.≤abs (q ℚ.- 0))

          q<ε : q ℚOrder.< fst ε
          q<ε = ℚOrder.isTrans≤< q (ℚOrdered.abs (q ℚ.- 0)) (fst ε)
            q≤absqMinusZero
            (ℚOrder.isTrans<
              (ℚOrdered.abs (q ℚ.- 0))
              (fst (α +₊ κ))
              (fst ε)
              absqMinusZero<α+κ α+κ<ε)

          maxRatPath :
            maxℝ (rat q) (rat (fst ε)) ≡ rat (fst ε)
          maxRatPath =
            max-rat q (fst ε)
            ∙ cong rat
                (ℚOrder.≤→max q (fst ε)
                  (ℚOrder.<Weaken≤ q (fst ε) q<ε))

  close→upperBound : ∀ x y ε →
    x ∼[ ε ] y → x ≤ℝ y + rat (fst ε)
  close→upperBound x y ε x∼εy =
    subst2 _≤ℝ_
      (subAddCancel x y)
      (addComm (rat (fst ε)) y)
      (addPres≤R (x - y) (rat (fst ε)) y
        (closeZero→upperBound (x - y) ε
          (subst ((x - y) ∼[ ε ]_) (subSelf y)
            (add-pres∼₁ x y (- y) ε x∼εy))))

  close→lowerBound : ∀ x y ε →
    x ∼[ ε ] y → y - rat (fst ε) ≤ℝ x
  close→lowerBound x y ε x∼εy =
    subst ((y - rat (fst ε)) ≤ℝ_)
      (addCancelR x (rat (fst ε)))
      (addPres≤R y (x + rat (fst ε)) (- rat (fst ε))
        (close→upperBound y x ε (sym∼ x y ε x∼εy)))
