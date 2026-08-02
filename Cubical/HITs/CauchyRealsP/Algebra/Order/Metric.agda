module Cubical.HITs.CauchyRealsP.Algebra.Order.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue

open import Cubical.Relation.Premetric.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing
  module ℝP = PremetricStr (snd ℝPremetricSpace)

opaque
  unfolding _≤ℝ_

  closeZero→upperBound : ∀ z ε →
    z ∼[ ε ] 0 → z ≤ℝ rat (fst ε)
  closeZero→upperBound z ε z∼ε0 =
    PT.rec (isProp≤ℝ z (rat (fst ε))) proveAtSmallerRadius
      (rounded∼ z 0 ε z∼ε0)
    where
    proveAtSmallerRadius :
      Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) × z ∼[ κ ] 0 →
      z ≤ℝ rat (fst ε)
    proveAtSmallerRadius (κ , κ<ε , z∼κ0) =
      eqℝ (maxℝ z (rat (fst ε))) (rat (fst ε)) proveCloseness
      where
      proveCloseness : ∀ θ →
        maxℝ z (rat (fst ε)) ∼[ θ ] rat (fst ε)
      proveCloseness θ =
        PT.rec
          (isProp∼
            (maxℝ z (rat (fst ε))) θ (rat (fst ε)))
          proveFromApproximation
          (∃ratApprox z α)
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
          Σ[ q ∈ ℚ ] rat q ∼[ α ] z →
          maxℝ z (rat (fst ε)) ∼[ θ ] rat (fst ε)
        proveFromApproximation (q , ratq∼αz) =
          ℝP.isMonotone≈< _ _ α θ α<θ
            (subst
              (maxℝ z (rat (fst ε)) ∼[ α ]_)
              maxRatPath
              (maxPres∼₁ z (rat q) (rat (fst ε)) α
                (sym∼ (rat q) z α ratq∼αz)))
          where
          absq<α+κ : abs q ℚ.< fst (α +₊ κ)
          absq<α+κ =
            subst2 ℚ._<_
              (cong {x = q ℚ.- 0} {y = q} abs ℚ!)
              refl
              (rat-rat-toAbs q 0 (α +₊ κ)
                (triangle∼ (rat q) z 0 α κ ratq∼αz z∼κ0))

          q<ε : q ℚ.< fst ε
          q<ε =
            ℚ.isTrans≤<
              q (abs q) (fst ε)
              (ℚOrder.≤abs q)
              (ℚ.isTrans<
                (abs q) (fst (α +₊ κ)) (fst ε)
                absq<α+κ α+κ<ε)

          maxRatPath :
            maxℝ (rat q) (rat (fst ε)) ≡ rat (fst ε)
          maxRatPath =
            max-rat q (fst ε)
            ∙ cong rat
                (ℚ.≤→max q (fst ε)
                  (ℚ.<Weaken≤ q (fst ε) q<ε))

closeZero→lowerBound : ∀ z ε →
  z ∼[ ε ] 0 → rat (ℚ.- fst ε) ≤ℝ z
closeZero→lowerBound z ε z∼ε0 =
  subst2 _≤ℝ_
    (neg-rat (fst ε))
    (negInvol z)
    (≤ℝ-neg (- z) (rat (fst ε))
      (closeZero→upperBound (- z) ε
        (subst ((- z) ∼[ ε ]_) negZero
          (negPres∼ z 0 ε z∼ε0))))

close→upperBound : ∀ x y ε →
  x ∼[ ε ] y → x ≤ℝ y + rat (fst ε)
close→upperBound x y ε x∼εy =
  subst2 _≤ℝ_
    (subAddCancel x y)
    (addComm (rat (fst ε)) y)
    (≤ℝ-addR (x - y) (rat (fst ε)) y
      (closeZero→upperBound (x - y) ε
        (subst ((x - y) ∼[ ε ]_) (subSelf y)
          (addPres∼₁ x y (- y) ε x∼εy))))

close→lowerBound : ∀ x y ε →
  x ∼[ ε ] y → y - rat (fst ε) ≤ℝ x
close→lowerBound x y ε x∼εy =
  subst2 _≤ℝ_
    refl
    (addSubCancel x (rat (fst ε)))
    (≤ℝ-addR y (x + rat (fst ε)) (- rat (fst ε))
      (close→upperBound y x ε
        (sym∼ x y ε x∼εy)))

closeness→absDifference< : ∀ x y ε →
  x ∼[ ε ] y → absℝ (x - y) <ℝ rat (fst ε)
closeness→absDifference< x y ε x∼εy =
  PT.rec (isProp<ℝ (absℝ (x - y)) (rat (fst ε)))
    proveAtSmallerRadius
    (rounded∼ x y ε x∼εy)
  where
  proveAtSmallerRadius :
    Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) × x ∼[ κ ] y →
    absℝ (x - y) <ℝ rat (fst ε)
  proveAtSmallerRadius (κ , κ<ε , x∼κy) =
    ≤<ℝ-trans
      (absℝ (x - y)) (rat (fst κ)) (rat (fst ε))
      (closeZero→upperBound (absℝ (x - y)) κ
        (subst (absℝ (x - y) ∼[ κ ]_) absZero
          (absPres∼ (x - y) 0 κ
            (subst ((x - y) ∼[ κ ]_) (subSelf y)
              (addPres∼₁ x y (- y) κ x∼κy)))))
      (<ℚ→<ℝ (fst κ) (fst ε) κ<ε)

absBound→closeZeroAbove : ∀ z ρ ε →
  ρ <₊ ε → absℝ z ≤ℝ rat (fst ρ) → z ∼[ ε ] 0
absBound→closeZeroAbove z ρ ε ρ<ε absz≤ρ =
  PT.rec (isProp∼ z ε 0) proveFromApproximation
    (∃ratApprox z α)
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
    Σ[ q ∈ ℚ ] rat q ∼[ α ] z → z ∼[ ε ] 0
  proveFromApproximation (q , ratq∼αz) =
    ℝP.isMonotone≈< z 0 (α +₊ β) ε α+β<ε
      (triangle∼ z (rat q) 0 α β
        (sym∼ (rat q) z α ratq∼αz)
        (rat-rat-fromAbs q 0 β
          (subst (ℚ._< fst β)
            (sym
              (cong {x = q ℚ.- 0} {y = q} abs ℚ!))
            absq<β)))
    where
    ratAbsq≤absz+α :
      rat (abs q) ≤ℝ absℝ z + rat (fst α)
    ratAbsq≤absz+α =
      subst (_≤ℝ (absℝ z + rat (fst α)))
        (abs-rat q)
        (close→upperBound
          (absℝ (rat q)) (absℝ z) α
          (absPres∼ (rat q) z α ratq∼αz))

    ratAbsq≤ρ+α :
      rat (abs q) ≤ℝ rat (fst ρ ℚ.+ fst α)
    ratAbsq≤ρ+α =
      ≤ℝ-trans
        (rat (abs q))
        (absℝ z + rat (fst α))
        (rat (fst ρ ℚ.+ fst α))
        ratAbsq≤absz+α
        (subst
          ((absℝ z + rat (fst α)) ≤ℝ_)
          (rat+rat (fst ρ) (fst α))
          (≤ℝ-add
            (absℝ z) (rat (fst ρ))
            (rat (fst α)) (rat (fst α))
            absz≤ρ (≤ℝ-refl (rat (fst α)))))

    absq≤ρ+α : abs q ℚ.≤ fst ρ ℚ.+ fst α
    absq≤ρ+α =
      ≤ℝ→≤ℚ (abs q) (fst ρ ℚ.+ fst α) ratAbsq≤ρ+α

    absq<β : abs q ℚ.< fst β
    absq<β =
      ℚ.isTrans≤<
        (abs q) (fst ρ ℚ.+ fst α) (fst β)
        absq≤ρ+α
        (subst2 ℚ._<_
          (ℚ.+Comm (fst α) (fst ρ))
          (ℚ.+Comm (fst (α +₊ α)) (fst ρ))
          (ℚ.<-+o
            (fst α) (fst (α +₊ α)) (fst ρ)
            (<₊SumLeft α α)))

absDifference<→closeness : ∀ x y ε →
  absℝ (x - y) <ℝ rat (fst ε) → x ∼[ ε ] y
absDifference<→closeness x y ε =
  PT.rec (isProp∼ x ε y) proveFromGap
  where
  proveFromGap :
    PositiveGap (absℝ (x - y)) (rat (fst ε)) →
    x ∼[ ε ] y
  proveFromGap w =
    subst2 (_∼[ ε ]_)
      (subAddCancel x y)
      (addIdL y)
      (addPres∼₁ (x - y) 0 y ε
        (absBound→closeZeroAbove
          (x - y) ρ ε ρ<ε absDiff≤ρ))
    where
    δ : ℚ₊
    δ = width w

    absDiff+δ≤ε :
      absℝ (x - y) + rat (fst δ) ≤ℝ rat (fst ε)
    absDiff+δ≤ε =
      gapBoundElim
        (absℝ (x - y)) (rat (fst ε)) δ (bound w)

    δ≤ε : fst δ ℚ.≤ fst ε
    δ≤ε =
      ≤ℝ→≤ℚ (fst δ) (fst ε)
        (≤ℝ-trans
          (rat (fst δ))
          (absℝ (x - y) + rat (fst δ))
          (rat (fst ε))
          (subst
            (_≤ℝ (absℝ (x - y) + rat (fst δ)))
            (addIdL (rat (fst δ)))
            (≤ℝ-add
              0 (absℝ (x - y))
              (rat (fst δ)) (rat (fst δ))
              (absNonnegative (x - y))
              (≤ℝ-refl (rat (fst δ)))))
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
    halfδ≤δ = ℚ.<Weaken≤ _ _ (/2₊<id δ)

    absDiff+halfδ≤ε :
      absℝ (x - y) + rat (fst (δ /2₊)) ≤ℝ rat (fst ε)
    absDiff+halfδ≤ε =
      ≤ℝ-trans
        (absℝ (x - y) + rat (fst (δ /2₊)))
        (absℝ (x - y) + rat (fst δ))
        (rat (fst ε))
        (≤ℝ-addL
          (rat (fst (δ /2₊))) (rat (fst δ))
          (absℝ (x - y))
          (≤ℚ→≤ℝ (fst (δ /2₊)) (fst δ) halfδ≤δ))
        absDiff+δ≤ε

    ρ+halfδPath :
      rat (fst ρ) + rat (fst (δ /2₊)) ≡ rat (fst ε)
    ρ+halfδPath =
      rat+rat (fst ρ) (fst (δ /2₊))
      ∙ cong rat (minusPlus₊ ε (δ /2₊))

    absDiff≤ρ : absℝ (x - y) ≤ℝ rat (fst ρ)
    absDiff≤ρ =
      ≤ℝ-addR-cancel
        (absℝ (x - y)) (rat (fst ρ))
        (rat (fst (δ /2₊)))
        (subst
          ((absℝ (x - y) + rat (fst (δ /2₊))) ≤ℝ_)
          (sym ρ+halfδPath)
          absDiff+halfδ≤ε)

closeness≃absDifference< : ∀ x y ε →
  (x ∼[ ε ] y) ≃ (absℝ (x - y) <ℝ rat (fst ε))
closeness≃absDifference< x y ε =
  propBiimpl→Equiv
    (isProp∼ x ε y)
    (isProp<ℝ (absℝ (x - y)) (rat (fst ε)))
    (closeness→absDifference< x y ε)
    (absDifference<→closeness x y ε)
