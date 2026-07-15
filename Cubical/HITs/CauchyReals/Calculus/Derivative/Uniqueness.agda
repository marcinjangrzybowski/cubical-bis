module Cubical.HITs.CauchyReals.Calculus.Derivative.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

derivativeValueUnique : ∀ (f f' g' : ℝ → ℝ) →
  DerivativeOfℙ ⊤Pred , (λ x _ → f x) is (λ x _ → f' x) →
  DerivativeOfℙ ⊤Pred , (λ x _ → f x) is (λ x _ → g' x) →
  ∀ x → f' x ≡ g' x
derivativeValueUnique f f' g' df dg x =
  eqℝ (f' x) (g' x) λ ε →
    PT.rec2 (isProp∼ _ _ _)
      (compare ε) (df x tt ((ε /2₊) /2₊)) (dg x tt ((ε /2₊) /2₊))
  where
  compare :
    (ε : ℚ₊) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
        absᵣ (derivativeErrorℙ ⊤Pred
          (λ u _ → f u) (λ u _ → f' u) x tt y y∈) ≤ᵣ
        rat (fst ((ε /2₊) /2₊)) ·ᵣ absᵣ (y -ᵣ x)) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
        absᵣ (derivativeErrorℙ ⊤Pred
          (λ u _ → f u) (λ u _ → g' u) x tt y y∈) ≤ᵣ
        rat (fst ((ε /2₊) /2₊)) ·ᵣ absᵣ (y -ᵣ x)) →
    f' x ∼[ ε ] g' x
  compare ε (δ , Df) (δ' , Dg) =
    invEq (∼≃abs<ε (f' x) (g' x) ε)
      (invEq (z<x≃y₊·z<y₊·x
        (rat (fst ε)) (absᵣ (f' x -ᵣ g' x)) h₊)
        multiplied)
    where
    h₊ : ℝ₊
    h₊ = ℚ₊→ℝ₊ (min₊ δ δ')

    h : ℝ
    h = fst h₊

    y : ℝ
    y = x +ᵣ h

    hPos : 0 <ᵣ h
    hPos = snd h₊

    distancePath : absᵣ (y -ᵣ x) ≡ h
    distancePath = cong absᵣ ℝ! ∙ absᵣPos h hPos

    distance≤δ : absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ)
    distance≤δ =
      isTrans≡≤ᵣ _ _ _ distancePath
        (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ')))

    distance≤δ' : absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ')
    distance≤δ' =
      isTrans≡≤ᵣ _ _ _ distancePath
        (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))

    Ef : ℝ
    Ef = derivativeErrorℙ ⊤Pred
      (λ u _ → f u) (λ u _ → f' u) x tt y tt

    Eg : ℝ
    Eg = derivativeErrorℙ ⊤Pred
      (λ u _ → f u) (λ u _ → g' u) x tt y tt

    Ef≤ : absᵣ Ef ≤ᵣ
      rat (fst ((ε /2₊) /2₊)) ·ᵣ absᵣ (y -ᵣ x)
    Ef≤ = Df y tt distance≤δ

    Eg≤ : absᵣ Eg ≤ᵣ
      rat (fst ((ε /2₊) /2₊)) ·ᵣ absᵣ (y -ᵣ x)
    Eg≤ = Dg y tt distance≤δ'

    errorDifference : Eg -ᵣ Ef ≡ (f' x -ᵣ g' x) ·ᵣ h
    errorDifference = ℝ!

    errorDifference≤ : absᵣ (Eg -ᵣ Ef) ≤ᵣ
      rat (fst (ε /2₊)) ·ᵣ absᵣ (y -ᵣ x)
    errorDifference≤ =
      isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _
          (absᵣ-triangle'' Eg Ef)
          (≤ᵣMonotone+ᵣ _ _ _ _ Eg≤ Ef≤))
        (ε/2+ε/2·abs≡ε·abs (ε /2₊) (y -ᵣ x))

    halfProduct<product :
      rat (fst (ε /2₊)) ·ᵣ h <ᵣ rat (fst ε) ·ᵣ h
    halfProduct<product =
      <ᵣ-·ᵣo _ _ h₊ (<ℚ→<ᵣ _ _ (/2₊<id ε))

    multiplied :
      h ·ᵣ absᵣ (f' x -ᵣ g' x) <ᵣ h ·ᵣ rat (fst ε)
    multiplied =
      isTrans≡<ᵣ _ _ _
        (·ᵣComm h (absᵣ (f' x -ᵣ g' x))
         ∙ cong (absᵣ (f' x -ᵣ g' x) ·ᵣ_) (sym (absᵣPos h hPos))
         ∙ sym (·absᵣ (f' x -ᵣ g' x) h)
         ∙ cong absᵣ (sym errorDifference))
        (isTrans≤<ᵣ _ _ _ errorDifference≤
          (isTrans≡<ᵣ _ _ _
            (cong (rat (fst (ε /2₊)) ·ᵣ_) distancePath)
            (isTrans<≡ᵣ _ _ _ halfProduct<product
              (·ᵣComm (rat (fst ε)) h))))
