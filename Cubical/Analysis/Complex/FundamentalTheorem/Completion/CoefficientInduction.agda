module Cubical.Analysis.Complex.FundamentalTheorem.Completion.CoefficientInduction where

-- Finite native coefficient vectors are generated from Gaussian vectors
-- by native sequential limits. This induction principle does not flatten
-- completed coordinates into chosen rational approximation sequences.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; map; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base using (ℝ; rat; ℝPremetricSpace; lim; SeqWitness; refl∼; lim-isLimitSeq; module S)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients

CoefficientSeqWitness : ∀ n → (ℕ → MonicPolynomial n) → Type₀
CoefficientSeqWitness n ps = PT.∥ PremetricTheory.isCauchySeq (coefficientSpace n) ps ∥₁

SequentiallyClosedCoefficients : ∀ n → (MonicPolynomial n → Type₀) → Type₀
SequentiallyClosedCoefficients n H = ∀ ps → CoefficientSeqWitness n ps → ∀ p →
  PremetricTheory.isLimitSeq (coefficientSpace n) ps p → (∀ k → H (ps k)) → H p

private
  realHead : ∀ {n} (p : MonicPolynomial n) b → NE[ ℝPremetricSpace , coefficientSpace (suc n) ]
  fst (realHead p b) a = (a , b) ∷ p
  IsNonExpanding.pres≈ (snd (realHead p b)) a c ε close zero = close , refl∼ b ε
  IsNonExpanding.pres≈ (snd (realHead p b)) a c ε close (suc i) = coefficientCloseness-refl p ε i

  imagHead : ∀ {n} (p : MonicPolynomial n) a → NE[ ℝPremetricSpace , coefficientSpace (suc n) ]
  fst (imagHead p a) b = (a , b) ∷ p
  IsNonExpanding.pres≈ (snd (imagHead p a)) b d ε close zero = refl∼ a ε , close
  IsNonExpanding.pres≈ (snd (imagHead p a)) b d ε close (suc i) = coefficientCloseness-refl p ε i

  prepend : ∀ n z → NE[ coefficientSpace n , coefficientSpace (suc n) ]
  fst (prepend n z) p = z ∷ p
  IsNonExpanding.pres≈ (snd (prepend n (a , b))) p q ε close zero = refl∼ a ε , refl∼ b ε
  IsNonExpanding.pres≈ (snd (prepend n z)) p q ε close (suc i) = close i

coefficientInduction : ∀ n (H : MonicPolynomial n → Type₀) →
  (∀ p → isProp (H p)) → (∀ qs → H (map gaussianℂ qs)) →
  SequentiallyClosedCoefficients n H → ∀ p → H p
coefficientInduction zero H prop base closed [] = base []
coefficientInduction (suc n) H prop base closed (z ∷ p) =
  coefficientInduction n Tail tail-prop tail-base tail-closed p (re z) (im z)
  where
  Tail : MonicPolynomial n → Type₀
  Tail p = ∀ a b → H ((a , b) ∷ p)

  tail-prop : ∀ p → isProp (Tail p)
  tail-prop p = isPropΠ2 λ a b → prop ((a , b) ∷ p)

  tail-base : ∀ qs → Tail (map gaussianℂ qs)
  tail-base qs = S.Elimℭ̂ₛ-Prop.go realElim
    where
    p₀ : MonicPolynomial n
    p₀ = map gaussianℂ qs

    imagElim : ∀ a → S.Elimℭ̂ₛ-Prop (λ b → H ((rat a , b) ∷ p₀))
    imagElim a .S.Elimℭ̂ₛ-Prop.ιA b = base ((a , b) ∷ qs)
    imagElim a .S.Elimℭ̂ₛ-Prop.limA ys gy IH = closed
      (λ k → (rat a , ys k) ∷ p₀)
      (PT.map (NE→presIsCauchySeq (imagHead p₀ (rat a)) ys) gy)
      ((rat a , lim ys gy) ∷ p₀)
      (NE→seqContinuous (imagHead p₀ (rat a)) ys (lim ys gy) (lim-isLimitSeq ys gy)) IH
    imagElim a .S.Elimℭ̂ₛ-Prop.isPropA b = prop ((rat a , b) ∷ p₀)

    realElim : S.Elimℭ̂ₛ-Prop (λ a → ∀ b → H ((a , b) ∷ p₀))
    realElim .S.Elimℭ̂ₛ-Prop.ιA a = S.Elimℭ̂ₛ-Prop.go (imagElim a)
    realElim .S.Elimℭ̂ₛ-Prop.limA xs gx IH b = closed
      (λ k → (xs k , b) ∷ p₀)
      (PT.map (NE→presIsCauchySeq (realHead p₀ b) xs) gx)
      ((lim xs gx , b) ∷ p₀)
      (NE→seqContinuous (realHead p₀ b) xs (lim xs gx) (lim-isLimitSeq xs gx)) (λ k → IH k b)
    realElim .S.Elimℭ̂ₛ-Prop.isPropA a = isPropΠ λ b → prop ((a , b) ∷ p₀)

  tail-closed : SequentiallyClosedCoefficients n Tail
  tail-closed ps witness p converges IH a b = closed
    (λ k → (a , b) ∷ ps k)
    (PT.map (NE→presIsCauchySeq (prepend n (a , b)) ps) witness)
    ((a , b) ∷ p)
    (NE→seqContinuous (prepend n (a , b)) ps p converges) (λ k → IH k a b)
