module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.JointLoops where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (Interval; 𝕀; 𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real using (constantUC)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Cubes
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Product

-- Joint regularity is a predicate on EXISTING nested loops. It is not
-- an assumed exponential law or a new kind of homotopy representative.
module JointEvaluation (X : PointedPremetricSpace ℓ-zero ℓ-zero) where
  private
    M = fst X
    x = snd X
    module PM = PremetricStr (snd M)
    module B = BasedCubes M x

  Space : (n : ℕ) → PremetricSpace (loopLevel n ℓ-zero ℓ-zero) ℓ-zero
  Space n = fst (realΩ^ n X)

  base : (n : ℕ) → fst (Space n)
  base n = snd (realΩ^ n X)

  evaluate : (n : ℕ) → fst (Space n) → RealCube n → fst M
  evaluate zero p v = p
  evaluate (suc zero) p t = fst (fst p) t
  evaluate (suc (suc n)) p (t , v) = evaluate (suc n) (fst (fst p) t) v

  evaluate-base : (n : ℕ) (v : RealCube n) → evaluate n (base n) v ≡ x
  evaluate-base zero v = refl
  evaluate-base (suc zero) v = refl
  evaluate-base (suc (suc n)) (t , v) = evaluate-base (suc n) v

  evaluate-boundary : (n : ℕ) (p : fst (Space n)) (v : RealCube n) →
    OnBoundary n v → evaluate n p v ≡ x
  evaluate-boundary zero p v ()
  evaluate-boundary (suc zero) p t = PT.rec (PM.isSetM _ _)
    (λ where
      (inl at0) → cong (fst (fst p)) at0 ∙ fst (snd p)
      (inr at1) → cong (fst (fst p)) at1 ∙ snd (snd p))
  evaluate-boundary (suc (suc n)) p (t , v) = PT.rec (PM.isSetM _ _)
    (λ where
      (inl at0) → cong (λ t → evaluate (suc n) (fst (fst p) t) v) at0 ∙
        cong (λ q → evaluate (suc n) q v) (fst (snd p)) ∙ evaluate-base (suc n) v
      (inr (inl at1)) → cong (λ t → evaluate (suc n) (fst (fst p) t) v) at1 ∙
        cong (λ q → evaluate (suc n) q v) (snd (snd p)) ∙ evaluate-base (suc n) v
      (inr (inr boundary)) → evaluate-boundary (suc n) (fst (fst p) t) v boundary)

  Joint : (n : ℕ) → fst (Space n) → Type
  Joint n p = isUniformlyContinuous (snd (CubeSpace n)) (evaluate n p) (snd M)

  joint-prop : (n : ℕ) (p : fst (Space n)) → isProp (Joint n p)
  joint-prop n p = squash₁

  asBasedCube : (n : ℕ) (p : fst (Space n)) → Joint n p → B.BasedCube n
  asBasedCube n p joint = (evaluate n p , joint) , evaluate-boundary n p

  joint-zero : (p : fst (Space zero)) → Joint zero p
  joint-zero p = snd (constantUC p)

  joint-one : (p : fst (Space (suc zero))) → Joint (suc zero) p
  joint-one p = snd (fst p)

  -- Account for the zero-cube convention when a construction supplies
  -- a jointly UC outer-time/lower-cube family.
  joint-successor : (n : ℕ) (p : fst (Space (suc n))) →
    isUniformlyContinuous (snd (PremetricProduct Interval (CubeSpace n)))
      (λ (t , v) → evaluate n (fst (fst p) t) v) (snd M) → Joint (suc n) p
  joint-successor zero p family = joint-one p
  joint-successor (suc n) p family = family

  joint-base : (n : ℕ) → Joint n (base n)
  joint-base n = subst (λ f → isUniformlyContinuous (snd (CubeSpace n)) f (snd M))
    (sym (funExt (evaluate-base n))) (snd (constantUC x))

  evaluate-injective : (n : ℕ) (p q : fst (Space n)) →
    ((v : RealCube n) → evaluate n p v ≡ evaluate n q v) → p ≡ q
  evaluate-injective zero p q same = same tt
  evaluate-injective (suc zero) p q same = RealLoops.path-ext M x same
  evaluate-injective (suc (suc n)) p q same = RealLoops.path-ext (Space (suc n)) (base (suc n))
    (λ t → evaluate-injective (suc n) (fst (fst p) t) (fst (fst q) t) (λ v → same (t , v)))

  evaluate-close : (n : ℕ) (p q : fst (Space n)) (ε : ℚ₊) →
    PremetricStr._≈[_]_ (snd (Space n)) p ε q →
    (v : RealCube n) → PM._≈[_]_ (evaluate n p v) ε (evaluate n q v)
  evaluate-close zero p q ε close v = close
  evaluate-close (suc zero) p q ε close t =
    ≈→→pointwise 𝕀 M (fst (fst p)) (fst (fst q)) ε close t
  evaluate-close (suc (suc n)) p q ε close (t , v) =
    evaluate-close (suc n) _ _ ε
      (≈→→pointwise 𝕀 (Space (suc n)) (fst (fst p)) (fst (fst q)) ε close t) v
