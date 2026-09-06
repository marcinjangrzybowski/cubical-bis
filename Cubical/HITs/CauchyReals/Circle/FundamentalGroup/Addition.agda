module Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Pasting
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra using (circle-image-injective)
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Base
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.NormalForm
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  sum : Circle → Circle → Circle
  sum a b = fromCartesian (Circle→distCircle a ℝS¹.+ Circle→distCircle b)

  sum-zero : ∀ a → sum a basepoint ≡ a
  sum-zero a = circle-image-injective _ _ (to-fromCartesian _
    ∙ cong (Circle→distCircle a ℝS¹.+_) injCircle0≡circle0 ∙ ℝS¹.+IdR _)
  zero-sum : ∀ a → sum basepoint a ≡ a
  zero-sum a = circle-image-injective _ _ (to-fromCartesian _
    ∙ cong (ℝS¹._+ Circle→distCircle a) injCircle0≡circle0 ∙ ℝS¹.+IdL _)

pointwiseLoop : Loop → Loop → Loop
pointwiseLoop p q = addCircleUC (fst p) (fst q) ,
  (cong₂ sum (fst (snd p)) (fst (snd q)) ∙ sum-zero basepoint) ,
  (cong₂ sum (snd (snd p)) (snd (snd q)) ∙ sum-zero basepoint)

pointwise-homotopy : ∀ {p p' q q' : Loop} → PathHomotopy p p' → PathHomotopy q q' →
  PathHomotopy (pointwiseLoop p q) (pointwiseLoop p' q')
pointwise-homotopy h k = result
  where
  open PathHomotopy
  result : PathHomotopy _ _
  deformation result = addCircleUC (deformation h) (deformation k)
  at-start result t = cong₂ sum (at-start h t) (at-start k t)
  at-end result t = cong₂ sum (at-end h t) (at-end k t)
  fixes-start result s = cong₂ sum (fixes-start h s) (fixes-start k s) ∙ sum-zero basepoint
  fixes-end result s = cong₂ sum (fixes-end h s) (fixes-end k s) ∙ sum-zero basepoint

-- The waiting clocks identify concatenation with pointwise addition,
-- up to a homotopy that keeps both loop endpoints at the basepoint.
concat-pointwise : (p q : Loop) → PathHomotopy (concatPath p q) (pointwiseLoop p q)
concat-pointwise p q = result
  where
  open PathHomotopy
  p' q' : Loop
  p' = reparametrize p early early-0 early-1
  q' = reparametrize q late late-0 late-1

  waiting : PathHomotopy (pointwiseLoop p' q') (pointwiseLoop p q)
  waiting = homotopy-sym {p = pointwiseLoop p q} {q = pointwiseLoop p' q'}
    (pointwise-homotopy {p = p} {p' = p'} {q = q} {q' = q'}
      (reparametrize-homotopy p early early-0 early-1)
      (reparametrize-homotopy q late late-0 late-1))

  expanded : ∀ t → at (concatPath p q) t ≡ at (pointwiseLoop p' q') t
  expanded t = concat-eq p q t _
    (λ upper → sym (cong (sum (at p (fst early t)))
      (cong (at q) (clip-below _ (isTrans≤≡ᵣ _ (2 -ᵣ 2) 0
        (≤ᵣ-+o (fst t ·ᵣ 3) 2 (-ᵣ 2) (<ᵣWeaken≤ᵣ _ _ upper)) ℝ!))
        ∙ fst (snd q)) ∙ sum-zero (at p (fst early t))))
    (λ lower → sym (cong (λ a → sum a (at q (fst late t)))
      (cong (at p) (clip-above _ (<ᵣWeaken≤ᵣ _ _ lower)) ∙ snd (snd p))
      ∙ zero-sum (at q (fst late t))))

  -- Use the pointwise equation only at the boundary. Transporting the
  -- entire homotopy along a path equality expands its continuity proofs.
  result : PathHomotopy (concatPath p q) (pointwiseLoop p q)
  deformation result = deformation waiting
  at-start result t = at-start waiting t ∙ sym (expanded t)
  at-end result t = at-end waiting t
  fixes-start result s = fixes-start waiting s
  fixes-end result s = fixes-end waiting s

pointwise-integerLoop : ∀ k l → pointwiseLoop (integerLoop k) (integerLoop l) ≡ integerLoop (k ℤ.+ l)
pointwise-integerLoop k l = path-ext
  {p = pointwiseLoop (integerLoop k) (integerLoop l)}
  {q = integerLoop (k ℤ.+ l)} λ t → circle-image-injective _ _
  (to-fromCartesian _
    ∙ cong₂ ℝS¹._+_ (sym (cover-β (fst t ·ᵣ integer-real k))) (sym (cover-β (fst t ·ᵣ integer-real l)))
    ∙ sym (cover-add _ _)
    ∙ cong cover (sym (·DistL+ (fst t) (integer-real k) (integer-real l))
      ∙ cong (fst t ·ᵣ_) (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℤ+→ℚ+ k l)))
    ∙ cover-β (fst t ·ᵣ integer-real (k ℤ.+ l)))
