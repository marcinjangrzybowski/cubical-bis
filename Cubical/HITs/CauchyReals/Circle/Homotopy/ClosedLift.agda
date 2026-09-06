module Cubical.HITs.CauchyReals.Circle.Homotopy.ClosedLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Homotopy.RealPaths
open import Cubical.HITs.CauchyReals.Circle.Homotopy.IntervalLift
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Tactics.CommRingSolver.OrderedReflection
open CategoryStructures using (_∘UC_; idᵘᶜ)

module ClosedLifting (f : CirclePath) (period : ∀ t → fst f (t +ᵣ 1) ≡ fst f t)
  (lifted : IntervalLift f 0 1) (end : fst (IntervalLift.path lifted) 1 ≡ 0) where

  private
    g : RealPath
    g = IntervalLift.path lifted
    B : ℝ₊
    B = IntervalLift.bound lifted
    g-bound : ∀ t → absᵣ (fst g t) ≤ᵣ fst B
    g-bound = IntervalLift.bounded lifted
    before : ∀ t → t ≤ᵣ 0 → fst g t ≡ 0
    before = IntervalLift.lower lifted
    after : ∀ t → 1 ≤ᵣ t → fst g t ≡ 0
    after t lower = IntervalLift.upper lifted t lower ∙ end

  opaque
    wrapped : RealPath
    wrapped = addRealUC (addRealUC (g ∘UC addRealUC idᵘᶜ (constantUC 1)) g)
      (g ∘UC subRealUC idᵘᶜ (constantUC 1))

    wrapped-β : ∀ t → fst wrapped t ≡ (fst g (t +ᵣ 1) +ᵣ fst g t) +ᵣ fst g (t -ᵣ 1)
    wrapped-β t = refl

  wrapped-bound : ℝ₊
  wrapped-bound = (B ₊+ᵣ B) ₊+ᵣ B

  wrapped-bounded : ∀ t → absᵣ (fst wrapped t) ≤ᵣ fst wrapped-bound
  wrapped-bounded t = isTrans≡≤ᵣ _ _ _ (cong absᵣ (wrapped-β t))
    (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
      (≤ᵣMonotone+ᵣ _ _ _ _
        (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
          (≤ᵣMonotone+ᵣ _ _ _ _ (g-bound (t +ᵣ 1)) (g-bound t)))
        (g-bound (t -ᵣ 1))))

  -- Only this overlap periodicity is needed for descent to the circle.
  wrapped-periodic : ∀ t → -1 ≤ᵣ t → t ≤ᵣ 1 → fst wrapped (t +ᵣ 1) ≡ fst wrapped t
  wrapped-periodic t lower upper = wrapped-β (t +ᵣ 1)
    ∙ cong₂ _+ᵣ_
      (cong (_+ᵣ fst g (t +ᵣ 1)) (after ((t +ᵣ 1) +ᵣ 1) future)
        ∙ +IdL (fst g (t +ᵣ 1)))
      (cong (fst g) ℝ!)
    ∙ sym (+IdR (fst g (t +ᵣ 1) +ᵣ fst g t))
    ∙ cong ((fst g (t +ᵣ 1) +ᵣ fst g t) +ᵣ_) (sym (before (t -ᵣ 1) past))
    ∙ sym (wrapped-β t)
    where
    future : 1 ≤ᵣ (t +ᵣ 1) +ᵣ 1
    future = subst2 _≤ᵣ_ ℝ! ℝ! (≤ᵣ-+o -1 t 2 lower)
    past : t -ᵣ 1 ≤ᵣ 0
    past = isTrans≤≡ᵣ _ _ _ (≤ᵣ-+o t 1 (-ᵣ 1) upper) (+-ᵣ 1)

  private
    rational-value : ∀ q → fst wrapped (rat q) ≡
      (fst g (rat (q ℚ.+ 1)) +ᵣ fst g (rat q)) +ᵣ fst g (rat (q ℚ.- 1))
    rational-value q = wrapped-β (rat q)
      ∙ cong₂ _+ᵣ_ (cong (_+ᵣ fst g (rat q)) (cong (fst g) (+ᵣ-rat q 1)))
        (cong (fst g) (-ᵣ-rat₂ q 1))

    before-rat : ∀ q → q ℚ.≤ 0 → fst g (rat q) ≡ 0
    before-rat q q≤0 = before (rat q) (≤ℚ→≤ᵣ q 0 q≤0)
    after-rat : ∀ q → 1 ℚ.≤ q → fst g (rat q) ≡ 0
    after-rat q q≥1 = after (rat q) (≤ℚ→≤ᵣ 1 q q≥1)

    left-value : ∀ q → q ℚ.≤ 0 → fst wrapped (rat q) ≡ fst g (rat (q ℚ.+ 1))
    left-value q q≤0 = rational-value q
      ∙ cong₂ _+ᵣ_ (cong (fst g (rat (q ℚ.+ 1)) +ᵣ_) (before-rat q q≤0))
        (before-rat (q ℚ.- 1) <≤ℚ![ q≤0 ])
      ∙ +IdR _ ∙ +IdR _

    middle-value : ∀ q → 0 ℚ.≤ q → q ℚ.≤ 1 → fst wrapped (rat q) ≡ fst g (rat q)
    middle-value q 0≤q q≤1 = rational-value q
      ∙ cong₂ _+ᵣ_ (cong (_+ᵣ fst g (rat q)) (after-rat (q ℚ.+ 1) <≤ℚ![ 0≤q ]))
        (before-rat (q ℚ.- 1) <≤ℚ![ q≤1 ])
      ∙ +IdR _ ∙ +IdL _

    right-value : ∀ q → 1 ℚ.≤ q → fst wrapped (rat q) ≡ fst g (rat (q ℚ.- 1))
    right-value q 1≤q = rational-value q
      ∙ cong (λ z → z +ᵣ fst g (rat (q ℚ.- 1)))
        (cong₂ _+ᵣ_ (after-rat (q ℚ.+ 1) <≤ℚ![ 1≤q ]) (after-rat q 1≤q) ∙ +ᵣ-rat 0 0)
      ∙ +IdL _

    covers-rat : ∀ q → 0 ℚ.≤ q → q ℚ.≤ 1 →
      fst f 0 ℝS¹.+ cover (fst g (rat q)) ≡ fst f (rat q)
    covers-rat q 0≤q q≤1 = IntervalLift.covers lifted (rat q) ∙ cong (fst f)
      (sym (∈ℚintervalℙ→clampᵣ≡ 0 1 (rat q) (≤ℚ→≤ᵣ 0 q 0≤q , ≤ℚ→≤ᵣ q 1 q≤1)))

    projected : CirclePath
    projected = addDistCircleUC (constantUC (fst f 0)) (coverUC ∘UC wrapped)

    covers-rational : ∀ q → -1 ℚ.≤ q → q ℚ.≤ 2 → fst projected (rat q) ≡ fst f (rat q)
    covers-rational q low high = PT.rec (isSetDistCircle _ _) cases (ℚ.isTotal≤ q 0)
      where
      cases : (q ℚ.≤ 0) ⊎ (0 ℚ.≤ q) → fst projected (rat q) ≡ fst f (rat q)
      cases (inl q≤0) = cong (λ z → fst f 0 ℝS¹.+ cover z) (left-value q q≤0)
        ∙ covers-rat (q ℚ.+ 1)
          (subst (ℚ._≤ (q ℚ.+ 1)) ℚ! (ℚ.≤-+o -1 q 1 low))
          (subst ((q ℚ.+ 1) ℚ.≤_) ℚ! (ℚ.≤-+o q 0 1 q≤0))
        ∙ cong (fst f) (sym (+ᵣ-rat q 1)) ∙ period (rat q)
      cases (inr 0≤q) = PT.rec (isSetDistCircle _ _)
        (λ { (inl q≤1) → cong (λ z → fst f 0 ℝS¹.+ cover z) (middle-value q 0≤q q≤1)
               ∙ covers-rat q 0≤q q≤1
           ; (inr 1≤q) → cong (λ z → fst f 0 ℝS¹.+ cover z) (right-value q 1≤q)
               ∙ covers-rat (q ℚ.- 1)
                 (subst (ℚ._≤ (q ℚ.- 1)) ℚ! (ℚ.≤-+o 1 q -1 1≤q))
                 (subst ((q ℚ.- 1) ℚ.≤_) ℚ! (ℚ.≤-+o q 2 -1 high))
               ∙ sym (period (rat (q ℚ.- 1)))
               ∙ cong (fst f) (+ᵣ-rat (q ℚ.- 1) 1 ∙ cong rat ℚ!) }) (ℚ.isTotal≤ q 1)

  wrapped-covers : ∀ t → -1 ≤ᵣ t → t ≤ᵣ 2 →
    fst f 0 ℝS¹.+ cover (fst wrapped t) ≡ fst f t
  wrapped-covers = circlePath-ext-interval -1 2 <≤ℚ! projected f covers-rational
