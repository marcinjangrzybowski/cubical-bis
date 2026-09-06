module Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Subdivision where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Pasting
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

half fiveSixths : 𝕀
half = rat [ 1 / 2 ] , decℚ≤ᵣ? , decℚ≤ᵣ?
fiveSixths = rat [ 5 / 6 ] , decℚ≤ᵣ? , decℚ≤ᵣ?

private
  affine-lower : ∀ c b → 0 ℚ.≤ c → (t : 𝕀) → rat b ≤ᵣ fst t ·ᵣ rat c +ᵣ rat b
  affine-lower c b positive t = isTrans≡≤ᵣ _ _ _ ℝ!
    (≤ᵣ-+o (0 ·ᵣ rat c) (fst t ·ᵣ rat c) (rat b)
      (≤ᵣ-·o 0 (fst t) c positive (fst (snd t))))

  affine-upper : ∀ c b → 0 ℚ.≤ c → (t : 𝕀) → fst t ·ᵣ rat c +ᵣ rat b ≤ᵣ rat (c ℚ.+ b)
  affine-upper c b positive t = isTrans≤≡ᵣ _ (1 ·ᵣ rat c +ᵣ rat b) _
    (≤ᵣ-+o (fst t ·ᵣ rat c) (1 ·ᵣ rat c) (rat b)
      (≤ᵣ-·o (fst t) 1 c positive (snd (snd t))))
    (cong (_+ᵣ rat b) ℝ! ∙ +ᵣ-rat c b)

  boundedAffine : (c b : ℚ) → 0 ℚ.≤ c → 0 ℚ.≤ b → c ℚ.+ b ℚ.≤ 1 → UC[ Interval , Interval ]
  boundedAffine c b positive lower upper = restrictUC (intervalℙ 0 1) (intervalℙ 0 1)
    (affineUC (rat c) (rat b)) λ t bounds →
      isTrans≤ᵣ 0 (rat b) _ (≤ℚ→≤ᵣ 0 b lower) (affine-lower c b positive (t , bounds)) ,
      isTrans≤ᵣ _ (rat (c ℚ.+ b)) 1 (affine-upper c b positive (t , bounds)) (≤ℚ→≤ᵣ _ 1 upper)

-- Three adjacent clocks covering [0,1]. They cut the composite
-- p * (q * r) inside its two constant waiting intervals.
firstClock middleClock lastClock : UC[ Interval , Interval ]
firstClock = boundedAffine [ 1 / 2 ] 0 <≤ℚ! <≤ℚ! <≤ℚ!
middleClock = boundedAffine [ 1 / 3 ] [ 1 / 2 ] <≤ℚ! <≤ℚ! <≤ℚ!
lastClock = boundedAffine [ 1 / 6 ] [ 5 / 6 ] <≤ℚ! <≤ℚ! <≤ℚ!

first-0 : fst firstClock 𝟘 ≡ 𝟘
first-0 = interval-ext ℝ!
first-1 : fst firstClock 𝟙 ≡ half
first-1 = interval-ext ℝ!
middle-0 : fst middleClock 𝟘 ≡ half
middle-0 = interval-ext ℝ!
middle-1 : fst middleClock 𝟙 ≡ fiveSixths
middle-1 = interval-ext ℝ!
last-0 : fst lastClock 𝟘 ≡ fiveSixths
last-0 = interval-ext ℝ!
last-1 : fst lastClock 𝟙 ≡ 𝟙
last-1 = interval-ext ℝ!

first≤half : ∀ t → fst (fst firstClock t) ≤ᵣ fst half
first≤half t = isTrans≤≡ᵣ _ _ _ (affine-upper [ 1 / 2 ] 0 <≤ℚ! t) (cong rat ℚ!)
half≤middle : ∀ t → fst half ≤ᵣ fst (fst middleClock t)
half≤middle = affine-lower [ 1 / 3 ] [ 1 / 2 ] <≤ℚ!
middle≤fiveSixths : ∀ t → fst (fst middleClock t) ≤ᵣ fst fiveSixths
middle≤fiveSixths t = isTrans≤≡ᵣ _ _ _ (affine-upper [ 1 / 3 ] [ 1 / 2 ] <≤ℚ! t) (cong rat ℚ!)
fiveSixths≤last : ∀ t → fst fiveSixths ≤ᵣ fst (fst lastClock t)
fiveSixths≤last = affine-lower [ 1 / 6 ] [ 5 / 6 ] <≤ℚ!

early-half : fst early half ≡ 𝟙
early-half = clip-above _ (isTrans≤≡ᵣ 1 (rat [ 3 / 2 ]) _ decℚ≤ᵣ? ℝ!)
late-half : fst late half ≡ 𝟘
late-half = clip-below _ (isTrans≡≤ᵣ _ (rat (ℚ.- [ 1 / 2 ])) 0 ℝ! decℚ≤ᵣ?)
late-fiveSixths : fst late fiveSixths ≡ half
late-fiveSixths = cong clip ℝ! ∙ clip-fixes half

late-monotone : ∀ s t → fst s ≤ᵣ fst t → fst (fst late s) ≤ᵣ fst (fst late t)
late-monotone s t order = clamp-monotone-≤ᵣ 0 1 _ _
  (≤ᵣ-+o (fst s ·ᵣ 3) (fst t ·ᵣ 3) (-ᵣ 2) (≤ᵣ-·o (fst s) (fst t) 3 <≤ℚ! order))

middle-late≤half : ∀ t → fst (fst late (fst middleClock t)) ≤ᵣ fst half
middle-late≤half t = subst (fst (fst late (fst middleClock t)) ≤ᵣ_) (cong fst late-fiveSixths)
  (late-monotone (fst middleClock t) fiveSixths (middle≤fiveSixths t))
half≤last-late : ∀ t → fst half ≤ᵣ fst (fst late (fst lastClock t))
half≤last-late t = subst (_≤ᵣ fst (fst late (fst lastClock t))) (cong fst late-fiveSixths)
  (late-monotone fiveSixths (fst lastClock t) (fiveSixths≤last t))

left-of-half : (t : 𝕀) → fst t ≤ᵣ fst half → fst t ·ᵣ 3 <ᵣ 2
left-of-half t upper = isTrans≤<ᵣ _ (fst half ·ᵣ 3) _
  (≤ᵣ-·o (fst t) (fst half) 3 <≤ℚ! upper)
  (isTrans≡<ᵣ _ (rat [ 3 / 2 ]) 2 ℝ! decℚ<ᵣ?)
right-of-half : (t : 𝕀) → fst half ≤ᵣ fst t → 1 <ᵣ fst t ·ᵣ 3
right-of-half t lower = isTrans<≤ᵣ _ (fst half ·ᵣ 3) _
  (isTrans<≡ᵣ 1 (rat [ 3 / 2 ]) _ decℚ<ᵣ? ℝ!)
  (≤ᵣ-·o (fst half) (fst t) 3 <≤ℚ! lower)

half≤last : ∀ t → fst half ≤ᵣ fst (fst lastClock t)
half≤last t = isTrans≤ᵣ _ (fst fiveSixths) _ decℚ≤ᵣ? (fiveSixths≤last t)
