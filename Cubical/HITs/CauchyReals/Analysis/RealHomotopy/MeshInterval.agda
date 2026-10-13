module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.MeshInterval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq; equivFun)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Uniform using (clampᵣ∼)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.InterpolationClocks
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.RationalMesh
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

private
  width-form : (a : ℚ) → (a ℚ.+ [ 1 / 2 ]) ℚ.- start ≡ a ℚ.+ 2
  width-form a = ℚ!
  finish-form : (a : ℚ) → (a ℚ.+ 2) ℚ.+ start ≡ a ℚ.+ [ 1 / 2 ]
  finish-form a = ℚ!
  affine-expand : (a b c z : ℝ) → (z ·ᵣ a +ᵣ b) ·ᵣ c +ᵣ (-ᵣ b) ·ᵣ c ≡ z ·ᵣ (a ·ᵣ c)
  affine-expand a b c z = ℝ!
  times-one : (z : ℝ) → z ·ᵣ 1 ≡ z
  times-one z = ℝ!
  affine-difference : (a b z w : ℝ) →
    (z ·ᵣ a +ᵣ b) -ᵣ (w ·ᵣ a +ᵣ b) ≡ (z -ᵣ w) ·ᵣ a
  affine-difference a b z w = ℝ!

unscaleUC : ℕ → UC[ ℝPremetricSpace , Interval ]
fst (unscaleUC k) z = clip (z ·ᵣ rat (fst (inverseWidth k)) +ᵣ
  ((-ᵣ rat start) ·ᵣ rat (fst (inverseWidth k))))
snd (unscaleUC k) = snd (clipUC ∘UC affineUC (rat (fst (inverseWidth k)))
  ((-ᵣ rat start) ·ᵣ rat (fst (inverseWidth k))))

unscale-stretch : (k : ℕ) (t : 𝕀) → fst (unscaleUC k) (fst (stretchUC k) t) ≡ t
unscale-stretch k t = cong clip
  (cong (λ a → (fst t ·ᵣ rat a +ᵣ rat start) ·ᵣ inv +ᵣ (-ᵣ rat start) ·ᵣ inv)
    (width-form (cut k) ∙ sym (width-β k)) ∙
   affine-expand (rat (fst (width k))) (rat start) inv (fst t) ∙
   cong (fst t ·ᵣ_) (sym (rat·ᵣrat (fst (width k)) (fst (inverseWidth k))) ∙
     cong rat (cong (fst (width k) ℚ.·_) (cong fst (inverseWidth-β k)) ∙ ℚ.x·invℚ₊[x] (width k))) ∙ times-one (fst t)) ∙ clip-fixes t
  where
  inv = rat (fst (inverseWidth k))

node : ℕ → ℚ
node j = cut j ℚ.+ start

sample : ℕ → ℕ → 𝕀
sample k j = fst (unscaleUC k) (rat (node j))

sample-start : (k : ℕ) → sample k zero ≡ 𝟘
sample-start k = interval-ext
  (cong (λ z → fst (fst (unscaleUC k) z)) (cong rat (ℚ.+IdL start) ∙ sym (stretch-start k)) ∙
   cong fst (unscale-stretch k 𝟘))

sample-finish : (k : ℕ) → sample k (suc k) ≡ 𝟙
sample-finish k = interval-ext (cong (λ z → fst (fst (unscaleUC k) z))
  (cong rat (finish-form (cut k)) ∙ sym (stretch-finish k)) ∙ cong fst (unscale-stretch k 𝟙))

private
  affine-close : (a : ℚ₊) (b z w : ℝ) (ε : ℚ₊) → z ≈ℝ[ ε ] w →
    (z ·ᵣ rat (fst a) +ᵣ b) ≈ℝ[ ε ·₊ a ] (w ·ᵣ rat (fst a) +ᵣ b)
  affine-close a b z w ε close = ∼→≈ℝ _ _ (ε ·₊ a) (invEq (∼≃abs<ε _ _ (ε ·₊ a))
    (isTrans≡<ᵣ _ (absᵣ (z -ᵣ w) ·ᵣ rat (fst a)) _
      (cong absᵣ (affine-difference (rat (fst a)) b z w) ∙ ·absᵣ (z -ᵣ w) (rat (fst a)) ∙
        cong (absᵣ (z -ᵣ w) ·ᵣ_) (absᵣPos (rat (fst a)) (snd (ℚ₊→ℝ₊ a))))
      (isTrans<≡ᵣ _ (rat (fst ε) ·ᵣ rat (fst a)) _
        (<ᵣ-·ᵣo (absᵣ (z -ᵣ w)) (rat (fst ε)) (ℚ₊→ℝ₊ a)
          (equivFun (∼≃abs<ε z w ε) (≈ℝ→∼ z w ε close)))
        (sym (rat·ᵣrat (fst ε) (fst a))))))

-- Keep the complete quantitative lemma available with abstract affine
-- coefficients. Direct specialization to unscaleUC was expensive to
-- check; the remaining finite-window proof should consume this API.
opaque
  clipped-affine-close : (a : ℚ₊) (b z w : ℝ) (ε : ℚ₊) → z ≈ℝ[ ε ] w →
    PremetricStr._≈[_]_ (snd Interval)
      (clip (z ·ᵣ rat (fst a) +ᵣ b)) (ε ·₊ a) (clip (w ·ᵣ rat (fst a) +ᵣ b))
  clipped-affine-close a b z w ε close = ∼→≈ℝ
    (fst (clip (z ·ᵣ rat (fst a) +ᵣ b))) (fst (clip (w ·ᵣ rat (fst a) +ᵣ b))) (ε ·₊ a)
    (clampᵣ∼ {a = 0} {b = 1}
    {u = z ·ᵣ rat (fst a) +ᵣ b} {v = w ·ᵣ rat (fst a) +ᵣ b} {ε = ε ·₊ a}
    (≈ℝ→∼ (z ·ᵣ rat (fst a) +ᵣ b) (w ·ᵣ rat (fst a) +ᵣ b) (ε ·₊ a)
      (affine-close a b z w ε close)))

