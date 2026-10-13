module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.RationalMesh where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.InterpolationClocks

private
  nat-step : (k : ℕ) → 1 ℚ.+ fromNat (suc k) ≡ fromNat (suc (suc k))
  nat-step k = ℚ.ℤ+→ℚ+ (pos 1) (pos (suc k)) ∙ cong [_/ 1 ] (sym (ℤ.pos+ 1 (suc k)))

  twice-step : (a : ℚ) → (2 ℚ.· a) ℚ.+ 2 ≡ 2 ℚ.· (1 ℚ.+ a)
  twice-step a = ℚ!
  twice-sum : (a : ℚ) → a ℚ.+ a ≡ 2 ℚ.· a
  twice-sum a = ℚ!
  cancel-third : (a : ℚ) → 3 ℚ.· (a ℚ.· [ 1 / 3 ]) ≡ a
  cancel-third a = ℚ!

-- A polygon with k+1 edges spans this normalized real length.
opaque
  width : ℕ → ℚ₊
  width k = (cut k ℚ.+ 2) ,
    ℚ.isTrans<≤ 0 (0 ℚ.+ 2) (cut k ℚ.+ 2) <≤ℚ!
      (ℚ.≤-+o 0 (cut k) 2 (cut-nonnegative k))

opaque
  unfolding width
  width-β : (k : ℕ) → fst (width k) ≡ cut k ℚ.+ 2
  width-β k = refl

  width-doubled : (k : ℕ) → fst (width k) ≡ 2 ℚ.· fromNat (suc k)
  width-doubled zero = ℚ!
  width-doubled (suc k) = cong (ℚ._+ 2) (width-doubled k) ∙
    twice-step (fromNat (suc k)) ∙ cong (2 ℚ.·_) (nat-step k)

opaque
  inverseWidth : ℕ → ℚ₊
  inverseWidth k = (width k) ℚ.⁻¹₊

opaque
  unfolding inverseWidth
  inverseWidth-β : (k : ℕ) → inverseWidth k ≡ (width k) ℚ.⁻¹₊
  inverseWidth-β k = refl

private
  twice-larger : (q : ℚ₊) → fst q ℚ.≤ 2 ℚ.· fst q
  twice-larger q = subst2 ℚ._≤_ (ℚ.+IdR (fst q)) (twice-sum (fst q))
    (ℚ.≤-o+ 0 (fst q) (fst q) (ℚ.<Weaken≤ 0 (fst q) (snd q)))

  inverse-bound : (k : ℕ) → fst (inverseWidth k) ℚ.≤ [ 1 / 1+ k ]
  inverse-bound k = subst (λ a → fst a ℚ.≤ [ 1 / 1+ k ]) (sym (inverseWidth-β k))
    (subst (fst ((width k) ℚ.⁻¹₊) ℚ.≤_) (ℚ.invℚ₊-fromNat k)
    (ℚ.invℚ≤invℚ (width k) (fromNat (suc k))
      (subst (fromNat (suc k) ℚ.≤_) (sym (width-doubled k)) (twice-larger (fromNat (suc k))))))

-- Three normalized units give slack beyond the 5/2 units needed for
-- both endpoints of any interpolation branch.
meshRadius : ℕ → ℚ₊
meshRadius k = 3 ·₊ inverseWidth k

private
  fine-from : (η : ℚ₊) (k : ℕ) → [ 1 / 1+ k ] ℚ.< fst η ℚ.· [ 1 / 3 ] →
    fst (meshRadius k) ℚ.< fst η
  fine-from η k small =
    ℚ.isTrans≤< (fst (meshRadius k)) (3 ℚ.· [ 1 / 1+ k ]) (fst η)
      (ℚ.≤-o· (fst (inverseWidth k)) [ 1 / 1+ k ] 3 <≤ℚ! (inverse-bound k))
      (subst (3 ℚ.· [ 1 / 1+ k ] ℚ.<_) (cancel-third (fst η))
        (ℚ.<-o· [ 1 / 1+ k ] (fst η ℚ.· [ 1 / 3 ]) 3 <≤ℚ! small))

  opaque
    small-denominator : (η : ℚ₊) → Σ[ k ∈ ℕ₊₁ ] [ 1 / k ] ℚ.< fst η
    small-denominator = ℚ.lowerBoundℕ⁻¹

fineMesh : (η : ℚ₊) → Σ[ k ∈ ℕ ] fst (meshRadius k) ℚ.< fst η
fineMesh η = build (small-denominator (η ·₊ [ 1 / 3 ]₊))
  where
  build : (Σ[ k ∈ ℕ₊₁ ] [ 1 / k ] ℚ.< fst η ℚ.· [ 1 / 3 ]) →
    Σ[ k ∈ ℕ ] fst (meshRadius k) ℚ.< fst η
  build ((1+ k) , small) = k , fine-from η k small
