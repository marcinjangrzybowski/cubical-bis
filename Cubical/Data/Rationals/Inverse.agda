module Cubical.Data.Rationals.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.Int.Fast as ℤ hiding (_+_ ; _-_ ; -_ ; _·_)
import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.Rationals as ℚ
  renaming (_+_ to _+ℚ_ ; _-_ to _-ℚ_; -_ to -ℚ_ ; _·_ to _·ℚ_)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals

open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open CommRingStr
open OrderedCommRingStr
open Units ℚCommRing

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open ElimProp

Σinverseℚ₊ : ((ε , 0<ε) : ℚ₊) → Σ[ δ ∈ ℚ ] (ε ℚ.· δ ≡ 1)
Σinverseℚ₊ = uncurry $ (SQ.ElimProp.go w)
 where
 w : _
 w .isPropB ε = isPropΠ λ _ → inverseUniqueness ε
 w .f (x , y) z .fst = [ (ℕ₊₁→ℤ y) , (ℤ.0<→ℕ₊₁-fst x) ]
 w .f (pos zero , (1+ n₁)) (pos<pos ()) .snd
 w .f (pos (suc n) , (1+ m)) (pos<pos _) .snd = ℚ!
    

infixl 7 _⁻¹₊


0<inverseℚ₊ : ∀ ε → 0 <ℚ fst (Σinverseℚ₊ ε)
0<inverseℚ₊ (ε , 0<ε) = SQ.ElimProp.go w ε 0<ε
 where
 w : SQ.ElimProp _
 w .isPropB ε = isPropΠ λ 0<ε → isProp< _ (fst (Σinverseℚ₊ (ε , 0<ε)))
 w .f (pos zero , _) (pos<pos ())
 w .f (pos (suc n) , _) _ = pos<pos _ 
 
_⁻¹₊ : ℚ₊ → ℚ₊
fst (ε ⁻¹₊) = fst (Σinverseℚ₊ ε)
snd (ε ⁻¹₊) = 0<inverseℚ₊ ε
   

_₊／₊_ : ℚ₊ → ℚ₊ → ℚ₊
ε ₊／₊ L = ε ·₊ (L ⁻¹₊)


_／₊_ : ℚ → ℚ₊ → ℚ
x ／₊ L = x ℚ.· fst (L ⁻¹₊)

⁻¹inverse : ∀ ε → ⟨ ε ₊／₊ ε ⟩₊ ≡ 1
⁻¹inverse = snd ∘ Σinverseℚ₊

·／ : ∀ L ε → ⟨ L ·₊ (ε ₊／₊ L) ⟩₊ ≡ ⟨ ε ⟩₊
·／ L ε = ℚ!

x=y/z→x·z=y : ∀ x y z → x ≡ y ／₊ z → x ℚ.· (fst z) ≡ y 
x=y/z→x·z=y x y z p = cong (ℚ._· (fst z)) p ∙ ℚ!
