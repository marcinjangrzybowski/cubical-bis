module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.RelatedLoops where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
  using (Interval; 𝕀; 𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Relation.Premetric.Instances.FunctionSpace

-- A pointwise relation is lifted BEFORE quotienting the real loops.
-- Packing related pairs needs neither an exponential law nor a choice
-- of a common modulus for the original nested loops.
module Related (X : PointedPremetricSpace ℓ-zero ℓ-zero)
  (R : fst (fst X) → fst (fst X) → Type)
  (R-prop : (x y : fst (fst X)) → isProp (R x y))
  (R-refl : (x : fst (fst X)) → R x x) where

  Space : (n : ℕ) → PremetricSpace (loopLevel n ℓ-zero ℓ-zero) ℓ-zero
  Space n = fst (realΩ^ n X)

  base : (n : ℕ) → fst (Space n)
  base n = snd (realΩ^ n X)

  Rel : (n : ℕ) → fst (Space n) → fst (Space n) → Type
  Rel zero = R
  Rel (suc n) p q = (t : 𝕀) → Rel n (fst (fst p) t) (fst (fst q) t)

  rel-prop : (n : ℕ) (p q : fst (Space n)) → isProp (Rel n p q)
  rel-prop zero = R-prop
  rel-prop (suc n) p q = isPropΠ (λ t → rel-prop n _ _)

  rel-refl : (n : ℕ) (p : fst (Space n)) → Rel n p p
  rel-refl zero = R-refl
  rel-refl (suc n) p t = rel-refl n (fst (fst p) t)

  private
    module PairSpace (n : ℕ) where
      Pair = Σ[ pq ∈ (fst (Space n) × fst (Space n)) ] Rel n (fst pq) (snd pq)
      module Injection = SubspaceAlongInjection (PremetricProduct (Space n) (Space n))
        (isSetΣSndProp (PremetricStr.isSetM (snd (PremetricProduct (Space n) (Space n))))
          (λ (p , q) → rel-prop n p q))
        (λ (p : Pair) → fst p) (λ p q → Σ≡Prop (λ (x , y) → rel-prop n x y))

  Pairs : (n : ℕ) → PremetricSpace (loopLevel n ℓ-zero ℓ-zero) ℓ-zero
  Pairs n = PairSpace.Injection.injectionPremetricSpace n

  pairs∙ : (n : ℕ) → PointedPremetricSpace (loopLevel n ℓ-zero ℓ-zero) ℓ-zero
  pairs∙ n = Pairs n , ((base n , base n) , rel-refl n (base n))

  module Step (n : ℕ) where
    private
      module L = RealLoops (Space n) (base n)
      module LP = RealLoops (Pairs n) (snd (pairs∙ n))

    slices : fst (Pairs (suc n)) → UC[ Interval , Pairs n ]
    fst (slices ((p , q) , h)) t = (L.at p t , L.at q t) , h t
    snd (slices ((p , q) , h)) = PT.map
      (λ (μ , uc) → μ , isuniformlycontinuouswith (IsUniformlyContinuousWith.pres≈ uc))
      (snd (pairUC (fst p) (fst q)))

    pack : fst (Pairs (suc n)) → LP.RealLoop
    fst (pack a) = slices a
    snd (pack ((p , q) , h)) =
      Σ≡Prop (λ (x , y) → rel-prop n x y)
        (cong₂ _,_ (fst (snd p)) (fst (snd q))) ,
      Σ≡Prop (λ (x , y) → rel-prop n x y)
        (cong₂ _,_ (snd (snd p)) (snd (snd q)))

    packUC : UC[ Pairs (suc n) , fst (realΩ (pairs∙ n)) ]
    fst packUC = pack
    snd packUC = ∣ ((λ ε → ε /2₊) , isuniformlycontinuouswith
      (λ ((p , q) , h) ((p' , q') , h') ε (pp' , qq') →
        ∣ (ε /2₊ , /2₊<id ε , λ t →
          ≈→→pointwise 𝕀 (Space n) (L.at p) (L.at p') (ε /2₊) pp' t ,
          ≈→→pointwise 𝕀 (Space n) (L.at q) (L.at q') (ε /2₊) qq' t) ∣₁)) ∣₁

    pack-based : pack (snd (pairs∙ (suc n))) ≡ snd (realΩ (pairs∙ n))
    pack-based = LP.path-ext (λ t → Σ≡Prop (λ (x , y) → rel-prop n x y) refl)

  -- Evaluation at each real loop coordinate preserves a given radius.
  -- Thus a base-space sufficient radius remains sufficient at every depth.
  close→related : (δ : ℚ₊) →
    ((x y : fst (fst X)) → PremetricStr._≈[_]_ (snd (fst X)) x δ y → R x y) →
    (n : ℕ) (p q : fst (Space n)) → PremetricStr._≈[_]_ (snd (Space n)) p δ q → Rel n p q
  close→related δ safe zero = safe
  close→related δ safe (suc n) p q close t = close→related δ safe n _ _
    (≈→→pointwise 𝕀 (Space n) (fst (fst p)) (fst (fst q)) δ close t)
