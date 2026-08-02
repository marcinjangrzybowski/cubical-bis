module Cubical.Data.Rationals.PiecewiseLinear where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as ∥₁
  using (∥_∥₁; ∣_∣₁)

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚP
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Order.Algebra
open import Cubical.Data.Rationals.Inverse

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals


-- A sequence is strictly increasing when each point is below its successor.
StrictlyIncreasingℚ₊ : (ℕ → ℚ₊) → Type₀
StrictlyIncreasingℚ₊ p = ∀ n → fst (p n) < fst (p (suc n))

-- Cofinality is kept propositionally truncated.  The locators are currently
-- supplied separately; this is the assumption from which they can later be
-- recovered using decidability of rational order.
Cofinalℚ₊ : (ℕ → ℚ₊) → Type₀
Cofinalℚ₊ p = (q : ℚ₊) → ∥ Σ[ n ∈ ℕ ] fst q < fst (p n) ∥₁

-- Interval zero is the interval between zero and the first point.  Interval
-- (suc n) lies between points n and suc n.
InOpenInterval : (ℕ → ℚ₊) → ℕ → ℚ₊ → Type₀
InOpenInterval p zero q = fst q < fst (p zero)
InOpenInterval p (suc n) q =
  (fst (p n) < fst q) × (fst q < fst (p (suc n)))

-- A locator may either identify an open interval or identify a breakpoint
-- exactly.
Location : (ℕ → ℚ₊) → ℚ₊ → Type₀
Location p q =
  (Σ[ n ∈ ℕ ] InOpenInterval p n q)
  ⊎ (Σ[ n ∈ ℕ ] q ≡ p n)

Locator : (ℕ → ℚ₊) → Type₀
Locator p = (q : ℚ₊) → Location p q


private
  -- We calculate with half-open cells: q belongs to the least n with q ≤ p n.
  -- Unlike Location, this representation is immediately useful at a breakpoint.
  Cell : (ℕ → ℚ₊) → ℕ → ℚ₊ → Type₀
  Cell p zero q = fst q ≤ fst (p zero)
  Cell p (suc n) q =
    (fst (p n) < fst q) × (fst q ≤ fst (p (suc n)))

  CellLocation : (ℕ → ℚ₊) → ℚ₊ → Type₀
  CellLocation p q = Σ[ n ∈ ℕ ] Cell p n q

  strict-offset : ∀ {p : ℕ → ℚ₊} → StrictlyIncreasingℚ₊ p
    → (n k : ℕ) → fst (p n) < fst (p (k ℕ.+ suc n))
  strict-offset {p} inc n zero = inc n
  strict-offset {p} inc n (suc k) =
    isTrans< (fst (p n)) (fst (p (k ℕ.+ suc n)))
      (fst (p (suc k ℕ.+ suc n)))
      (strict-offset {p} inc n k) (inc (k ℕ.+ suc n))

  strict-mono : ∀ {p : ℕ → ℚ₊} → StrictlyIncreasingℚ₊ p
    → ∀ {m n} → m ℕ.< n → fst (p m) < fst (p n)
  strict-mono {p} inc {m} {n} (k , k+sm≡n) =
    subst (λ j → fst (p m) < fst (p j)) k+sm≡n
      (strict-offset {p} inc m k)

  mono : ∀ {p : ℕ → ℚ₊} → StrictlyIncreasingℚ₊ p
    → ∀ {m n} → m ℕ.≤ n → fst (p m) ≤ fst (p n)
  mono {p} inc {m} {n} m≤n = ⊎.rec
    (<Weaken≤ (fst (p m)) (fst (p n)) ∘ strict-mono {p} inc)
    (λ eq → subst (λ j → fst (p m) ≤ fst (p j)) eq
      (isRefl≤ (fst (p m))))
    (ℕ.≤-split m≤n)

  cell-upper : ∀ {p : ℕ → ℚ₊} {q : ℚ₊} {n : ℕ}
    → Cell p n q → fst q ≤ fst (p n)
  cell-upper {n = zero} q≤p₀ = q≤p₀
  cell-upper {n = suc n} (_ , q≤pₙ₊₁) = q≤pₙ₊₁

  cells-not-lt : ∀ {p : ℕ → ℚ₊} {q : ℚ₊} {i j : ℕ}
    → StrictlyIncreasingℚ₊ p
    → i ℕ.< j → Cell p i q → Cell p j q → ⊥
  cells-not-lt {j = zero} inc i<j _ _ = ℕ.¬-<-zero i<j
  cells-not-lt {p} {q} {i} {suc j} inc i<j cell-i (pj<q , _) =
    ≤→≯ (fst q) (fst (p j))
      (isTrans≤ (fst q) (fst (p i)) (fst (p j))
        (cell-upper {p = p} {q = q} {n = i} cell-i)
        (mono {p} inc (ℕ.pred-≤-pred i<j))) pj<q

  cell-index-unique : ∀ {p : ℕ → ℚ₊} {q : ℚ₊}
    → StrictlyIncreasingℚ₊ p
    → (x y : CellLocation p q) → fst x ≡ fst y
  cell-index-unique {p} {q} inc x y with fst x ℕ.≟ fst y
  ... | ℕ.eq i≡j = i≡j
  ... | ℕ.lt i<j = ⊥.rec (cells-not-lt {p} {q} inc i<j (snd x) (snd y))
  ... | ℕ.gt j<i = ⊥.rec (cells-not-lt {p} {q} inc j<i (snd y) (snd x))

  isPropCell : (p : ℕ → ℚ₊) (n : ℕ) (q : ℚ₊) → isProp (Cell p n q)
  isPropCell p zero q = isProp≤ (fst q) (fst (p zero))
  isPropCell p (suc n) q =
    isProp× (isProp< (fst (p n)) (fst q))
      (isProp≤ (fst q) (fst (p (suc n))))

  isPropCellLocation : ∀ {p : ℕ → ℚ₊} {q : ℚ₊}
    → StrictlyIncreasingℚ₊ p
    → isProp (CellLocation p q)
  isPropCellLocation {p} {q} inc x y =
    Σ≡Prop (λ n → isPropCell p n q) (cell-index-unique {p} {q} inc x y)

  location→cell : ∀ {p : ℕ → ℚ₊} {q : ℚ₊}
    → StrictlyIncreasingℚ₊ p
    → Location p q → CellLocation p q
  location→cell {p} {q} inc (inl (zero , q<p₀)) =
    zero , <Weaken≤ (fst q) (fst (p zero)) q<p₀
  location→cell {p} {q} inc (inl (suc n , pn<q , q<pn₊₁)) =
    suc n , pn<q , <Weaken≤ (fst q) (fst (p (suc n))) q<pn₊₁
  location→cell {p} {q} inc (inr (zero , q≡p₀)) =
    zero , ≡Weaken≤ (fst q) (fst (p zero)) (cong fst q≡p₀)
  location→cell {p} {q} inc (inr (suc n , q≡pn₊₁)) =
    suc n
    , subst (fst (p n) <_) (sym (cong fst q≡pn₊₁)) (inc n)
    , ≡Weaken≤ (fst q) (fst (p (suc n))) (cong fst q≡pn₊₁)

record PiecewiseLinearℚ₊Args : Type₀ where
  no-eta-equality
  field
    points : ℕ → ℚ₊ × ℚ₊
    source-strict : StrictlyIncreasingℚ₊ (fst ∘ points)
    target-strict : StrictlyIncreasingℚ₊ (snd ∘ points)
    source-cofinal : Cofinalℚ₊ (fst ∘ points)
    target-cofinal : Cofinalℚ₊ (snd ∘ points)
    source-locator : Locator (fst ∘ points)
    target-locator : Locator (snd ∘ points)


private
  gap : (p : ℕ → ℚ₊) → StrictlyIncreasingℚ₊ p → ℕ → ℚ₊
  gap p inc n =
    fst (p (suc n)) - fst (p n) , -< (fst (p n)) (fst (p (suc n))) (inc n)

  initialPiece : (p r : ℕ → ℚ₊) → ℚ₊ → ℚ₊
  initialPiece p r q = (q ₊／₊ p zero) ·₊ r zero

  intervalPiece : (p r : ℕ → ℚ₊)
    → (p-inc : StrictlyIncreasingℚ₊ p)
    → (r-inc : StrictlyIncreasingℚ₊ r)
    → (n : ℕ) (q : ℚ₊) → fst (p n) < fst q → ℚ₊
  intervalPiece p r p-inc r-inc n q pn<q =
    r n +₊
      (((fst q - fst (p n) , -< (fst (p n)) (fst q) pn<q)
        ₊／₊ gap p p-inc n)
       ·₊ gap r r-inc n)

  evaluate : (p r : ℕ → ℚ₊)
    → StrictlyIncreasingℚ₊ p → StrictlyIncreasingℚ₊ r
    → (q : ℚ₊) → CellLocation p q → ℚ₊
  evaluate p r p-inc r-inc q (zero , _) = initialPiece p r q
  evaluate p r p-inc r-inc q (suc n , pn<q , _) =
    intervalPiece p r p-inc r-inc n q pn<q

  initialPiece-cell : (p r : ℕ → ℚ₊) (q : ℚ₊) → Cell p zero q
    → Cell r zero (initialPiece p r q)
  initialPiece-cell p r q q≤p₀ =
    subst (fst (initialPiece p r q) ≤_) (ℚP.·IdL (fst (r zero))) product≤
    where
    ratio≤1 : fst q ／₊ p zero ≤ 1
    ratio≤1 = fst (x≤y≃x/y≤1 (fst q) (p zero)) q≤p₀

    product≤ :
      (fst q ／₊ p zero) · fst (r zero) ≤ 1 · fst (r zero)
    product≤ = ≤-·o _ _ _ (<Weaken≤ _ _ (snd (r zero))) ratio≤1

  intervalPiece-cell : (p r : ℕ → ℚ₊)
    (p-inc : StrictlyIncreasingℚ₊ p) (r-inc : StrictlyIncreasingℚ₊ r)
    (n : ℕ) (q : ℚ₊)
    → (pn<q : fst (p n) < fst q)
    → fst q ≤ fst (p (suc n))
    → Cell r (suc n) (intervalPiece p r p-inc r-inc n q pn<q)
  intervalPiece-cell p r p-inc r-inc n q pn<q q≤pn₊₁ =
    <₊SumLeft (r n)
      (((fst q - fst (p n) , -< (fst (p n)) (fst q) pn<q)
        ₊／₊ gap p p-inc n)
       ·₊ gap r r-inc n)
    , subst (fst (intervalPiece p r p-inc r-inc n q pn<q) ≤_) upper-path
        sum≤
    where
    q-pn≤gap : fst q - fst (p n) ≤ fst (p (suc n)) - fst (p n)
    q-pn≤gap = subst2 _≤_ ℚ!! ℚ!!
      (≤-+o (fst q) (fst (p (suc n))) (- fst (p n)) q≤pn₊₁)

    ratio≤1 :
      (fst q - fst (p n)) ／₊ gap p p-inc n ≤ 1
    ratio≤1 =
      fst (x≤y≃x/y≤1 (fst q - fst (p n)) (gap p p-inc n)) q-pn≤gap

    product≤ :
      ((fst q - fst (p n)) ／₊ gap p p-inc n)
        · fst (gap r r-inc n)
      ≤ 1 · fst (gap r r-inc n)
    product≤ = ≤-·o _ _ _
      (<Weaken≤ _ _ (snd (gap r r-inc n))) ratio≤1

    sum≤ :
      fst (r n) +
        (((fst q - fst (p n)) ／₊ gap p p-inc n)
          · fst (gap r r-inc n))
      ≤ fst (r n) + (1 · fst (gap r r-inc n))
    sum≤ = ≤-o+ _ _ (fst (r n)) product≤

    upper-path :
      fst (r n) + (1 · fst (gap r r-inc n)) ≡ fst (r (suc n))
    upper-path = ℚ!!

  evaluate-cell : (p r : ℕ → ℚ₊)
    (p-inc : StrictlyIncreasingℚ₊ p) (r-inc : StrictlyIncreasingℚ₊ r)
    (q : ℚ₊) (loc : CellLocation p q)
    → Cell r (fst loc) (evaluate p r p-inc r-inc q loc)
  evaluate-cell p r p-inc r-inc q (zero , q≤p₀) =
    initialPiece-cell p r q q≤p₀
  evaluate-cell p r p-inc r-inc q (suc n , pn<q , q≤pn₊₁) =
    intervalPiece-cell p r p-inc r-inc n q pn<q q≤pn₊₁

  cancel-scale : (x : ℚ) (u : ℚ₊) → (x · fst u) ／₊ u ≡ x
  cancel-scale x u =
    sym (ℚP.·Assoc x (fst u) (fst (u ⁻¹₊)))
    ∙ cong (x ·_) (x·invℚ₊[x] u)
    ∙ ℚP.·IdR x

  cancel-division : (x : ℚ) (u : ℚ₊) → (x ／₊ u) · fst u ≡ x
  cancel-division x u =
    sym (ℚP.·Assoc x (fst (u ⁻¹₊)) (fst u))
    ∙ cong (x ·_) (invℚ₊[x]·x u)
    ∙ ℚP.·IdR x

  affine-inverse : (a c x : ℚ) (sourceGap targetGap : ℚ₊) →
    a +
      ((((c + ((x - a) ／₊ sourceGap) · fst targetGap) - c)
        ／₊ targetGap)
       · fst sourceGap)
    ≡ x
  affine-inverse a c x sourceGap targetGap =
    cong (λ (z : ℚ) → a + (z ／₊ targetGap) · fst sourceGap)
      subtract-middle
    ∙ cong (λ z → a + z · fst sourceGap)
        (cancel-scale ((x - a) ／₊ sourceGap) targetGap)
    ∙ cong (a +_) (cancel-division (x - a) sourceGap)
    ∙ ℚ!!
    where
    subtract-middle :
      (c + ((x - a) ／₊ sourceGap) · fst targetGap) - c
      ≡ ((x - a) ／₊ sourceGap) · fst targetGap
    subtract-middle = ℚ!!

  evaluate-inverse : (p r : ℕ → ℚ₊)
    (p-inc : StrictlyIncreasingℚ₊ p) (r-inc : StrictlyIncreasingℚ₊ r)
    (q : ℚ₊) (loc : CellLocation p q)
    → evaluate r p r-inc p-inc
        (evaluate p r p-inc r-inc q loc)
        (fst loc , evaluate-cell p r p-inc r-inc q loc)
      ≡ q
  evaluate-inverse p r p-inc r-inc q (zero , q≤p₀) =
    ℚ₊≡
      (cong (_· fst (p zero))
        (cancel-scale (fst q ／₊ p zero) (r zero))
      ∙ cancel-division (fst q) (p zero))
  evaluate-inverse p r p-inc r-inc q (suc n , pn<q , q≤pn₊₁) =
    ℚ₊≡
      (affine-inverse (fst (p n)) (fst (r n)) (fst q)
        (gap p p-inc n) (gap r r-inc n))

  evaluate-point : (p r : ℕ → ℚ₊)
    (p-inc : StrictlyIncreasingℚ₊ p) (r-inc : StrictlyIncreasingℚ₊ r)
    (n : ℕ) →
    evaluate p r p-inc r-inc (p n)
      (location→cell p-inc (inr (n , refl)))
    ≡ r n
  evaluate-point p r p-inc r-inc zero =
    ℚ₊≡
      (cong (_· fst (r zero)) (⁻¹inverse (p zero))
      ∙ ℚP.·IdL (fst (r zero)))
  evaluate-point p r p-inc r-inc (suc n) =
    ℚ₊≡
      (cong (λ z → fst (r n) + z · fst (gap r r-inc n))
        (⁻¹inverse (gap p p-inc n))
      ∙ ℚ!!)


private
  module PiecewiseLinearConstruction (args : PiecewiseLinearℚ₊Args) where
    open PiecewiseLinearℚ₊Args args

    source target : ℕ → ℚ₊
    source = fst ∘ points
    target = snd ∘ points

    sourceCell : (q : ℚ₊) → CellLocation source q
    sourceCell q = location→cell source-strict (source-locator q)

    targetCell : (q : ℚ₊) → CellLocation target q
    targetCell q = location→cell target-strict (target-locator q)

    forward backward : ℚ₊ → ℚ₊
    forward q = evaluate source target source-strict target-strict q (sourceCell q)
    backward q = evaluate target source target-strict source-strict q (targetCell q)

    backward-forward : ∀ q → backward (forward q) ≡ q
    backward-forward q =
      cong (evaluate target source target-strict source-strict (forward q))
        (isPropCellLocation target-strict (targetCell (forward q))
          (fst (sourceCell q) ,
            evaluate-cell source target source-strict target-strict q (sourceCell q)))
      ∙ evaluate-inverse source target source-strict target-strict q (sourceCell q)

    forward-backward : ∀ q → forward (backward q) ≡ q
    forward-backward q =
      cong (evaluate source target source-strict target-strict (backward q))
        (isPropCellLocation source-strict (sourceCell (backward q))
          (fst (targetCell q) ,
            evaluate-cell target source target-strict source-strict q (targetCell q)))
      ∙ evaluate-inverse target source target-strict source-strict q (targetCell q)

piecewiseLinearℚ₊Iso : PiecewiseLinearℚ₊Args → Iso ℚ₊ ℚ₊
Iso.fun (piecewiseLinearℚ₊Iso args) = PiecewiseLinearConstruction.forward args
Iso.inv (piecewiseLinearℚ₊Iso args) = PiecewiseLinearConstruction.backward args
Iso.sec (piecewiseLinearℚ₊Iso args) = PiecewiseLinearConstruction.forward-backward args
Iso.ret (piecewiseLinearℚ₊Iso args) = PiecewiseLinearConstruction.backward-forward args

piecewiseLinearℚ₊ : PiecewiseLinearℚ₊Args → ℚ₊ ≃ ℚ₊
piecewiseLinearℚ₊ args = isoToEquiv (piecewiseLinearℚ₊Iso args)

piecewiseLinearEquivℚ₊ : PiecewiseLinearℚ₊Args → ℚ₊ ≃ ℚ₊
piecewiseLinearEquivℚ₊ = piecewiseLinearℚ₊

piecewiseLinearAutomorphismℚ₊ : PiecewiseLinearℚ₊Args → ℚ₊ ≃ ℚ₊
piecewiseLinearAutomorphismℚ₊ = piecewiseLinearEquivℚ₊

piecewiseLinearℚ₊-point : (args : PiecewiseLinearℚ₊Args) (n : ℕ) →
  equivFun (piecewiseLinearℚ₊ args)
    (fst (PiecewiseLinearℚ₊Args.points args n))
  ≡ snd (PiecewiseLinearℚ₊Args.points args n)
piecewiseLinearℚ₊-point args n =
  cong (evaluate source target source-strict target-strict (source n))
    (isPropCellLocation source-strict selected canonical)
  ∙ evaluate-point source target source-strict target-strict n
  where
  open PiecewiseLinearℚ₊Args args

  source target : ℕ → ℚ₊
  source = fst ∘ points
  target = snd ∘ points

  selected : CellLocation source (source n)
  selected = location→cell source-strict (source-locator (source n))

  canonical : CellLocation source (source n)
  canonical = location→cell source-strict (inr (n , refl))
