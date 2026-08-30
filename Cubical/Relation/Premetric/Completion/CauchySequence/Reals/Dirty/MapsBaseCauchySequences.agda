module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Dirty.MapsBaseCauchySequences where

-- This is an exploratory module.  Its purpose is to isolate the choice
-- needed when the only hypothesis on a rational map is preservation of
-- Cauchy sequences.  Nothing in this module is re-exported by the stable
-- Cauchy-sequence completion API.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.Algebra as ℚ
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph
  as CauchyGraphDefinition

module G = CauchyGraphDefinition ℚPremetricSpace ℚPremetricSpace
module S = Real.Base
module SP = Real.Premetric

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


-- The weak premise under investigation.  It only knows how to act on a
-- sequence whose terms are injected rationals; its values may already be
-- arbitrary completed reals.

MapsRationalCauchySequencesToReals : (ℚ → Real.ℝ) → Type₀
MapsRationalCauchySequencesToReals f =
  ∀ q → S.IsCauchySequence (Real.ιℚ ∘ q) →
    S.IsCauchySequence (f ∘ q)


isPropMapsRationalCauchySequencesToReals : ∀ f →
  isProp (MapsRationalCauchySequencesToReals f)
isPropMapsRationalCauchySequencesToReals f =
  isPropΠ2 λ _ _ → S.isPropIsCauchySequence _


-- For an ordinary rational endomap, this is the same weak premise with the
-- codomain injection made explicit.

MapsRationalCauchySequences : (ℚ → ℚ) → Type₀
MapsRationalCauchySequences f =
  MapsRationalCauchySequencesToReals (Real.ιℚ ∘ f)


-- Two completion-valued sequences are eventually close if, separately at
-- each radius, a suitable tail merely exists.  This matches the placement
-- of truncation in `IsCauchySequence`.

EventuallyClose : (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyClose x y = ∀ ε →
  ∃[ N ∈ ℕ ]
    (∀ n → N ℕ.≤ n → x n S.≈ᶜ[ ε ] y n)


isPropEventuallyClose : ∀ x y → isProp (EventuallyClose x y)
isPropEventuallyClose x y = isPropΠ λ _ → squash₁


private
  tripleQuarter< : ∀ ε →
    ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
           (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾


-- Cauchyness is invariant under an eventually vanishing pointwise error.
-- This is the elementary metric step used after a rational graph selection
-- has been made.

cauchy-under-eventual-closeness : ∀ {x y} →
  S.IsCauchySequence x → EventuallyClose x y →
  S.IsCauchySequence y
cauchy-under-eventual-closeness {x} {y} gx x∼y ε =
  PT.rec squash₁ with-source (gx leg)
  where
  leg = ε /4₊

  with-source : S.CauchyTail x leg → ∥ S.CauchyTail y ε ∥₁
  with-source (K , xc) =
    PT.rec squash₁ (with-error K xc) (x∼y leg)
    where
    with-error :
      (K : ℕ) →
      (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
        x m S.≈ᶜ[ leg ] x n) →
      (Σ[ N ∈ ℕ ]
        (∀ n → N ℕ.≤ n → x n S.≈ᶜ[ leg ] y n)) →
      ∥ S.CauchyTail y ε ∥₁
    with-error K xc (L , close) = ∣ N , tail ∣₁
      where
      N = ℕ.max K L

      K≤N : K ℕ.≤ N
      K≤N = ℕ.left-≤-max {m = K} {n = L}

      L≤N : L ℕ.≤ N
      L≤N = ℕ.right-≤-max {n = L} {m = K}

      tail : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        y m S.≈ᶜ[ ε ] y n
      tail m n N≤m N≤n =
        S.isMonotone≈ᶜ< _ _ _ ε (tripleQuarter< ε)
          (Real.Approximation.tri≈ᶜ _ _ _ (leg +₊ leg) leg
            (Real.Approximation.tri≈ᶜ _ _ _ leg leg
              (S.sym≈ᶜ _ _ leg
                (close m (ℕ.≤-trans L≤N N≤m)))
              (xc m n
                (ℕ.≤-trans K≤N N≤m)
                (ℕ.≤-trans K≤N N≤n)))
            (close n (ℕ.≤-trans L≤N N≤n)))


-- At a limit constructor the graph extension needs to know that an
-- arbitrary completion-valued graph sequence has a Cauchy image.  The weak
-- premise cannot be applied directly: its input must be a single rational
-- sequence.  `RationalGraphSelection` names exactly such a bridge.

RationalGraphSelection : (ℚ → Real.ℝ) → Type₀
RationalGraphSelection f =
  ∀ x y → (∀ n → G.GraphClosure f (x n) (y n)) →
  S.IsCauchySequence x →
  ∥ Σ[ q ∈ (ℕ → ℚ) ]
      S.IsCauchySequence (Real.ιℚ ∘ q) ×
      EventuallyClose (f ∘ q) y ∥₁


isPropRationalGraphSelection : ∀ f →
  isProp (RationalGraphSelection f)
isPropRationalGraphSelection f =
  isPropΠ4 λ _ _ _ _ → squash₁


maps+selection→preservesCauchyGraphs : ∀ {f} →
  MapsRationalCauchySequencesToReals f →
  RationalGraphSelection f →
  G.PreservesCauchyGraphs f
maps+selection→preservesCauchyGraphs maps select =
  G.preservesCauchyGraphs λ x y joint gx →
    PT.rec (S.isPropIsCauchySequence y)
      (λ where
        (q , q-cauchy , fq∼y) →
          cauchy-under-eventual-closeness
            (maps q q-cauchy) fq∼y)
      (select x y joint gx)


-- Consequently the existing graph extension gives a genuine total lift.
-- It extends the base map definitionally, and the resulting function maps
-- all completion-valued Cauchy sequences to Cauchy sequences.

liftWithGraphSelection :
  (f : ℚ → Real.ℝ) →
  MapsRationalCauchySequencesToReals f →
  RationalGraphSelection f →
  Real.ℝ → Real.ℝ
liftWithGraphSelection f maps select =
  G.extend f (maps+selection→preservesCauchyGraphs maps select)


liftWithGraphSelection-ι :
  ∀ (f : ℚ → Real.ℝ)
    (maps : MapsRationalCauchySequencesToReals f)
    (select : RationalGraphSelection f) q →
  liftWithGraphSelection f maps select (Real.ιℚ q) ≡ f q
liftWithGraphSelection-ι f maps select =
  G.extend-ι f (maps+selection→preservesCauchyGraphs maps select)


liftWithGraphSelection-presCauchy :
  ∀ (f : ℚ → Real.ℝ)
    (maps : MapsRationalCauchySequencesToReals f)
    (select : RationalGraphSelection f) →
  G.PreservesCauchySequences
    (liftWithGraphSelection f maps select)
liftWithGraphSelection-presCauchy f maps select =
  G.extend-presCauchy f
    (maps+selection→preservesCauchyGraphs maps select)


-- Why the selection is a choice principle -------------------------------
--
-- Graph closure supplies one truncated rational approximation for each
-- sequence index and requested pair of radii.  A diagonal rational
-- sequence asks to commute the outer natural-number product with that
-- truncation.  We parameterize, but do not assume, precisely that commute.

CountableChoice₀ : Type₁
CountableChoice₀ =
  ∀ (A : ℕ → Type₀) →
    (∀ n → ∥ A n ∥₁) → ∥ (∀ n → A n) ∥₁


record VanishingRadii : Type₀ where

  no-eta-equality

  field
    radius : ℕ → ℚ₊
    eventuallySmall : ∀ ε →
      Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → radius n <₊ ε)

open VanishingRadii public


private
  dyadic : ℕ → ℚ₊
  dyadic n = [ 1 / 2 ]₊ ℚ₊^ⁿ n

  half<one : fst [ 1 / 2 ]₊ <ℚ 1
  half<one = subst (fst [ 1 / 2 ]₊ <ℚ_)
    (/2+/2≡id 1) (<₊SumLeft [ 1 / 2 ]₊ [ 1 / 2 ]₊)

  dyadicAntitone : ∀ m n → m ℕ.≤ n →
    fst (dyadic n) ≤ℚ fst (dyadic m)
  dyadicAntitone m n m≤n =
    powExponentAntitone (fst [ 1 / 2 ]₊)
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        _ _ (snd [ 1 / 2 ]₊))
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        _ _ half<one)
      m n m≤n


dyadicVanishingRadii : VanishingRadii
dyadicVanishingRadii .radius = dyadic
dyadicVanishingRadii .eventuallySmall ε = N , small
  where
  N = fst (1/2ⁿ<ε ε)

  small : ∀ n → N ℕ.≤ n → dyadic n <₊ ε
  small n N≤n = begin<
    fst (dyadic n)
      ≤⟨ dyadicAntitone N n N≤n ⟩
    fst (dyadic N)
      <⟨ snd (1/2ⁿ<ε ε) ⟩
    fst ε ◾


-- A selected diagonal approximation of a Cauchy source sequence is again
-- Cauchy.  This proof is choice-free once the diagonal has been selected.

diagonalInputIsCauchy :
  (scale : VanishingRadii) → ∀ x (q : ℕ → ℚ) →
  (∀ n → Real.ιℚ (q n) S.≈ᶜ[ radius scale n ] x n) →
  S.IsCauchySequence x →
  S.IsCauchySequence (Real.ιℚ ∘ q)
diagonalInputIsCauchy scale x q q∼x gx ε =
  PT.rec squash₁ with-source (gx leg)
  where
  leg = ε /4₊

  R : ℕ
  R = fst (eventuallySmall scale leg)

  radius-small : ∀ n → R ℕ.≤ n → radius scale n <₊ leg
  radius-small = snd (eventuallySmall scale leg)

  with-source : S.CauchyTail x leg →
    ∥ S.CauchyTail (Real.ιℚ ∘ q) ε ∥₁
  with-source (K , xc) = ∣ N , tail ∣₁
    where
    N = ℕ.max K R

    K≤N : K ℕ.≤ N
    K≤N = ℕ.left-≤-max {m = K} {n = R}

    R≤N : R ℕ.≤ N
    R≤N = ℕ.right-≤-max {n = R} {m = K}

    tail : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
      Real.ιℚ (q m) S.≈ᶜ[ ε ] Real.ιℚ (q n)
    tail m n N≤m N≤n =
      S.isMonotone≈ᶜ< _ _ _ ε (tripleQuarter< ε)
        (Real.Approximation.tri≈ᶜ _ _ _ (leg +₊ leg) leg
          (Real.Approximation.tri≈ᶜ _ _ _ leg leg
            (S.isMonotone≈ᶜ< _ _ _ leg
              (radius-small m (ℕ.≤-trans R≤N N≤m))
              (q∼x m))
            (xc m n
              (ℕ.≤-trans K≤N N≤m)
              (ℕ.≤-trans K≤N N≤n)))
          (S.sym≈ᶜ _ _ leg
            (S.isMonotone≈ᶜ< _ _ _ leg
              (radius-small n (ℕ.≤-trans R≤N N≤n))
              (q∼x n))))


diagonalOutputEventuallyClose :
  (scale : VanishingRadii) → ∀ (f : ℚ → Real.ℝ) q y →
  (∀ n → f (q n) S.≈ᶜ[ radius scale n ] y n) →
  EventuallyClose (f ∘ q) y
diagonalOutputEventuallyClose scale f q y fq∼y ε =
  ∣ N , close ∣₁
  where
  N = fst (eventuallySmall scale ε)

  close : ∀ n → N ℕ.≤ n → f (q n) S.≈ᶜ[ ε ] y n
  close n N≤n =
    S.isMonotone≈ᶜ< _ _ _ ε
      (snd (eventuallySmall scale ε) n N≤n)
      (fq∼y n)


countableChoice→rationalGraphSelection :
  VanishingRadii → CountableChoice₀ →
  ∀ f → RationalGraphSelection f
countableChoice→rationalGraphSelection scale choice f x y joint gx =
  PT.map finish (choice A pointwise)
  where
  A : ℕ → Type₀
  A n = Σ[ q ∈ ℚ ]
    (Real.ιℚ q S.≈ᶜ[ radius scale n ] x n) ×
    (f q S.≈ᶜ[ radius scale n ] y n)

  pointwise : ∀ n → ∥ A n ∥₁
  pointwise n = joint n (radius scale n) (radius scale n)

  finish : (∀ n → A n) →
    Σ[ q ∈ (ℕ → ℚ) ]
      S.IsCauchySequence (Real.ιℚ ∘ q) ×
      EventuallyClose (f ∘ q) y
  finish selected =
    q ,
    diagonalInputIsCauchy scale x q
      (λ n → selected n .snd .fst) gx ,
    diagonalOutputEventuallyClose scale f q y
      (λ n → selected n .snd .snd)
    where
    q : ℕ → ℚ
    q n = selected n .fst


-- Thus countable choice is sufficient for the weak premise to support the
-- desired lift.  Keeping it as an explicit argument records the obstruction
-- rather than silently adding an axiom to the rational completion.

liftWithCountableChoice :
  CountableChoice₀ →
  (f : ℚ → Real.ℝ) →
  MapsRationalCauchySequencesToReals f →
  Real.ℝ → Real.ℝ
liftWithCountableChoice choice f maps =
  liftWithGraphSelection f maps
    (countableChoice→rationalGraphSelection
      dyadicVanishingRadii choice f)


liftWithCountableChoice-ι :
  ∀ (choice : CountableChoice₀)
    (f : ℚ → Real.ℝ)
    (maps : MapsRationalCauchySequencesToReals f) q →
  liftWithCountableChoice choice f maps (Real.ιℚ q) ≡ f q
liftWithCountableChoice-ι choice f maps =
  liftWithGraphSelection-ι f maps
    (countableChoice→rationalGraphSelection
      dyadicVanishingRadii choice f)


liftRationalMapWithCountableChoice :
  CountableChoice₀ →
  (f : ℚ → ℚ) → MapsRationalCauchySequences f →
  Real.ℝ → Real.ℝ
liftRationalMapWithCountableChoice choice f =
  liftWithCountableChoice choice (Real.ιℚ ∘ f)


liftRationalMapWithCountableChoice-ι :
  ∀ (choice : CountableChoice₀)
    (f : ℚ → ℚ) (maps : MapsRationalCauchySequences f) q →
  liftRationalMapWithCountableChoice choice f maps (Real.ιℚ q) ≡
    Real.ιℚ (f q)
liftRationalMapWithCountableChoice-ι choice f maps q =
  liftWithCountableChoice-ι choice (Real.ιℚ ∘ f) maps q
