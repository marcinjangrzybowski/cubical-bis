module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Lift.MapsRationalCauchySequencesPresented where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous
  as CauchyContinuousDefinition

module S = SequentialDefinition ℚPremetricSpace
module SP = SequentialPropertiesDefinition ℚPremetricSpace
module C = CauchyContinuousDefinition

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


-- A real presentation keeps the rational sequence as computational data.
-- Its Cauchy witness remains mere, exactly as in the weak hypothesis.

record RationalCauchyPresentation : Type₀ where

  no-eta-equality

  field
    sequence : ℕ → ℚ
    cauchy : C.RationalSeqWitness sequence

open RationalCauchyPresentation public


presentedReal : RationalCauchyPresentation → S.ℭ̂ₛ
presentedReal p =
  S.lim (S.ι ∘ sequence p)
    (C.rationalSeqWitness→injected
      (sequence p) (cauchy p))


-- This redundant version records explicitly which real is represented.  It
-- is useful as a domain for operations which are allowed to inspect the
-- chosen rational approximation.

record RealWithRationalCauchyPresentation : Type₀ where

  no-eta-equality

  field
    real : S.ℭ̂ₛ
    presentation : RationalCauchyPresentation
    realizes : real ≡ presentedReal presentation

open RealWithRationalCauchyPresentation public


canonicalPresentedReal :
  RationalCauchyPresentation → RealWithRationalCauchyPresentation
canonicalPresentedReal p .real = presentedReal p
canonicalPresentedReal p .presentation = p
canonicalPresentedReal p .realizes = refl


-- Constants give canonical presentations of injected rationals.

constantSequence : ℚ → ℕ → ℚ
constantSequence q _ = q


constantInjectedWitness : ∀ q →
  S.SeqWitness (S.ι ∘ constantSequence q)
constantInjectedWitness q =
  ∣ (λ _ → zero) ,
    (λ ε m n _ _ → S.isRefl∼̂ₛ (S.ι q) ε) ∣₁


constantRationalWitness : ∀ q →
  C.RationalSeqWitness (constantSequence q)
constantRationalWitness q =
  C.injectedSeqWitness→rational
    (constantSequence q) (constantInjectedWitness q)


constantPresentation : ℚ → RationalCauchyPresentation
constantPresentation q .sequence = constantSequence q
constantPresentation q .cauchy = constantRationalWitness q


constantLimit≡ι : ∀ q
  (g : S.SeqWitness (S.ι ∘ constantSequence q)) →
  S.lim (S.ι ∘ constantSequence q) g ≡ S.ι q
constantLimit≡ι q g = S.eqℭ _ _ λ ε →
  S.sym∼ _ _ ε
    (PT.rec (S.isProp∼ (S.ι q) ε
      (S.lim (S.ι ∘ constantSequence q) g))
      (λ where
        (K , close) → close K ℕ.≤-refl)
      (SP.lim-isLimitSeq (S.ι ∘ constantSequence q) g ε))


ι≡presentedConstant : ∀ q →
  S.ι q ≡ presentedReal (constantPresentation q)
ι≡presentedConstant q = sym
  (constantLimit≡ι q
    (C.rationalSeqWitness→injected
      (constantSequence q) (constantRationalWitness q)))


rationalWithPresentation :
  ℚ → RealWithRationalCauchyPresentation
rationalWithPresentation q .real = S.ι q
rationalWithPresentation q .presentation = constantPresentation q
rationalWithPresentation q .realizes = ι≡presentedConstant q


-- Direct mapping of presentations ----------------------------------------

mapRationalCauchyPresentation :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  RationalCauchyPresentation → RationalCauchyPresentation
mapRationalCauchyPresentation f maps p .sequence =
  f ∘ sequence p
mapRationalCauchyPresentation f maps p .cauchy =
  maps (sequence p) (cauchy p)


liftFromRationalCauchyPresentation :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  RationalCauchyPresentation → S.ℭ̂ₛ
liftFromRationalCauchyPresentation f maps =
  presentedReal ∘ mapRationalCauchyPresentation f maps


mapRealWithRationalCauchyPresentation :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  RealWithRationalCauchyPresentation →
  RealWithRationalCauchyPresentation
mapRealWithRationalCauchyPresentation f maps x =
  canonicalPresentedReal
    (mapRationalCauchyPresentation f maps (presentation x))


forgetMappedReal :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  RealWithRationalCauchyPresentation → S.ℭ̂ₛ
forgetMappedReal f maps =
  real ∘ mapRealWithRationalCauchyPresentation f maps


liftFromRationalCauchyPresentation-sequence :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) p →
  liftFromRationalCauchyPresentation f maps p ≡
    S.lim (S.ι ∘ f ∘ sequence p)
      (C.rationalSeqWitness→injected (f ∘ sequence p)
        (maps (sequence p) (cauchy p)))
liftFromRationalCauchyPresentation-sequence f maps p = refl


forgetMappedReal-computes :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) x →
  forgetMappedReal f maps x ≡
    liftFromRationalCauchyPresentation f maps (presentation x)
forgetMappedReal-computes f maps x = refl


liftFromRationalCauchyPresentation-rational :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) q →
  liftFromRationalCauchyPresentation f maps
    (constantPresentation q) ≡ S.ι (f q)
liftFromRationalCauchyPresentation-rational f maps q =
  constantLimit≡ι (f q)
    (C.rationalSeqWitness→injected
      (f ∘ constantSequence q)
      (maps (constantSequence q) (constantRationalWitness q)))


forgetMappedReal-rational :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) q →
  forgetMappedReal f maps (rationalWithPresentation q) ≡ S.ι (f q)
forgetMappedReal-rational =
  liftFromRationalCauchyPresentation-rational


-- Descent to ordinary reals ----------------------------------------------
--
-- The direct construction is already total on presented reals.  To forget
-- the presentation before applying it, one needs exactly the following
-- presentation-independence statement.  It is separated out so that an
-- attempted proof from `maps` cannot hide a countable-choice assumption.

IsPresentationIndependent :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f → Type₀
IsPresentationIndependent f maps =
  ∀ p p' → presentedReal p ≡ presentedReal p' →
    liftFromRationalCauchyPresentation f maps p ≡
    liftFromRationalCauchyPresentation f maps p'


isPropIsPresentationIndependent :
  ∀ f maps → isProp (IsPresentationIndependent f maps)
isPropIsPresentationIndependent f maps =
  isPropΠ3 λ _ _ _ → S.isSetℭ̂ₛ _ _


-- Independence immediately makes the mapped value independent of every
-- field except the represented real.

forgetMappedReal-independent :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) →
  IsPresentationIndependent f maps →
  ∀ x y → real x ≡ real y →
  forgetMappedReal f maps x ≡ forgetMappedReal f maps y
forgetMappedReal-independent f maps independent x y x≡y =
  independent (presentation x) (presentation y)
    (sym (realizes x) ∙ x≡y ∙ realizes y)


-- Quotient of rational presentations -------------------------------------
--
-- Interleaving is the useful equivalence test here.  If the interleaving
-- of two rational sequences is Cauchy, their represented limits agree.  A
-- map which sends rational Cauchy sequences to rational Cauchy sequences
-- preserves this relation immediately.

interleave : (ℕ → ℚ) → (ℕ → ℚ) → ℕ → ℚ
interleave q r zero = q zero
interleave q r (suc zero) = r zero
interleave q r (suc (suc n)) =
  interleave (q ∘ suc) (r ∘ suc) n


interleave-even : ∀ q r n →
  interleave q r (ℕ.doubleℕ n) ≡ q n
interleave-even q r zero = refl
interleave-even q r (suc n) =
  interleave-even (q ∘ suc) (r ∘ suc) n


interleave-odd : ∀ q r n →
  interleave q r (suc (ℕ.doubleℕ n)) ≡ r n
interleave-odd q r zero = refl
interleave-odd q r (suc n) =
  interleave-odd (q ∘ suc) (r ∘ suc) n


interleave-map-pointwise : ∀ f q r n →
  interleave (f ∘ q) (f ∘ r) n ≡ f (interleave q r n)
interleave-map-pointwise f q r zero = refl
interleave-map-pointwise f q r (suc zero) = refl
interleave-map-pointwise f q r (suc (suc n)) =
  interleave-map-pointwise f (q ∘ suc) (r ∘ suc) n


interleave-map : ∀ f q r →
  interleave (f ∘ q) (f ∘ r) ≡ f ∘ interleave q r
interleave-map f q r = funExt (interleave-map-pointwise f q r)


n≤double : ∀ n → n ℕ.≤ ℕ.doubleℕ n
n≤double zero = ℕ.≤-refl
n≤double (suc n) =
  ℕ.suc-≤-suc (ℕ.≤-trans (n≤double n) ℕ.≤-sucℕ)


data ParitySplit : ℕ → Type₀ where
  even : ∀ n → ParitySplit (ℕ.doubleℕ n)
  odd : ∀ n → ParitySplit (suc (ℕ.doubleℕ n))


paritySplit : ∀ n → ParitySplit n
paritySplit zero = even zero
paritySplit (suc n) with paritySplit n
... | even k = odd k
... | odd k = even (suc k)


double≤double→≤ : ∀ {m n} →
  ℕ.doubleℕ m ℕ.≤ ℕ.doubleℕ n → m ℕ.≤ n
double≤double→≤ {zero} {n} p = ℕ.zero-≤
double≤double→≤ {suc m} {zero} p =
  ⊥.rec (ℕ.¬-<-zero p)
double≤double→≤ {suc m} {suc n} p =
  ℕ.suc-≤-suc
    (double≤double→≤
      (ℕ.pred-≤-pred (ℕ.pred-≤-pred p)))


double≤odd→≤ : ∀ {m n} →
  ℕ.doubleℕ m ℕ.≤ suc (ℕ.doubleℕ n) → m ℕ.≤ n
double≤odd→≤ {zero} {n} p = ℕ.zero-≤
double≤odd→≤ {suc m} {zero} p =
  ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred p))
double≤odd→≤ {suc m} {suc n} p =
  ℕ.suc-≤-suc
    (double≤odd→≤
      (ℕ.pred-≤-pred (ℕ.pred-≤-pred p)))


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


InterleavingCauchy :
  RationalCauchyPresentation → RationalCauchyPresentation → Type₀
InterleavingCauchy p p' =
  C.RationalSeqWitness
    (interleave (sequence p) (sequence p'))


isPropInterleavingCauchy : ∀ p p' →
  isProp (InterleavingCauchy p p')
isPropInterleavingCauchy p p' = squash₁


interleavingCauchy→presentedReal≡ : ∀ p p' →
  InterleavingCauchy p p' → presentedReal p ≡ presentedReal p'
interleavingCauchy→presentedReal≡ p p' joined =
  PT.rec (S.isSetℭ̂ₛ _ _) with-left left-witness
  where
  q = sequence p
  r = sequence p'

  q̂ r̂ joined̂ : ℕ → S.ℭ̂ₛ
  q̂ = S.ι ∘ q
  r̂ = S.ι ∘ r
  joined̂ = S.ι ∘ interleave q r

  left-witness : S.SeqWitness q̂
  left-witness = C.rationalSeqWitness→injected q (cauchy p)

  right-witness : S.SeqWitness r̂
  right-witness = C.rationalSeqWitness→injected r (cauchy p')

  joined-witness : S.SeqWitness joined̂
  joined-witness =
    C.rationalSeqWitness→injected (interleave q r) joined

  with-left : S.CauchySeq q̂ →
    presentedReal p ≡ presentedReal p'
  with-left (Kq , qc) =
    PT.rec (S.isSetℭ̂ₛ _ _) with-right right-witness
    where
    with-right : S.CauchySeq r̂ →
      presentedReal p ≡ presentedReal p'
    with-right (Kr , rc) =
      PT.rec (S.isSetℭ̂ₛ _ _) with-joined joined-witness
      where
      with-joined : S.CauchySeq joined̂ →
        presentedReal p ≡ presentedReal p'
      with-joined (Kj , jc) = S.eqℭ _ _ close
        where
        close : ∀ ε →
          presentedReal p S.∼̂ₛ[ ε ] presentedReal p'
        close ε =
          S.isMonotone∼̂ₛ< _ _ _ ε (tripleQuarter< ε)
            (S.tri∼ _ _ _ (ε /4₊ +₊ ε /4₊) (ε /4₊)
              (S.tri∼ _ _ _ (ε /4₊) (ε /4₊)
                (S.sym∼ _ _ (ε /4₊) qk-close-left)
                qk-close-rk)
              rk-close-right)
          where
          leg = ε /4₊

          Bq Br Bj : ℕ
          Bq = Kq ((leg /4₊) /4₊)
          Br = Kr ((leg /4₊) /4₊)
          Bj = Kj leg

          k : ℕ
          k = ℕ.max (ℕ.max Bq Br) Bj

          Bq≤k : Bq ℕ.≤ k
          Bq≤k = ℕ.≤-trans
            (ℕ.left-≤-max {m = Bq} {n = Br})
            (ℕ.left-≤-max {m = ℕ.max Bq Br} {n = Bj})

          Br≤k : Br ℕ.≤ k
          Br≤k = ℕ.≤-trans
            (ℕ.right-≤-max {n = Br} {m = Bq})
            (ℕ.left-≤-max {m = ℕ.max Bq Br} {n = Bj})

          Bj≤k : Bj ℕ.≤ k
          Bj≤k = ℕ.right-≤-max
            {n = Bj} {m = ℕ.max Bq Br}

          qk-close-left :
            S.ι (q k) S.∼̂ₛ[ leg ] presentedReal p
          qk-close-left =
            SP.close-lim-from-late
              (S.ι (q k)) q̂ left-witness Kq qc leg k Bq≤k
              (S.isRefl∼̂ₛ (S.ι (q k))
                (((leg /4₊) /4₊) /4₊))

          rk-close-right :
            S.ι (r k) S.∼̂ₛ[ leg ] presentedReal p'
          rk-close-right =
            SP.close-lim-from-late
              (S.ι (r k)) r̂ right-witness Kr rc leg k Br≤k
              (S.isRefl∼̂ₛ (S.ι (r k))
                (((leg /4₊) /4₊) /4₊))

          qk-close-rk : S.ι (q k) S.∼̂ₛ[ leg ] S.ι (r k)
          qk-close-rk =
            subst2 (S._∼̂ₛ[ leg ]_)
              (cong S.ι (interleave-even q r k))
              (cong S.ι (interleave-odd q r k))
              (jc leg (ℕ.doubleℕ k) (suc (ℕ.doubleℕ k))
                (ℕ.≤-trans Bj≤k (n≤double k))
                (ℕ.≤-trans Bj≤k
                  (ℕ.≤-trans (n≤double k) ℕ.≤-sucℕ)))


-- Conversely, two presentations of the same sequential real have Cauchy
-- interleaving.  This direction is what makes the mapped result independent
-- of the selected presentation.

presentedReal≡→interleavingCauchy : ∀ p p' →
  presentedReal p ≡ presentedReal p' → InterleavingCauchy p p'
presentedReal≡→interleavingCauchy p p' same =
  C.injectedSeqWitness→rational (interleave q r)
    (PT.rec squash₁ with-left left-witness)
  where
  q = sequence p
  r = sequence p'

  q̂ r̂ joined̂ : ℕ → S.ℭ̂ₛ
  q̂ = S.ι ∘ q
  r̂ = S.ι ∘ r
  joined̂ = S.ι ∘ interleave q r

  left-witness : S.SeqWitness q̂
  left-witness = C.rationalSeqWitness→injected q (cauchy p)

  right-witness : S.SeqWitness r̂
  right-witness = C.rationalSeqWitness→injected r (cauchy p')

  with-left : S.CauchySeq q̂ → S.SeqWitness joined̂
  with-left (Kq , qc) = PT.rec squash₁ with-right right-witness
    where
    with-right : S.CauchySeq r̂ → S.SeqWitness joined̂
    with-right (Kr , rc) =
      ∣ modulus , close ∣₁
      where
      modulus : ℚ₊ → ℕ
      modulus ε = ℕ.doubleℕ
        (ℕ.max
          (Kq ((((ε /4₊) /4₊) /4₊)))
          (Kr ((((ε /4₊) /4₊) /4₊))))

      close : ∀ ε m n →
        modulus ε ℕ.≤ m → modulus ε ℕ.≤ n →
        joined̂ m S.∼̂ₛ[ ε ] joined̂ n
      close ε m n late-m late-n
        with paritySplit m | paritySplit n
      ... | even i | even j =
        subst2 (S._∼̂ₛ[ ε ]_)
          (sym (cong S.ι (interleave-even q r i)))
          (sym (cong S.ι (interleave-even q r j)))
          (connect (q-close i i-late) left-refl
            (q-close j j-late))
        where
        leg = ε /4₊
        Bq = Kq ((leg /4₊) /4₊)
        Br = Kr ((leg /4₊) /4₊)
        k = ℕ.max Bq Br

        Bq≤k : Bq ℕ.≤ k
        Bq≤k = ℕ.left-≤-max {m = Bq} {n = Br}

        i-late : Bq ℕ.≤ i
        i-late = ℕ.≤-trans Bq≤k (double≤double→≤ late-m)

        j-late : Bq ℕ.≤ j
        j-late = ℕ.≤-trans Bq≤k (double≤double→≤ late-n)

        q-close : ∀ t → Bq ℕ.≤ t →
          S.ι (q t) S.∼̂ₛ[ leg ] presentedReal p
        q-close t late = SP.close-lim-from-late
          (S.ι (q t)) q̂ left-witness Kq qc leg t late
          (S.isRefl∼̂ₛ (S.ι (q t))
            (((leg /4₊) /4₊) /4₊))

        left-refl :
          presentedReal p S.∼̂ₛ[ leg ] presentedReal p
        left-refl = S.isRefl∼̂ₛ (presentedReal p) leg

        connect : ∀ {u v c d} →
          u S.∼̂ₛ[ leg ] c → c S.∼̂ₛ[ leg ] d →
          v S.∼̂ₛ[ leg ] d → u S.∼̂ₛ[ ε ] v
        connect u∼c c∼d v∼d =
          S.isMonotone∼̂ₛ< _ _ _ ε (tripleQuarter< ε)
            (S.tri∼ _ _ _ (leg +₊ leg) leg
              (S.tri∼ _ _ _ leg leg u∼c c∼d)
              (S.sym∼ _ _ leg v∼d))

      ... | even i | odd j =
        subst2 (S._∼̂ₛ[ ε ]_)
          (sym (cong S.ι (interleave-even q r i)))
          (sym (cong S.ι (interleave-odd q r j)))
          (connect (q-close i i-late) left-close-right
            (r-close j j-late))
        where
        leg = ε /4₊
        Bq = Kq ((leg /4₊) /4₊)
        Br = Kr ((leg /4₊) /4₊)
        k = ℕ.max Bq Br

        i-late : Bq ℕ.≤ i
        i-late = ℕ.≤-trans
          (ℕ.left-≤-max {m = Bq} {n = Br})
          (double≤double→≤ late-m)

        j-late : Br ℕ.≤ j
        j-late = ℕ.≤-trans
          (ℕ.right-≤-max {n = Br} {m = Bq})
          (double≤odd→≤ late-n)

        q-close : ∀ t → Bq ℕ.≤ t →
          S.ι (q t) S.∼̂ₛ[ leg ] presentedReal p
        q-close t late = SP.close-lim-from-late
          (S.ι (q t)) q̂ left-witness Kq qc leg t late
          (S.isRefl∼̂ₛ (S.ι (q t))
            (((leg /4₊) /4₊) /4₊))

        r-close : ∀ t → Br ℕ.≤ t →
          S.ι (r t) S.∼̂ₛ[ leg ] presentedReal p'
        r-close t late = SP.close-lim-from-late
          (S.ι (r t)) r̂ right-witness Kr rc leg t late
          (S.isRefl∼̂ₛ (S.ι (r t))
            (((leg /4₊) /4₊) /4₊))

        left-close-right :
          presentedReal p S.∼̂ₛ[ leg ] presentedReal p'
        left-close-right =
          subst (presentedReal p S.∼̂ₛ[ leg ]_)
            same (S.isRefl∼̂ₛ (presentedReal p) leg)

        connect : ∀ {u v c d} →
          u S.∼̂ₛ[ leg ] c → c S.∼̂ₛ[ leg ] d →
          v S.∼̂ₛ[ leg ] d → u S.∼̂ₛ[ ε ] v
        connect u∼c c∼d v∼d =
          S.isMonotone∼̂ₛ< _ _ _ ε (tripleQuarter< ε)
            (S.tri∼ _ _ _ (leg +₊ leg) leg
              (S.tri∼ _ _ _ leg leg u∼c c∼d)
              (S.sym∼ _ _ leg v∼d))

      ... | odd i | even j =
        subst2 (S._∼̂ₛ[ ε ]_)
          (sym (cong S.ι (interleave-odd q r i)))
          (sym (cong S.ι (interleave-even q r j)))
          (connect (r-close i i-late) right-close-left
            (q-close j j-late))
        where
        leg = ε /4₊
        Bq = Kq ((leg /4₊) /4₊)
        Br = Kr ((leg /4₊) /4₊)
        k = ℕ.max Bq Br

        i-late : Br ℕ.≤ i
        i-late = ℕ.≤-trans
          (ℕ.right-≤-max {n = Br} {m = Bq})
          (double≤odd→≤ late-m)

        j-late : Bq ℕ.≤ j
        j-late = ℕ.≤-trans
          (ℕ.left-≤-max {m = Bq} {n = Br})
          (double≤double→≤ late-n)

        q-close : ∀ t → Bq ℕ.≤ t →
          S.ι (q t) S.∼̂ₛ[ leg ] presentedReal p
        q-close t late = SP.close-lim-from-late
          (S.ι (q t)) q̂ left-witness Kq qc leg t late
          (S.isRefl∼̂ₛ (S.ι (q t))
            (((leg /4₊) /4₊) /4₊))

        r-close : ∀ t → Br ℕ.≤ t →
          S.ι (r t) S.∼̂ₛ[ leg ] presentedReal p'
        r-close t late = SP.close-lim-from-late
          (S.ι (r t)) r̂ right-witness Kr rc leg t late
          (S.isRefl∼̂ₛ (S.ι (r t))
            (((leg /4₊) /4₊) /4₊))

        right-close-left :
          presentedReal p' S.∼̂ₛ[ leg ] presentedReal p
        right-close-left = S.sym∼ _ _ leg
          (subst (presentedReal p S.∼̂ₛ[ leg ]_)
            same (S.isRefl∼̂ₛ (presentedReal p) leg))

        connect : ∀ {u v c d} →
          u S.∼̂ₛ[ leg ] c → c S.∼̂ₛ[ leg ] d →
          v S.∼̂ₛ[ leg ] d → u S.∼̂ₛ[ ε ] v
        connect u∼c c∼d v∼d =
          S.isMonotone∼̂ₛ< _ _ _ ε (tripleQuarter< ε)
            (S.tri∼ _ _ _ (leg +₊ leg) leg
              (S.tri∼ _ _ _ leg leg u∼c c∼d)
              (S.sym∼ _ _ leg v∼d))

      ... | odd i | odd j =
        subst2 (S._∼̂ₛ[ ε ]_)
          (sym (cong S.ι (interleave-odd q r i)))
          (sym (cong S.ι (interleave-odd q r j)))
          (connect (r-close i i-late) right-refl
            (r-close j j-late))
        where
        leg = ε /4₊
        Bq = Kq ((leg /4₊) /4₊)
        Br = Kr ((leg /4₊) /4₊)
        k = ℕ.max Bq Br

        Br≤k : Br ℕ.≤ k
        Br≤k = ℕ.right-≤-max {n = Br} {m = Bq}

        i-late : Br ℕ.≤ i
        i-late = ℕ.≤-trans Br≤k (double≤odd→≤ late-m)

        j-late : Br ℕ.≤ j
        j-late = ℕ.≤-trans Br≤k (double≤odd→≤ late-n)

        r-close : ∀ t → Br ℕ.≤ t →
          S.ι (r t) S.∼̂ₛ[ leg ] presentedReal p'
        r-close t late = SP.close-lim-from-late
          (S.ι (r t)) r̂ right-witness Kr rc leg t late
          (S.isRefl∼̂ₛ (S.ι (r t))
            (((leg /4₊) /4₊) /4₊))

        right-refl :
          presentedReal p' S.∼̂ₛ[ leg ] presentedReal p'
        right-refl = S.isRefl∼̂ₛ (presentedReal p') leg

        connect : ∀ {u v c d} →
          u S.∼̂ₛ[ leg ] c → c S.∼̂ₛ[ leg ] d →
          v S.∼̂ₛ[ leg ] d → u S.∼̂ₛ[ ε ] v
        connect u∼c c∼d v∼d =
          S.isMonotone∼̂ₛ< _ _ _ ε (tripleQuarter< ε)
            (S.tri∼ _ _ _ (leg +₊ leg) leg
              (S.tri∼ _ _ _ leg leg u∼c c∼d)
              (S.sym∼ _ _ leg v∼d))


mapInterleavingCauchy :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f)
    p p' → InterleavingCauchy p p' →
  InterleavingCauchy
    (mapRationalCauchyPresentation f maps p)
    (mapRationalCauchyPresentation f maps p')
mapInterleavingCauchy f maps p p' joined =
  subst C.RationalSeqWitness
    (sym (interleave-map f (sequence p) (sequence p')))
    (maps (interleave (sequence p) (sequence p')) joined)


mapsRationalCauchySequences→presentationIndependent :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) →
  IsPresentationIndependent f maps
mapsRationalCauchySequences→presentationIndependent
  f maps p p' same =
  interleavingCauchy→presentedReal≡
    (mapRationalCauchyPresentation f maps p)
    (mapRationalCauchyPresentation f maps p')
    (mapInterleavingCauchy f maps p p'
      (presentedReal≡→interleavingCauchy p p' same))


RationalCauchyPresentationOf : S.ℭ̂ₛ → Type₀
RationalCauchyPresentationOf x =
  Σ[ p ∈ RationalCauchyPresentation ]
    x ≡ presentedReal p


MerelyRationalCauchyPresented : S.ℭ̂ₛ → Type₀
MerelyRationalCauchyPresented x =
  ∥ RationalCauchyPresentationOf x ∥₁


isPropMerelyRationalCauchyPresented : ∀ x →
  isProp (MerelyRationalCauchyPresented x)
isPropMerelyRationalCauchyPresented x = squash₁


rationalIsMerelyPresented : ∀ q →
  MerelyRationalCauchyPresented (S.ι q)
rationalIsMerelyPresented q =
  ∣ constantPresentation q , ι≡presentedConstant q ∣₁


-- Since the mapped value is presentation-independent, a merely existing
-- rational presentation is sufficient.  This is recursion from a
-- propositional truncation into the set of sequential reals, not a choice of
-- an approximation sequence.

liftFromMereRationalCauchyPresentation :
  (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) →
  ∀ x → MerelyRationalCauchyPresented x → S.ℭ̂ₛ
liftFromMereRationalCauchyPresentation f maps x =
  PT.rec→Set S.isSetℭ̂ₛ from-presentation constant
  where
  from-presentation : RationalCauchyPresentationOf x → S.ℭ̂ₛ
  from-presentation (p , _) =
    liftFromRationalCauchyPresentation f maps p

  constant : ∀ u v → from-presentation u ≡ from-presentation v
  constant (p , x≡p) (p' , x≡p') =
    mapsRationalCauchySequences→presentationIndependent f maps
      p p' (sym x≡p ∙ x≡p')


liftFromMereRationalCauchyPresentation-rational :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) q →
  liftFromMereRationalCauchyPresentation f maps (S.ι q)
    (rationalIsMerelyPresented q) ≡ S.ι (f q)
liftFromMereRationalCauchyPresentation-rational =
  liftFromRationalCauchyPresentation-rational


record MerelyPresentedReal : Type₀ where

  no-eta-equality

  field
    real : S.ℭ̂ₛ
    hasPresentation : MerelyRationalCauchyPresented real


liftMerelyPresentedReal :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  MerelyPresentedReal → S.ℭ̂ₛ
liftMerelyPresentedReal f maps x =
  liftFromMereRationalCauchyPresentation f maps
    (x .MerelyPresentedReal.real)
    (x .MerelyPresentedReal.hasPresentation)


AllSequentialRealsMerelyPresented : Type₀
AllSequentialRealsMerelyPresented =
  ∀ x → MerelyRationalCauchyPresented x


-- This is the exact final bridge to an endomap of the original sequential
-- completion.  The construction above proves every other obligation from
-- `maps`; only mere rational presentability of every nested completion point
-- remains.

liftAllSequentialReals :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  AllSequentialRealsMerelyPresented → S.ℭ̂ₛ → S.ℭ̂ₛ
liftAllSequentialReals f maps presentations x =
  liftFromMereRationalCauchyPresentation f maps x (presentations x)


liftAllSequentialReals-rational :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f)
    (presentations : AllSequentialRealsMerelyPresented) q →
  liftAllSequentialReals f maps presentations (S.ι q) ≡ S.ι (f q)
liftAllSequentialReals-rational f maps presentations q =
  PT.elim
    {P = λ witness →
      liftFromMereRationalCauchyPresentation f maps (S.ι q) witness
        ≡ S.ι (f q)}
    (λ _ → S.isSetℭ̂ₛ _ _)
    (λ where
      (p , ιq≡p) →
        mapsRationalCauchySequences→presentationIndependent f maps
          p (constantPresentation q)
          (sym ιq≡p ∙ ι≡presentedConstant q)
        ∙ liftFromRationalCauchyPresentation-rational f maps q)
    (presentations (S.ι q))


RationalCauchyPresentedReal : Type₀
RationalCauchyPresentedReal =
  RationalCauchyPresentation // InterleavingCauchy


rationalPresentedReal : ℚ → RationalCauchyPresentedReal
rationalPresentedReal q = SQ.[ constantPresentation q ]


presentedRealQuotient : RationalCauchyPresentedReal → S.ℭ̂ₛ
presentedRealQuotient = SQ.rec S.isSetℭ̂ₛ presentedReal
  interleavingCauchy→presentedReal≡


presentedRealQuotient-rational : ∀ q →
  presentedRealQuotient (rationalPresentedReal q) ≡ S.ι q
presentedRealQuotient-rational q =
  constantLimit≡ι q
    (C.rationalSeqWitness→injected
      (constantSequence q) (constantRationalWitness q))


liftRationalCauchyPresentedReal :
  (f : ℚ → ℚ) → C.MapsRationalCauchySequences f →
  RationalCauchyPresentedReal → RationalCauchyPresentedReal
liftRationalCauchyPresentedReal f maps =
  SQ.rec SQ.squash/
    (λ p → SQ.[ mapRationalCauchyPresentation f maps p ])
    (λ p p' joined →
      SQ.eq/ _ _ (mapInterleavingCauchy f maps p p' joined))


liftRationalCauchyPresentedReal-rational :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) q →
  liftRationalCauchyPresentedReal f maps (rationalPresentedReal q) ≡
    rationalPresentedReal (f q)
liftRationalCauchyPresentedReal-rational f maps q =
  SQ.eq/ _ _
    (presentedReal≡→interleavingCauchy
      (mapRationalCauchyPresentation f maps (constantPresentation q))
      (constantPresentation (f q))
      (liftFromRationalCauchyPresentation-rational f maps q
        ∙ ι≡presentedConstant (f q)))


presentedRealQuotient-lift :
  ∀ (f : ℚ → ℚ) (maps : C.MapsRationalCauchySequences f) p →
  presentedRealQuotient
    (liftRationalCauchyPresentedReal f maps SQ.[ p ]) ≡
  liftFromRationalCauchyPresentation f maps p
presentedRealQuotient-lift f maps p = refl
