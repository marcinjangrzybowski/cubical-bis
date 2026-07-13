module Cubical.HITs.CauchyReals.Bisection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.RationalsImports

open import Cubical.Data.Rationals.Bisection as ℚB
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (_／₊_; _⁻¹₊)

open import Cubical.HITs.CauchyReals.Aproximations

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals


elimInClampsℚ : ∀ {ℓ} {P : ℚ → Type ℓ} → ∀ L U → L ℚ.≤ U →
  (∀ x → x ∈ ℚ.ℚintervalℙ L U → P x) →
  ∀ x → P (ℚ.clamp L U x)
elimInClampsℚ L U L≤U X x =
  X _ (ℚ.clam∈ℚintervalℙ L U L≤U x)

elimInClampsᵣ : ∀ {ℓ} {P : ℝ → Type ℓ} → ∀ L U →
  (∀ x → P (clampᵣ L U x)) →
  ∀ x → x ∈ intervalℙ L U → P x
elimInClampsᵣ {P = P} L U X x x∈ =
  subst P (sym (∈ℚintervalℙ→clampᵣ≡ L U x x∈)) (X x)

clampᵣ∈intervalℙ : ∀ L U → L ≤ᵣ U → ∀ x →
  clampᵣ L U x ∈ intervalℙ L U
clampᵣ∈intervalℙ L U L≤U x =
  ≤clampᵣ L U x L≤U , clamp≤ᵣ L U x

Lipschitz-ℚ→ℚℙ : ℚ₊ → (P : ℙ ℚ) → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚℙ L P f =
  ∀ q → q ∈ P → ∀ r → r ∈ P → (ε : ℚ₊) →
    abs (q ℚ.- r) ℚ.< fst ε →
    abs (f q ℚ.- f r) ℚ.< fst (L ·₊ ε)

-- Previously in Cubical.HITs.CauchyReals.Bisect.
Lipschitz-ℚ→ℝ' : ℚ₊ → (ℚ → ℝ) → Type
Lipschitz-ℚ→ℝ' L f =
  ∀ q r → absᵣ (f q -ᵣ f r) ≤ᵣ rat (fst L ℚ.· abs (q ℚ.- r))

Lipschitz-ℚ→ℝ'→Lipschitz-ℚ→ℝ :
  ∀ L f → Lipschitz-ℚ→ℝ' L f → Lipschitz-ℚ→ℝ L f
Lipschitz-ℚ→ℝ'→Lipschitz-ℚ→ℝ L f lf q r ε -ε<q-r q-r<ε =
  invEq (∼≃abs<ε _ _ _)
    (isTrans≤<ᵣ _ _ _ (lf q r)
      (<ℚ→<ᵣ _ _
        (ℚ.<-o· _ _ (fst L) (snd L)
          (absFrom<×< (fst ε) (q ℚ.- r) -ε<q-r q-r<ε))))

Lipschitz-ℚ→ℚℙ< : ℚ₊ → (P : ℙ ℚ) → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚℙ< L P f =
  ∀ q → q ∈ P → ∀ r → r ∈ P → r ℚ.< q →
    abs (f q ℚ.- f r) ℚ.≤ fst L ℚ.· (q ℚ.- r)

Lipschitz-ℚ→ℚℙ<→Lipschitz-ℚ→ℚℙ :
  ∀ L P f → Lipschitz-ℚ→ℚℙ< L P f → Lipschitz-ℚ→ℚℙ L P f
Lipschitz-ℚ→ℚℙ<→Lipschitz-ℚ→ℚℙ L P f X q q∈ r r∈ ε u
  with ℚ.Dichotomyℚ q r
... | inr r<q =
  ℚ.isTrans≤< _ _ _
    (X q q∈ r r∈ r<q)
    (ℚ.<-o· _ _ (fst L) (snd L)
      (subst (ℚ._< fst ε)
        (0<→abs≡id (q ℚ.- r) (ℚ.-< r q r<q))
        u))
... | inl q≤r with ℚ.≤→≡⊎< q r q≤r
... | inl q≡r =
  subst (λ z → abs (f z ℚ.- f r) ℚ.< fst (L ·₊ ε)) (sym q≡r)
    (subst (ℚ._< fst (L ·₊ ε))
      (cong abs (sym (ℚ.+InvR (f r))))
      (snd (L ·₊ ε)))
... | inr q<r =
  subst (ℚ._< fst (L ·₊ ε))
    (sym (abs-Comm (f q) (f r)))
    (ℚ.isTrans≤< _ _ _
      (X r r∈ q q∈ q<r)
      (ℚ.<-o· _ _ (fst L) (snd L)
        (subst (ℚ._< fst ε)
          (0<→abs≡id (r ℚ.- q) (ℚ.-< q r q<r))
          (subst (ℚ._< fst ε) (abs-Comm q r) u))))

Lipschitz-ℚ→ℚℙ→Lipschitz-ℚ→ℝℙ :
  ∀ L a b f → Lipschitz-ℚ→ℚℙ L (ℚ.ℚintervalℙ a b) f →
  Lipschitz-ℚ→ℝℙ L (intervalℙ (rat a) (rat b)) (λ q _ → rat (f q))
Lipschitz-ℚ→ℚℙ→Lipschitz-ℚ→ℝℙ L a b f fLip q q∈ r r∈ ε q-r<ε =
  isTrans≡<ᵣ _ _ _
    (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ-rat _)
    (<ℚ→<ᵣ _ _
      (fLip q (∈intervalℙ→∈ℚintervalℙ a b q q∈)
        r (∈intervalℙ→∈ℚintervalℙ a b r r∈) ε q-r<ε))

opaque
 unfolding minᵣ
 continuousMapsInterval :
   ∀ (f : ℝ → ℝ) → IsContinuous f →
   ∀ a b → a ℚ.≤ b → ∀ L U → L ≤ᵣ U →
   (∀ x → rat x ∈ intervalℙ (rat a) (rat b) →
      f (rat x) ∈ intervalℙ L U) →
   ∀ x → x ∈ intervalℙ (rat a) (rat b) → f x ∈ intervalℙ L U
 continuousMapsInterval f fC a b a≤b L U L≤U mapsℚ =
   elimInClampsᵣ (rat a) (rat b) λ x →
     subst-∈ (intervalℙ L U) (sym (clampEq x))
       (clampᵣ∈intervalℙ L U L≤U (f (clampᵣ (rat a) (rat b) x)))
   where
   clampEq : ∀ x →
     f (clampᵣ (rat a) (rat b) x) ≡
     clampᵣ L U (f (clampᵣ (rat a) (rat b) x))
   clampEq =
     ≡Continuous _ _
       (IsContinuous∘ _ _ fC (IsContinuousClamp (rat a) (rat b)))
       (IsContinuous∘ _ _
         (IsContinuousClamp L U)
         (IsContinuous∘ _ _ fC (IsContinuousClamp (rat a) (rat b))))
       (λ r →
         let q = ℚ.clamp a b r
             q∈ = ℚ.clam∈ℚintervalℙ a b a≤b r
             clampPath = clampᵣ-rat a b r
             ratCase =
               ∈ℚintervalℙ→clampᵣ≡ L U (f (rat q))
                 (mapsℚ q (∈ℚintervalℙ→∈intervalℙ a b q q∈))
         in cong f clampPath ∙ ratCase
            ∙ cong (clampᵣ L U ∘ f) (sym clampPath))


module InverseBisection
  (a b : ℚ)
  (a<b : a ℚ.< b)
  (fℚ : ℚ → ℚ)
  where

  module QB = ℚB.ℚIncrFunBisectFamily a b a<b fℚ

  inverseSeq : ℚ → ℕ → ℝ
  inverseSeq y n = rat (QB.bs y n)

  inverseSeqCauchy : ∀ y → IsCauchySequence' (inverseSeq y)
  inverseSeqCauchy y ε =
    map-snd
      (λ X m n N<n N<m →
        isTrans≡<ᵣ _ _ _
          (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ-rat _)
          (<ℚ→<ᵣ _ _ (X m n N<n N<m)))
      (QB.Run.isCauchySequenceSolve y ε)

  inverseℚ : ℚ → ℝ
  inverseℚ y = fromCauchySequence' (inverseSeq y) (inverseSeqCauchy y)

  inverseℚ∈ : ∀ y → inverseℚ y ∈ intervalℙ (rat a) (rat b)
  inverseℚ∈ y =
      ≤lim a _ _
        (λ δ →
          ≤ℚ→≤ᵣ a (QB.bs y (suc (fst (inverseSeqCauchy y δ))))
            (QB.a≤bs y (suc (fst (inverseSeqCauchy y δ)))))
    , lim≤ b _ _
        (λ δ →
          ≤ℚ→≤ᵣ (QB.bs y (suc (fst (inverseSeqCauchy y δ)))) b
            (QB.bs≤b y (suc (fst (inverseSeqCauchy y δ)))))

  module LowerSlope (L : ℚ₊) (slope : QB.SlopeBoundedBelow L) where

    targetLower targetUpper : ℚ
    targetLower = fℚ a
    targetUpper = fℚ b

    targetLower<targetUpper : targetLower ℚ.< targetUpper
    targetLower<targetUpper =
      ℚ.<minus→< targetLower targetUpper
        (ℚ.isTrans<≤ _ _ _
          (ℚ.·0< (fst L) (b ℚ.- a)
            (snd L)
            (ℚ.<→<minus a b a<b))
          (slope a b
            (ℚ.isRefl≤ a)
            (ℚ.<Weaken≤ a b a<b)
            (ℚ.isRefl≤ b)))

    targetLower≤targetUpper : targetLower ℚ.≤ targetUpper
    targetLower≤targetUpper =
      ℚ.<Weaken≤ targetLower targetUpper targetLower<targetUpper

    TargetIntervalℙ : ℙ ℝ
    TargetIntervalℙ = intervalℙ (rat targetLower) (rat targetUpper)

    targetℚ∈→brackets : ∀ y → rat y ∈ TargetIntervalℙ → QB.BracketsTarget y
    targetℚ∈→brackets y y∈ =
      ≤ᵣ→≤ℚ _ _ (fst y∈) ,
      ≤ᵣ→≤ℚ _ _ (snd y∈)

    inverseℚOnTarget : ∀ y → rat y ∈ TargetIntervalℙ → ℝ
    inverseℚOnTarget y _ = inverseℚ y

    inverseℚOnTarget∈ :
      ∀ y y∈ → inverseℚOnTarget y y∈ ∈ intervalℙ (rat a) (rat b)
    inverseℚOnTarget∈ y _ = inverseℚ∈ y

    private
      nonNegSlopeTerm : ∀ x x' → x ℚ.≤ x' →
        0 ℚ.≤ fst L ℚ.· (x' ℚ.- x)
      nonNegSlopeTerm x x' x≤x' =
        subst2 ℚ._≤_ ℚ! ℚ!
          (ℚ.≤-·o 0 (x' ℚ.- x) (fst L)
            (ℚ.<Weaken≤ 0 (fst L) (snd L))
            (ℚ.-≤ x x' x≤x'))

    sourceℚ∈→targetℚ∈ :
      ∀ x → x ∈ ℚ.ℚintervalℙ a b →
      fℚ x ∈ ℚ.ℚintervalℙ targetLower targetUpper
    sourceℚ∈→targetℚ∈ x (a≤x , x≤b) =
        ℚ.≤minus→≤ targetLower (fℚ x)
          (ℚ.isTrans≤ _ _ _
            (nonNegSlopeTerm a x a≤x)
            (slope a x (ℚ.isRefl≤ a) a≤x x≤b))
      , ℚ.≤minus→≤ (fℚ x) targetUpper
          (ℚ.isTrans≤ _ _ _
            (nonNegSlopeTerm x b x≤b)
            (slope x b a≤x x≤b (ℚ.isRefl≤ b)))

    inverseℚOnTarget-Lipschitz :
      Lipschitz-ℚ→ℝℙ (2 ·₊ (L ⁻¹₊)) TargetIntervalℙ inverseℚOnTarget
    inverseℚOnTarget-Lipschitz q q∈ r r∈ ε q-r<ε =
      fst (∼≃abs<ε _ _ _) $
        subst2 (λ u v → u ∼[ (2 ·₊ (L ⁻¹₊)) ·₊ ε ] v)
          (sym qSpeedup≡)
          (sym rSpeedup≡)
          limClose
      where
      qBrackets : QB.BracketsTarget q
      qBrackets = targetℚ∈→brackets q q∈

      rBrackets : QB.BracketsTarget r
      rBrackets = targetℚ∈→brackets r r∈

      base slack δ : ℚ₊
      base = (L ⁻¹₊) ·₊ ε
      slack = base /4₊
      δ = slack

      closeε : ℚ₊
      closeε =
        fst ((2 ·₊ (L ⁻¹₊)) ·₊ ε) ℚ.- (fst δ ℚ.+ fst δ) ,
        subst (0 ℚ.<_) ℚ! (snd (base +₊ (base /2₊)))

      limitEstimate :
        Σ[ N ∈ ℕ ] (∀ n m → N ℕ.< n → N ℕ.< m →
          abs (QB.bs q n ℚ.- QB.bs r m)
            ℚ.< (abs (q ℚ.- r) ／₊ L) ℚ.+ fst slack)
      limitEstimate =
        QB.bsLimitLipschitz L slope q r qBrackets rBrackets slack

      N : ℕ
      N = fst limitEstimate

      close :
        ∀ n m → N ℕ.< n → N ℕ.< m →
          abs (QB.bs q n ℚ.- QB.bs r m)
            ℚ.< (abs (q ℚ.- r) ／₊ L) ℚ.+ fst slack
      close = snd limitEstimate

      qIcs rIcs : IsCauchySequence' _
      qIcs = inverseSeqCauchy q
      rIcs = inverseSeqCauchy r

      qSpd rSpd : ℚ₊ → ℕ
      qSpd θ = N ℕ.+ fst (qIcs θ)
      rSpd θ = N ℕ.+ fst (rIcs θ)

      qIcsSpd : IsCauchySequence' (inverseSeq q)
      qIcsSpd =
        cauchySequenceSpeedup (inverseSeq q) qIcs qSpd
          (λ _ → ℕ.≤SumRight)

      rIcsSpd : IsCauchySequence' (inverseSeq r)
      rIcsSpd =
        cauchySequenceSpeedup (inverseSeq r) rIcs rSpd
          (λ _ → ℕ.≤SumRight)

      qSpeedup≡ : inverseℚ q ≡ fromCauchySequence' (inverseSeq q) qIcsSpd
      qSpeedup≡ =
        cauchySequenceSpeedup≡ (inverseSeq q) qIcs qSpd
          (λ _ → ℕ.≤SumRight)

      rSpeedup≡ : inverseℚ r ≡ fromCauchySequence' (inverseSeq r) rIcsSpd
      rSpeedup≡ =
        cauchySequenceSpeedup≡ (inverseSeq r) rIcs rSpd
          (λ _ → ℕ.≤SumRight)
      

      N<qδ : N ℕ.< suc (qSpd δ)
      N<qδ = ℕ.suc-≤-suc ℕ.≤SumLeft

      N<rδ : N ℕ.< suc (rSpd δ)
      N<rδ = ℕ.suc-≤-suc ℕ.≤SumLeft

      closeBound :
        (abs (q ℚ.- r) ／₊ L) ℚ.+ fst slack ℚ.< fst closeε
      closeBound =
        ℚ.isTrans< _ _ _
          (ℚ.<-+o _ _ (fst slack) absDiv<base)
          base+slack<closeε
        where
        absDiv<base : abs (q ℚ.- r) ／₊ L ℚ.< fst base
        absDiv<base =
          subst2 ℚ._<_ ℚ! ℚ!
            (ℚ.<-o· (abs (q ℚ.- r)) (fst ε) (fst (L ⁻¹₊))
              (snd (L ⁻¹₊)) q-r<ε)

        base+slack<closeε : fst base ℚ.+ fst slack ℚ.< fst closeε
        base+slack<closeε =
          subst2 ℚ._<_
            (ℚ.+IdR (fst base ℚ.+ fst slack))
            ℚ!
            (ℚ.<-o+ 0 (fst (base /4₊)) (fst base ℚ.+ fst slack)
              (snd (base /4₊)))

      closeAtδ :
        inverseSeq q (suc (qSpd δ)) ∼[ closeε ]
        inverseSeq r (suc (rSpd δ))
      closeAtδ =
        rat-rat-fromAbs _ _ closeε
          (ℚ.isTrans< _ _ _
            (close (suc (qSpd δ)) (suc (rSpd δ)) N<qδ N<rδ)
            closeBound)

      limClose :
        fromCauchySequence' (inverseSeq q) qIcsSpd
          ∼[ (2 ·₊ (L ⁻¹₊)) ·₊ ε ]
        fromCauchySequence' (inverseSeq r) rIcsSpd
      limClose =
        lim-lim _ _ ((2 ·₊ (L ⁻¹₊)) ·₊ ε) δ δ
          (fromCauchySequence'-isCA _ qIcsSpd)
          (fromCauchySequence'-isCA _ rIcsSpd)
          (snd closeε)
          closeAtδ

    inverseℚExtended :
      Σ[ f' ∈ (ℚ → ℝ) ]
        (Lipschitz-ℚ→ℝ (2 ·₊ (L ⁻¹₊)) f'
        × (∀ y y∈ → f' y ≡ inverseℚOnTarget y y∈))
    inverseℚExtended =
      extend-Lipshitzℚ→ℝ (2 ·₊ (L ⁻¹₊))
        targetLower targetUpper targetLower≤targetUpper
        inverseℚOnTarget inverseℚOnTarget-Lipschitz

    inverseℝ-L : Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (2 ·₊ (L ⁻¹₊)))
    inverseℝ-L =
      fromLipschitz (2 ·₊ (L ⁻¹₊))
        (fst inverseℚExtended , fst (snd inverseℚExtended))

    inverseℝ : ℝ → ℝ
    inverseℝ = fst inverseℝ-L

    inverseℝ-lip : Lipschitz-ℝ→ℝ (2 ·₊ (L ⁻¹₊)) inverseℝ
    inverseℝ-lip = snd inverseℝ-L

    inverseℝ-cont : IsContinuous inverseℝ
    inverseℝ-cont =
      Lipschitz→IsContinuous (2 ·₊ (L ⁻¹₊)) inverseℝ inverseℝ-lip

    inverseℝ-rat :
      ∀ y y∈ → inverseℝ (rat y) ≡ inverseℚ y
    inverseℝ-rat y y∈ =
      fromLipschitz-rat ∙ snd (snd inverseℚExtended) y y∈

    inverseℝ∈ :
      ∀ y → y ∈ TargetIntervalℙ → inverseℝ y ∈ intervalℙ (rat a) (rat b)
    inverseℝ∈ =
      continuousMapsInterval inverseℝ inverseℝ-cont
        targetLower targetUpper targetLower≤targetUpper
        (rat a) (rat b) (≤ℚ→≤ᵣ a b (ℚ.<Weaken≤ a b a<b))
        λ q q∈ →
          subst-∈ (intervalℙ (rat a) (rat b)) (sym (inverseℝ-rat q q∈))
            (inverseℚ∈ q)

    inverseℝ-ℚApproxℙ :
      ℚApproxℙ' TargetIntervalℙ (intervalℙ (rat a) (rat b))
        (λ y y∈ → inverseℝ y , inverseℝ∈ y y∈)
    inverseℝ-ℚApproxℙ y y∈ =
        (λ ε → QB.bs y (suc (fst (inverseSeqCauchy y ε))))
      , (λ ε →
          ∈ℚintervalℙ→∈intervalℙ a b _
            (QB.a≤bs y (suc (fst (inverseSeqCauchy y ε))) ,
             QB.bs≤b y (suc (fst (inverseSeqCauchy y ε)))))
      , fromCauchySequence'-isCA (inverseSeq y) (inverseSeqCauchy y)
      , sym (inverseℝ-rat y y∈)

    private
      pointInOwnBisectionBracket :
        ∀ x → x ∈ ℚ.ℚintervalℙ a b → ∀ n →
        (QB.bs (fℚ x) n ℚ.≤ x) × (x ℚ.≤ QB.bs↑ (fℚ x) n)
      pointInOwnBisectionBracket x (a≤x , x≤b) n =
          ℚ.≮→≥ x (QB.bs (fℚ x) n) bs≮x
        , ℚ.≮→≥ (QB.bs↑ (fℚ x) n) x x≮bs↑
        where
        xBrackets : QB.BracketsTarget (fℚ x)
        xBrackets = sourceℚ∈→targetℚ∈ x (a≤x , x≤b)

        bs≮x : ¬ (x ℚ.< QB.bs (fℚ x) n)
        bs≮x x<bs =
          let slope≤ =
                slope x (QB.bs (fℚ x) n)
                  a≤x
                  (ℚ.<Weaken≤ x (QB.bs (fℚ x) n) x<bs)
                  (QB.bs≤b (fℚ x) n)
              fbs-fx≤0 =
                ℚ.isTrans≤ _ _ _
                  (ℚ.≤-+o (fℚ (QB.bs (fℚ x) n)) (fℚ x) (ℚ.- fℚ x)
                    (QB.bs-lower-valid (fℚ x) (fst xBrackets) n))
                  (ℚ.≡Weaken≤ _ _ (ℚ.+InvR (fℚ x)))
              0<LΔ =
                ℚ.·0< (fst L) (QB.bs (fℚ x) n ℚ.- x)
                  (snd L)
                  (ℚ.<→<minus x (QB.bs (fℚ x) n) x<bs)
          in ℚ.≤→≯ _ _ (ℚ.isTrans≤ _ _ _ slope≤ fbs-fx≤0) 0<LΔ

        x≮bs↑ : ¬ (QB.bs↑ (fℚ x) n ℚ.< x)
        x≮bs↑ bs↑<x =
          let slope≤ =
                slope (QB.bs↑ (fℚ x) n) x
                  (QB.a≤bs↑ (fℚ x) n)
                  (ℚ.<Weaken≤ (QB.bs↑ (fℚ x) n) x bs↑<x)
                  x≤b
              fx-fbs↑≤0 =
                ℚ.isTrans≤ _ _ _
                  (ℚ.≤-+o (fℚ x) (fℚ (QB.bs↑ (fℚ x) n))
                    (ℚ.- fℚ (QB.bs↑ (fℚ x) n))
                    (QB.bs↑-upper-valid (fℚ x) (snd xBrackets) n))
                  (ℚ.≡Weaken≤ _ _ (ℚ.+InvR (fℚ (QB.bs↑ (fℚ x) n))))
              0<LΔ =
                ℚ.·0< (fst L) (x ℚ.- QB.bs↑ (fℚ x) n)
                  (snd L)
                  (ℚ.<→<minus (QB.bs↑ (fℚ x) n) x bs↑<x)
          in ℚ.≤→≯ _ _ (ℚ.isTrans≤ _ _ _ slope≤ fx-fbs↑≤0) 0<LΔ

      bsDistanceToPoint≤width :
        ∀ x x∈ n →
        abs (QB.bs (fℚ x) n ℚ.- x) ℚ.≤ QB.width (fℚ x) n
      bsDistanceToPoint≤width x x∈ n =
        absFrom≤×≤ (QB.width (fℚ x) n)
          (QB.bs (fℚ x) n ℚ.- x)
          lower≤ upper≤
        where
        bs≤x : QB.bs (fℚ x) n ℚ.≤ x
        bs≤x = fst (pointInOwnBisectionBracket x x∈ n)

        x≤bs↑ : x ℚ.≤ QB.bs↑ (fℚ x) n
        x≤bs↑ = snd (pointInOwnBisectionBracket x x∈ n)

        lower≤ : ℚ.- QB.width (fℚ x) n ℚ.≤ QB.bs (fℚ x) n ℚ.- x
        lower≤ =
          QB.diff≤→-≤diff x (QB.bs (fℚ x) n) (QB.width (fℚ x) n)
            (ℚ.≤-+o x (QB.bs↑ (fℚ x) n) (ℚ.- QB.bs (fℚ x) n) x≤bs↑)

        upper≤ : QB.bs (fℚ x) n ℚ.- x ℚ.≤ QB.width (fℚ x) n
        upper≤ =
          ℚ.isTrans≤ _ _ _
            (ℚ.≤-+o (QB.bs (fℚ x) n) x (ℚ.- x) bs≤x)
            (ℚ.isTrans≤ _ _ _
              (ℚ.≡Weaken≤ _ _ (ℚ.+InvR x))
              (QB.widthNonNeg (fℚ x) n))

    inverseℚ-left-rat :
      ∀ x → (x∈ : x ∈ ℚ.ℚintervalℙ a b) →
      inverseℚ (fℚ x) ≡ rat x
    inverseℚ-left-rat x x∈ =
      fromCauchySequence'≡ (inverseSeq (fℚ x)) (inverseSeqCauchy (fℚ x)) (rat x)
        λ ε →
          let (N , width<ε) = QB.widthEventually< (fℚ x) ε
          in ∣ N , (λ n N<n →
            isTrans≡<ᵣ _ _ _
              (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ-rat _)
              (<ℚ→<ᵣ _ _
                (ℚ.isTrans≤< _ _ _
                  (bsDistanceToPoint≤width x x∈ n)
                  (width<ε n N<n)))) ∣₁

    module RealFunction
      (M : ℚ₊)
      (F : ℝ → ℝ)
      (F-lip : Lipschitz-ℝ→ℝ M F)
      (fℚ-lip : Lipschitz-ℚ→ℚℙ M (ℚ.ℚintervalℙ a b) fℚ)
      (F-rat : ∀ x → rat x ∈ intervalℙ (rat a) (rat b) →
        F (rat x) ≡ rat (fℚ x))
      where

      F-cont : IsContinuous F
      F-cont = Lipschitz→IsContinuous M F F-lip

      F∈ : ∀ x → x ∈ intervalℙ (rat a) (rat b) → F x ∈ TargetIntervalℙ
      F∈ =
        continuousMapsInterval F F-cont a b (ℚ.<Weaken≤ a b a<b)
          (rat targetLower) (rat targetUpper)
          (≤ℚ→≤ᵣ targetLower targetUpper targetLower≤targetUpper)
          λ q q∈ →
            subst-∈ TargetIntervalℙ (sym (F-rat q q∈))
              (∈ℚintervalℙ→∈intervalℙ targetLower targetUpper (fℚ q)
                (sourceℚ∈→targetℚ∈ q (∈intervalℙ→∈ℚintervalℙ a b q q∈)))

      private
        imageDistanceToTarget≤ImageWidth :
          ∀ y → QB.BracketsTarget y → ∀ n →
          abs (fℚ (QB.bs y n) ℚ.- y)
            ℚ.≤ fℚ (QB.bs↑ y n) ℚ.- fℚ (QB.bs y n)
        imageDistanceToTarget≤ImageWidth y y∈ n =
          absFrom≤×≤ imageWidth (fbs ℚ.- y) lower≤ upper≤
          where
          fbs fbs↑ imageWidth : ℚ
          fbs = fℚ (QB.bs y n)
          fbs↑ = fℚ (QB.bs↑ y n)
          imageWidth = fbs↑ ℚ.- fbs

          fbs≤y : fbs ℚ.≤ y
          fbs≤y = QB.bs-lower-valid y (fst y∈) n

          y≤fbs↑ : y ℚ.≤ fbs↑
          y≤fbs↑ = QB.bs↑-upper-valid y (snd y∈) n

          fbs≤fbs↑ : fbs ℚ.≤ fbs↑
          fbs≤fbs↑ = ℚ.isTrans≤ _ _ _ fbs≤y y≤fbs↑

          lower≤ : ℚ.- imageWidth ℚ.≤ fbs ℚ.- y
          lower≤ =
            QB.diff≤→-≤diff y fbs imageWidth
              (ℚ.≤-+o y fbs↑ (ℚ.- fbs) y≤fbs↑)

          upper≤ : fbs ℚ.- y ℚ.≤ imageWidth
          upper≤ =
            ℚ.isTrans≤ _ _ _
              (ℚ.≤-+o fbs y (ℚ.- y) fbs≤y)
              (ℚ.isTrans≤ _ _ _
                (ℚ.≡Weaken≤ _ _ (ℚ.+InvR y))
                (ℚ.-≤ fbs fbs↑ fbs≤fbs↑))

        imageWidthSmall :
          ∀ y n ε → QB.width y n ℚ.< fst ((M ⁻¹₊) ·₊ ε) →
          abs (fℚ (QB.bs↑ y n) ℚ.- fℚ (QB.bs y n)) ℚ.< fst ε
        imageWidthSmall y n ε width< =
          subst (abs (fℚ (QB.bs↑ y n) ℚ.- fℚ (QB.bs y n)) ℚ.<_)
            (ℚ.y·[x/y] M (fst ε))
            (fℚ-lip
              (QB.bs↑ y n) (QB.a≤bs↑ y n , QB.bs↑≤b y n)
              (QB.bs y n) (QB.a≤bs y n , QB.bs≤b y n)
              ((M ⁻¹₊) ·₊ ε)
              (subst (λ z → z ℚ.< fst ((M ⁻¹₊) ·₊ ε))
                (sym (0≤→abs≡id (QB.bs↑ y n ℚ.- QB.bs y n)
                  (QB.widthNonNeg y n)))
                width<))

        targetConvergence :
          ∀ y → (y∈ : rat y ∈ TargetIntervalℙ) →
          ∀ ε → ∃[ N ∈ ℕ ] (∀ n → N ℕ.< n →
            absᵣ ((F ∘ inverseSeq y) n -ᵣ rat y) <ᵣ rat (fst ε))
        targetConvergence y y∈ ε =
          let yBrackets = targetℚ∈→brackets y y∈
              (N , width<) = QB.widthEventually< y ((M ⁻¹₊) ·₊ ε)
          in ∣ N , (λ n N<n →
            let bs∈ = ∈ℚintervalℙ→∈intervalℙ a b (QB.bs y n)
                  (QB.a≤bs y n , QB.bs≤b y n)
                rewriteF = F-rat (QB.bs y n) bs∈
                imageWidth< =
                  ℚ.isTrans≤< _ _ _
                    (≤abs (fℚ (QB.bs↑ y n) ℚ.- fℚ (QB.bs y n)))
                    (imageWidthSmall y n ε (width< n N<n))
                target< =
                  ℚ.isTrans≤< _ _ _
                    (imageDistanceToTarget≤ImageWidth y yBrackets n)
                    imageWidth<
            in isTrans≡<ᵣ _ _ _
                (cong absᵣ (cong₂ _-ᵣ_ rewriteF refl)
                  ∙ cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ-rat _)
                (<ℚ→<ᵣ _ _ target<)) ∣₁

      F-inverseℚ-rat :
        ∀ y → (y∈ : rat y ∈ TargetIntervalℙ) →
        F (inverseℚ y) ≡ rat y
      F-inverseℚ-rat y y∈ =
        snd mapped ∙
        fromCauchySequence'≡ (F ∘ inverseSeq y) (fst mapped) (rat y)
          (targetConvergence y y∈)
        where
        mapped =
          map-fromCauchySequence' M (inverseSeq y) (inverseSeqCauchy y) F F-lip

      F-inverseℝ-clamp :
        ∀ y → F (inverseℝ (clampᵣ (rat targetLower) (rat targetUpper) y))
          ≡ clampᵣ (rat targetLower) (rat targetUpper) y
      F-inverseℝ-clamp =
        ≡Continuous _ _
          (IsContinuous∘ _ _
            F-cont
            (IsContinuous∘ _ _
              inverseℝ-cont
              (IsContinuousClamp (rat targetLower) (rat targetUpper))))
          (IsContinuousClamp (rat targetLower) (rat targetUpper))
          rationalCase
        where
        rationalCase : ∀ r →
          F (inverseℝ (clampᵣ (rat targetLower) (rat targetUpper) (rat r)))
          ≡ clampᵣ (rat targetLower) (rat targetUpper) (rat r)
        rationalCase r =
          let q = ℚ.clamp targetLower targetUpper r
              q∈ℚ = ℚ.clam∈ℚintervalℙ targetLower targetUpper
                targetLower≤targetUpper r
              q∈ = ∈ℚintervalℙ→∈intervalℙ targetLower targetUpper q q∈ℚ
              clampPath = clampᵣ-rat targetLower targetUpper r
          in cong (F ∘ inverseℝ) clampPath
             ∙ cong F (inverseℝ-rat q q∈)
             ∙ F-inverseℚ-rat q q∈
             ∙ sym clampPath

      F-inverseℝ :
        ∀ y → y ∈ TargetIntervalℙ → F (inverseℝ y) ≡ y
      F-inverseℝ =
        elimInClampsᵣ (rat targetLower) (rat targetUpper)
          F-inverseℝ-clamp

      inverseℝ-F-clamp :
        ∀ x → inverseℝ (F (clampᵣ (rat a) (rat b) x))
          ≡ clampᵣ (rat a) (rat b) x
      inverseℝ-F-clamp =
        ≡Continuous _ _
          (IsContinuous∘ _ _
            inverseℝ-cont
            (IsContinuous∘ _ _ F-cont (IsContinuousClamp (rat a) (rat b))))
          (IsContinuousClamp (rat a) (rat b))
          rationalCase
        where
        rationalCase : ∀ r →
          inverseℝ (F (clampᵣ (rat a) (rat b) (rat r)))
          ≡ clampᵣ (rat a) (rat b) (rat r)
        rationalCase r =
          let q = ℚ.clamp a b r
              q∈ℚ = ℚ.clam∈ℚintervalℙ a b (ℚ.<Weaken≤ a b a<b) r
              q∈ = ∈ℚintervalℙ→∈intervalℙ a b q q∈ℚ
              fq∈ = ∈ℚintervalℙ→∈intervalℙ targetLower targetUpper (fℚ q)
                (sourceℚ∈→targetℚ∈ q q∈ℚ)
              clampPath = clampᵣ-rat a b r
          in cong (inverseℝ ∘ F) clampPath
             ∙ cong inverseℝ (F-rat q q∈)
             ∙ inverseℝ-rat (fℚ q) fq∈
             ∙ inverseℚ-left-rat q q∈ℚ
             ∙ sym clampPath

      inverseℝ-F :
        ∀ x → x ∈ intervalℙ (rat a) (rat b) → inverseℝ (F x) ≡ x
      inverseℝ-F =
        elimInClampsᵣ (rat a) (rat b) inverseℝ-F-clamp

      intervalIso :
        Iso (Σ ℝ (_∈ intervalℙ (rat a) (rat b)))
            (Σ ℝ (_∈ TargetIntervalℙ))
      intervalIso .Iso.fun (x , x∈) = F x , F∈ x x∈
      intervalIso .Iso.inv (y , y∈) = inverseℝ y , inverseℝ∈ y y∈
      intervalIso .Iso.sec (y , y∈) =
        Σ≡Prop (∈-isProp TargetIntervalℙ) (F-inverseℝ y y∈)
      intervalIso .Iso.ret (x , x∈) =
        Σ≡Prop (∈-isProp (intervalℙ (rat a) (rat b))) (inverseℝ-F x x∈)
