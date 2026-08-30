module Cubical.Data.Rationals.NatIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (⊎Iso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (prodIso ; Σ-cong-iso-fst)

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Bijections.Sum
open import Cubical.Data.Nat.Bijections.Product
open import Cubical.Data.Nat.Bijections.IncreasingFunction
open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Coprime

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ
  using (ℤ ; pos ; negsuc ; abs ; sign ; _·_ ; sign·abs)

open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.Base
import Cubical.Data.Rationals.Properties as ℚP


-- A decidable proposition on ℕ which contains 0 and has an element after
-- every index can be enumerated without repetitions.  Least-next search is
-- bounded by the supplied later element, so no choice principle is used.

private
  module BoundedLeast
    (P : ℕ → Type₀)
    (isPropP : ∀ n → isProp (P n))
    (decP : ∀ n → Dec (P n))
    where

    Candidate : ℕ → Type₀
    Candidate b = Σ[ n ∈ ℕ ] (n ≤ b) × P n

    NoCandidate : ℕ → Type₀
    NoCandidate b = ∀ n → n ≤ b → ¬ P n

    SearchResult : ℕ → Type₀
    SearchResult b =
      (Σ[ n ∈ ℕ ] ℕ.Minimal.Least P n × (n ≤ b)) ⊎ NoCandidate b

    searchUpTo : ∀ b → SearchResult b
    searchUpTo zero with decP zero
    ... | yes p = inl (zero , (p , λ n n<0 →
      ⊥.rec (ℕ.¬-<-zero n<0)) , ℕ.≤-refl)
    ... | no ¬p = inr λ n n≤0 →
      subst (¬_ ∘ P) (sym (ℕ.≤0→≡0 n≤0)) ¬p
    searchUpTo (suc b) with searchUpTo b
    ... | inl (n , least , n≤b) =
      inl (n , least , ℕ.≤-trans n≤b ℕ.≤-sucℕ)
    ... | inr none with decP (suc b)
    ...   | yes p = inl (suc b ,
      (p , λ n n<sb → none n (ℕ.pred-≤-pred n<sb)) ,
      ℕ.≤-refl)
    ...   | no ¬p = inr λ n n≤sb pn →
      case ℕ.≤-split n≤sb of λ where
        (inl n<sb) → none n (ℕ.pred-≤-pred n<sb) pn
        (inr n≡sb) → ¬p (subst P n≡sb pn)

    leastUpTo : ∀ b → Candidate b →
      Σ[ n ∈ ℕ ] ℕ.Minimal.Least P n
    leastUpTo b candidate with searchUpTo b
    ... | inl (n , least , _) = n , least
    ... | inr none = ⊥.rec (none
      (candidate .fst) (candidate .snd .fst) (candidate .snd .snd))


  module DecidableUnboundedSubtype
    (P : ℕ → Type₀)
    (isPropP : ∀ n → isProp (P n))
    (decP : ∀ n → Dec (P n))
    (P0 : P 0)
    (later : ∀ m → Σ[ n ∈ ℕ ] (m < n) × P n)
    where

    -- Search only above m by applying bounded least search to the
    -- decidable predicate (m <_) × P.

    Above : ℕ → ℕ → Type₀
    Above m n = (m < n) × P n

    decAbove : ∀ m n → Dec (Above m n)
    decAbove m n = Dec× (ℕ.<Dec m n) (decP n)

    isPropAbove : ∀ m n → isProp (Above m n)
    isPropAbove m n = isProp× ℕ.isProp≤ (isPropP n)

    nextLeast : ∀ m → Σ[ n ∈ ℕ ] ℕ.Minimal.Least (Above m) n
    nextLeast m = leastUpToForAbove bound candidate
      where
      bound = later m .fst

      candidate : Σ[ n ∈ ℕ ] (n ≤ bound) × Above m n
      candidate = bound , ℕ.≤-refl , later m .snd

      leastUpToForAbove : ∀ b →
        (Σ[ n ∈ ℕ ] (n ≤ b) × Above m n) →
        Σ[ n ∈ ℕ ] ℕ.Minimal.Least (Above m) n
      leastUpToForAbove b =
        BoundedLeast.leastUpTo
          (Above m) (isPropAbove m) (decAbove m) b

    next : ℕ → ℕ
    next m = nextLeast m .fst

    next> : ∀ m → m < next m
    next> m = nextLeast m .snd .fst .fst

    nextP : ∀ m → P (next m)
    nextP m = nextLeast m .snd .fst .snd

    noBetween : ∀ m n → m < n → n < next m → ¬ P n
    noBetween m n m<n n<next pn =
      nextLeast m .snd .snd n n<next (m<n , pn)

    enumerate : ℕ → ℕ
    enumerate zero = zero
    enumerate (suc n) = next (enumerate n)

    enumerateP : ∀ n → P (enumerate n)
    enumerateP zero = P0
    enumerateP (suc n) = nextP (enumerate n)

    enumerateStep : ∀ n → enumerate n < enumerate (suc n)
    enumerateStep n = next> (enumerate n)

    enumerateIncreasing : ℕ.isStrictlyIncreasing enumerate
    enumerateIncreasing =
      ℕ.sucIncreasing→StrictlyIncreasing enumerate enumerateStep

    rank : ℕ → ℕ
    rank n = nearestValues enumerate refl enumerateIncreasing n .fst .fst

    rankInterval : ∀ n →
      (enumerate (rank n) ≤ n) ×
      (n < enumerate (suc (rank n)))
    rankInterval n = nearestValues enumerate refl enumerateIncreasing n .fst .snd

    enumerate-rank : ∀ n → P n → enumerate (rank n) ≡ n
    enumerate-rank n pn with ℕ.≤-split (rankInterval n .fst)
    ... | inr en≡n = en≡n
    ... | inl en<n = ⊥.rec
      (noBetween (enumerate (rank n)) n en<n
        (rankInterval n .snd) pn)

    rank-enumerate : ∀ k → rank (enumerate k) ≡ k
    rank-enumerate k = cong fst
      (nearestValues enumerate refl enumerateIncreasing (enumerate k) .snd
        (k , ℕ.≤-refl , enumerateStep k))

    subtypeIsoℕ : Iso (Σ[ n ∈ ℕ ] P n) ℕ
    subtypeIsoℕ .Iso.fun (n , _) = rank n
    subtypeIsoℕ .Iso.inv k = enumerate k , enumerateP k
    subtypeIsoℕ .Iso.sec = rank-enumerate
    subtypeIsoℕ .Iso.ret (n , pn) =
      Σ≡Prop isPropP (enumerate-rank n pn)


-- Raw rational presentations are coded so that (pos n , 1) receives the
-- even code 2n.  This supplies the unbounded stream of reduced codes used by
-- the enumeration above.

private
  Raw : Type₀
  Raw = ℤ × ℕ₊₁

  Rest : Type₀
  Rest = ℕ ⊎ (ℤ × ℕ)

  ℤSumIso : Iso ℤ (ℕ ⊎ ℕ)
  ℤSumIso .Iso.fun (pos n) = inl n
  ℤSumIso .Iso.fun (negsuc n) = inr n
  ℤSumIso .Iso.inv (inl n) = pos n
  ℤSumIso .Iso.inv (inr n) = negsuc n
  ℤSumIso .Iso.sec (inl n) = refl
  ℤSumIso .Iso.sec (inr n) = refl
  ℤSumIso .Iso.ret (pos n) = refl
  ℤSumIso .Iso.ret (negsuc n) = refl

  ℤNatIso : Iso ℤ ℕ
  ℤNatIso = compIso ℤSumIso ℕ⊎ℕ≅ℕ

  RestNatIso : Iso Rest ℕ
  RestNatIso = compIso
    (⊎Iso idIso (compIso (prodIso ℤNatIso idIso) ℕ×ℕ≅ℕ))
    ℕ⊎ℕ≅ℕ

  splitRawIso : Iso Raw (ℕ ⊎ Rest)
  splitRawIso .Iso.fun (pos n , 1+ zero) = inl n
  splitRawIso .Iso.fun (negsuc n , 1+ zero) = inr (inl n)
  splitRawIso .Iso.fun (z , 1+ suc d) = inr (inr (z , d))
  splitRawIso .Iso.inv (inl n) = pos n , 1+ zero
  splitRawIso .Iso.inv (inr (inl n)) = negsuc n , 1+ zero
  splitRawIso .Iso.inv (inr (inr (z , d))) = z , 1+ suc d
  splitRawIso .Iso.sec (inl n) = refl
  splitRawIso .Iso.sec (inr (inl n)) = refl
  splitRawIso .Iso.sec (inr (inr (pos n , d))) = refl
  splitRawIso .Iso.sec (inr (inr (negsuc n , d))) = refl
  splitRawIso .Iso.ret (pos n , 1+ zero) = refl
  splitRawIso .Iso.ret (negsuc n , 1+ zero) = refl
  splitRawIso .Iso.ret (pos n , 1+ suc d) = refl
  splitRawIso .Iso.ret (negsuc n , 1+ suc d) = refl

  rawNatIso : Iso Raw ℕ
  rawNatIso = compIso splitRawIso
    (compIso (⊎Iso idIso RestNatIso) ℕ⊎ℕ≅ℕ)

  Reduced : Raw → Type₀
  Reduced (a , b) = areCoprime (ℤ.abs a , ℕ₊₁→ℕ b)

  isPropReduced : ∀ r → isProp (Reduced r)
  isPropReduced (a , b) = isPropAreCoprime _ _

  decReduced : ∀ r → Dec (Reduced r)
  decReduced (a , b) = decGCD

  CanonicalCode : ℕ → Type₀
  CanonicalCode n = Reduced (rawNatIso .Iso.inv n)

  isPropCanonicalCode : ∀ n → isProp (CanonicalCode n)
  isPropCanonicalCode n =
    isPropReduced (rawNatIso .Iso.inv n)

  decCanonicalCode : ∀ n → Dec (CanonicalCode n)
  decCanonicalCode n =
    decReduced (rawNatIso .Iso.inv n)

  integerRaw : ℕ → Raw
  integerRaw n = pos n , 1+ zero

  integerCode : ∀ n → rawNatIso .Iso.fun (integerRaw n) ≡ ℕ.doubleℕ n
  integerCode n = refl

  integerReduced : ∀ n → Reduced (integerRaw n)
  integerReduced n = oneGCD n

  integerCanonicalCode : ∀ n → CanonicalCode (ℕ.doubleℕ n)
  integerCanonicalCode n = subst CanonicalCode (integerCode n)
    (subst Reduced (sym (rawNatIso .Iso.ret (integerRaw n)))
      (integerReduced n))

  n≤double : ∀ n → n ≤ ℕ.doubleℕ n
  n≤double zero = ℕ.≤-refl
  n≤double (suc n) =
    ℕ.suc-≤-suc (ℕ.≤-trans (n≤double n) ℕ.≤-sucℕ)

  laterCanonicalCode : ∀ m →
    Σ[ n ∈ ℕ ] (m < n) × CanonicalCode n
  laterCanonicalCode m =
    ℕ.doubleℕ (suc m) , n≤double (suc m) ,
    integerCanonicalCode (suc m)

  module CanonicalEnumeration = DecidableUnboundedSubtype
    CanonicalCode isPropCanonicalCode decCanonicalCode
    (integerCanonicalCode zero) laterCanonicalCode

  canonicalReducedIso :
    Iso (Σ[ n ∈ ℕ ] CanonicalCode n)
        (Σ[ r ∈ Raw ] Reduced r)
  canonicalReducedIso =
    Σ-cong-iso-fst {B = Reduced} (invIso rawNatIso)

  reducedIsoℕ : Iso (Σ[ r ∈ Raw ] Reduced r) ℕ
  reducedIsoℕ = compIso (invIso canonicalReducedIso)
    CanonicalEnumeration.subtypeIsoℕ


-- Reduction chooses the unique coprime presentation of a quotient rational.

private
  reducedCoprime : ∀ (r : Raw) → Reduced r →
    ℚP.reduced [ r .fst / r .snd ] .fst ≡ r
  reducedCoprime (a , b) cp =
    cong (λ t → ℤ.sign a ℤ.· pos (t .fst) , t .snd)
      (toCoprime-idem (ℤ.abs a , b) cp)
    ∙ cong (_, b) (ℤ.sign·abs a)


private
  reducedRationalIso : Iso (Σ[ r ∈ Raw ] Reduced r) ℚ
  reducedRationalIso .Iso.fun ((a , b) , _) = [ a / b ]
  reducedRationalIso .Iso.inv q =
    ℚP.reduced q .fst , ℚP.reduced q .snd .fst
  reducedRationalIso .Iso.sec q = ℚP.reduced q .snd .snd
  reducedRationalIso .Iso.ret (r , cp) =
    Σ≡Prop isPropReduced (reducedCoprime r cp)


ℚIsoℕ : Iso ℚ ℕ
ℚIsoℕ = compIso (invIso reducedRationalIso) reducedIsoℕ

ℚ≃ℕ : ℚ ≃ ℕ
ℚ≃ℕ = isoToEquiv ℚIsoℕ
