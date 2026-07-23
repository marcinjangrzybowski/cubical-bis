module Cubical.Algebra.OrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.SIP using (TypeWithStr)
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Functions.Logic as L

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Nat as ℕ renaming (
  _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _∸_ to _∸ℕ_ ; _^_ to _^ℕ_)
open import Cubical.Data.Nat.Order as ℕ renaming (
  _≤_ to _≤ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Data.Nat.Order.Inductive as ℕ using (_<ᵗ_ ; _≤ᵗ_)

open import Cubical.Data.Int.Fast as ℤ using (ℤ ; pos ; negsuc ; _ℕ-_) renaming (
  _+_ to _+ℤ_ ; _·_ to _·ℤ_ ; _-_ to _-ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Int.Fast.Order as ℤ renaming (
  _≤_ to _≤ℤ_ ; _<_ to _<ℤ_ ) hiding (
    0≤→abs≡id ; 0<→abs≡id ; ≤→0≤Δ ; <→0<Δ ; 0≤Δ→≤ ; 0<Δ→<)

open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semiring
open import Cubical.Algebra.Semiring.BigOps
open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int.Fast
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Int.Fast

open import Cubical.Tactics.CommRingSolver

open import Cubical.Relation.Nullary

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Quoset
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Relation.Binary.Order.Poset hiding (isPseudolattice)
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Relation.Binary.Order.QuosetReasoning


private
  variable
    ℓ ℓ' ℓ'' : Level

OrderedCommRing→StrictOrder : OrderedCommRing ℓ ℓ' → StrictOrder ℓ ℓ'
OrderedCommRing→StrictOrder R .fst = R .fst
OrderedCommRing→StrictOrder R .snd = strictorderstr _ isStrictOrder where
  open OrderedCommRingStr (str R)

OrderedCommRing→Ring : OrderedCommRing ℓ ℓ' → Ring ℓ
OrderedCommRing→Ring = CommRing→Ring ∘ OrderedCommRing→CommRing

OrderedCommRing→Poset : OrderedCommRing ℓ ℓ' → Poset ℓ ℓ'
OrderedCommRing→Poset = Pseudolattice→Poset ∘ OrderedCommRing→PseudoLattice

OrderedCommRing→Quoset : OrderedCommRing ℓ ℓ' → Quoset ℓ ℓ'
OrderedCommRing→Quoset = StrictOrder→Quoset ∘ OrderedCommRing→StrictOrder

OrderedCommRing→Apartness : OrderedCommRing ℓ ℓ' → Apartness ℓ ℓ'
OrderedCommRing→Apartness = StrictOrder→Apartness ∘ OrderedCommRing→StrictOrder

module OrderedCommRingReasoning (R' : OrderedCommRing ℓ ℓ') where
  open OrderedCommRingStr (snd R')
  open <-≤-Reasoning
    (fst R')
    (str (OrderedCommRing→Poset  R'))
    (str (OrderedCommRing→Quoset R'))
    (λ x {y} {z} → <-≤-trans x y z)
    (λ x {y} {z} → ≤-<-trans x y z)
    (λ   {x} {y} → <-≤-weaken x y)
    public

  open <-syntax public
  open ≤-syntax public
  open ≡-syntax public


module _ (R' : OrderedCommRing ℓ ℓ') where
  private
    R = fst R'
    RCR = OrderedCommRing→CommRing R'
    open module R = RingTheory (OrderedCommRing→Ring R')
  open OrderedCommRingStr (snd R')
  open PseudolatticeTheory (OrderedCommRing→PseudoLattice R') renaming (
      L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨Comm to ⊔Comm ; ∨Idem to ⊔Idem ; ∨Assoc to ⊔Assoc
    ; ∨LUB to ⊔LUB
    ; ∨Monotone to ⊔Monotone ; ≥→∨≡Left to ≥→⊔≡Left
    ; ≤→∨≡Right to ≤→⊔≡Right
    ; ∧≤L to ⊓≤L ; ∧≤R to ⊓≤R ; ∧Comm to ⊓Comm ; ∧Idem to ⊓Idem ; ∧GLB to ⊓GLB
    ; ∧Monotone to ⊓Monotone)

  open OrderedCommRingReasoning R'

  module OrderedCommRingTheory where
    open Exponentiation (OrderedCommRing→CommRing R') public
    open BinaryRelation

    open ApartnessStr (str (OrderedCommRing→Apartness R')) using (_#_) public

    0≤1 : 0r ≤ 1r
    0≤1 = <-≤-weaken 0r 1r 0<1

    ≤→¬> : ∀ x y → x ≤ y → ¬ (y < x)
    ≤→¬> x y = equivFun (≤≃¬> x y)

    ¬<→≥ : ∀ x y → ¬ (x < y) → y ≤ x
    ¬<→≥ x y = invEq (≤≃¬> y x)

    ≥Using< : ∀ x y → (x < y → y ≤ x) → y ≤ x
    ≥Using< _ _ <→≥ = ¬<→≥ _ _ (∘diag (≤→¬> _ _ ∘ <→≥))

    abs ∣_∣ : R → R
    abs z = z ⊔ (- z)
    ∣_∣ = abs

    +MonoL< : ∀ x y z → x < y → z + x < z + y
    +MonoL< x y z = subst2 _<_ (+Comm _ _) (+Comm _ _) ∘ +MonoR< x y z

    +Mono< : ∀ x y z w → x < y → z < w → x + z < y + w
    +Mono< x y z w x<y z<w = begin<
      x + z <⟨ +MonoR< x y z x<y ⟩ y + z <⟨ +MonoL< z w y z<w ⟩ y + w ◾

    +MonoL≤ : ∀ x y z → x ≤ y → z + x ≤ z + y
    +MonoL≤ x y z = subst2 _≤_ (+Comm _ _) (+Comm _ _) ∘ +MonoR≤ x y z

    +Mono≤ : ∀ x y z w → x ≤ y → z ≤ w → x + z ≤ y + w
    +Mono≤ x y z w x<y z<w = begin≤
      x + z ≤⟨ +MonoR≤ x y z x<y ⟩ y + z ≤⟨ +MonoL≤ z w y z<w ⟩ y + w ◾

    +CancelR< : ∀ x y z → x + z < y + z → x < y
    +CancelR< x y z =
      subst2 _<_ (solve! RCR) (solve! RCR)
        ∘ +MonoR< (x + z) (y + z) (- z)

    +CancelL< : ∀ x y z → z + x < z + y → x < y
    +CancelL< x y z =
      +CancelR< x y z ∘ subst2 _<_ (+Comm z x) (+Comm z y)

    +CancelR≤ : ∀ x y z → x + z ≤ y + z → x ≤ y
    +CancelR≤ x y z =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        ∘ +MonoR≤ (x + z) (y + z) (- z)

    +CancelL≤ : ∀ x y z → z + x ≤ z + y → x ≤ y
    +CancelL≤ x y z =
      +CancelR≤ x y z ∘ subst2 _≤_ (+Comm z x) (+Comm z y)

    +CancelR<≃ : ∀ x y z → (x + z < y + z) ≃ (x < y)
    +CancelR<≃ x y z =
      propBiimpl→Equiv (is-prop-valued< _ _) (is-prop-valued< _ _)
        (+CancelR< x y z) (+MonoR< x y z)

    +CancelL<≃ : ∀ x y z → (z + x < z + y) ≃ (x < y)
    +CancelL<≃ x y z =
      propBiimpl→Equiv (is-prop-valued< _ _) (is-prop-valued< _ _)
        (+CancelL< x y z) (+MonoL< x y z)

    +CancelR≤≃ : ∀ x y z → (x + z ≤ y + z) ≃ (x ≤ y)
    +CancelR≤≃ x y z =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (+CancelR≤ x y z) (+MonoR≤ x y z)

    +CancelL≤≃ : ∀ x y z → (z + x ≤ z + y) ≃ (x ≤ y)
    +CancelL≤≃ x y z =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (+CancelL≤ x y z) (+MonoL≤ x y z)

    x-y≤z→x-z≤y : ∀ x y z → x - y ≤ z → x - z ≤ y
    x-y≤z→x-z≤y x y z x-y≤z =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ (x - y) z (y - z) x-y≤z)

    x-y≤z→x≤z+y : ∀ x y z → x - y ≤ z → x ≤ z + y
    x-y≤z→x≤z+y x y z x-y≤z =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ (x - y) z y x-y≤z)

    x<z+y→x-y<z : ∀ x y z → x < z + y → x - y < z
    x<z+y→x-y<z x y z x<z+y =
      subst2 _<_ (solve! RCR) (solve! RCR)
        (+MonoR< x (z + y) (- y) x<z+y)

    x≤z+y→x-z≤y : ∀ x y z → x ≤ z + y → x - z ≤ y
    x≤z+y→x-z≤y x y z x≤z+y =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ x (z + y) (- z) x≤z+y)

    x+y≤z→y≤z-x : ∀ x y z → x + y ≤ z → y ≤ z - x
    x+y≤z→y≤z-x x y z x+y≤z =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ (x + y) z (- x) x+y≤z)

    y≤z-x→x+y≤z : ∀ x y z → y ≤ z - x → x + y ≤ z
    y≤z-x→x+y≤z x y z y≤z-x =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ y (z - x) x y≤z-x)

    x-y≤z-w→x+w≤z+y : ∀ x y z w → x - y ≤ z - w → x + w ≤ z + y
    x-y≤z-w→x+w≤z+y x y z w x-y≤z-w =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ (x - y) (z - w) (y + w) x-y≤z-w)

    x+w≤z+y→x-y≤z-w : ∀ x y z w → x + w ≤ z + y → x - y ≤ z - w
    x+w≤z+y→x-y≤z-w x y z w x+w≤z+y =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ (x + w) (z + y) (- y - w) x+w≤z+y)

    y<z-x→x+y<z : ∀ x y z → y < z - x → x + y < z
    y<z-x→x+y<z x y z y<z-x =
      subst2 _<_ (solve! RCR) (solve! RCR)
        (+MonoR< y (z - x) x y<z-x)

    x<y-z→z<y-x : ∀ x y z → x < y - z → z < y - x
    x<y-z→z<y-x x y z x<y-z =
      subst2 _<_ (solve! RCR) (solve! RCR)
        (+MonoR< x (y - z) (z - x) x<y-z)

    x≤y-z→z≤y-x : ∀ x y z → x ≤ y - z → z ≤ y - x
    x≤y-z→z≤y-x x y z x≤y-z =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ x (y - z) (z - x) x≤y-z)

    x<y-z→x+z<y : ∀ x y z → x < y - z → x + z < y
    x<y-z→x+z<y x y z x<y-z =
      subst2 _<_ refl (solve! RCR)
        (+MonoR< x (y - z) z x<y-z)

    x+z<y→x<y-z : ∀ x y z → x + z < y → x < y - z
    x+z<y→x<y-z x y z x+z<y =
      subst2 _<_ (solve! RCR) refl
        (+MonoR< (x + z) y (- z) x+z<y)

    x-y<z→x-z<y : ∀ x y z → x - y < z → x - z < y
    x-y<z→x-z<y x y z x-y<z =
      subst2 _<_ (solve! RCR) (solve! RCR)
        (+MonoR< (x - y) z (y - z) x-y<z)

    x-y<z→x<z+y : ∀ x y z → x - y < z → x < z + y
    x-y<z→x<z+y x y z x-y<z =
      subst2 _<_ (solve! RCR) refl
        (+MonoR< (x - y) z y x-y<z)

    ·MonoL< : ∀ x y z → 0r < z → x < y → z · x < z · y
    ·MonoL< x y z 0<z x<y = begin<
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z <⟨ ·MonoR< x y z 0<z x<y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·MonoL≤ : ∀ x y z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    ·MonoL≤ x y z 0≤z x≤y = begin≤
      z · x ≡→≤⟨ ·Comm z x ⟩ x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩ y · z ≡→≤⟨ ·Comm y z ⟩ z · y ◾

    ·Mono≤ : ∀ x y z w → 0r ≤ y → 0r ≤ z → x ≤ y → z ≤ w → x · z ≤ y · w
    ·Mono≤ x y z w 0≤y 0≤z x≤y z≤w = begin≤
      x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩
      y · z ≤⟨ ·MonoL≤ z w y 0≤y z≤w ⟩
      y · w ◾

    ·Mono< : ∀ x y z w → 0r ≤ x → 0r ≤ z → x < y → z < w → x · z < y · w
    ·Mono< x y z w 0≤x 0≤z x<y z<w = begin<
      x · z ≤⟨ ·MonoL≤ z w x 0≤x (<-≤-weaken z w z<w) ⟩
      x · w <⟨ ·MonoR< x y w (≤-<-trans 0r z w 0≤z z<w) x<y ⟩
      y · w ◾

    ·Mono<≤ : ∀ x y z w → 0r ≤ x → 0r < z → x < y → z ≤ w → x · z < y · w
    ·Mono<≤ x y z w 0≤x 0<z x<y z≤w = begin<
      x · z <⟨ ·MonoR< x y z 0<z x<y ⟩
      y · z ≤⟨ ·MonoL≤ z w y 0≤y z≤w ⟩
      y · w ◾
      where
      0≤y : 0r ≤ y
      0≤y = begin≤
        0r ≤⟨ 0≤x ⟩ x ≤⟨ <-≤-weaken x y x<y ⟩ y ◾

    ·Mono≤< : ∀ x y z w → 0r < x → 0r ≤ z → x ≤ y → z < w → x · z < y · w
    ·Mono≤< x y z w 0<x 0≤z x≤y z<w = begin<
      x · z ≤⟨ ·MonoR≤ x y z 0≤z x≤y ⟩
      y · z <⟨ ·MonoL< z w y (<-≤-trans 0r x y 0<x x≤y) z<w ⟩
      y · w ◾

    powPositive : ∀ x n → 0r < x → 0r < x ^ n
    powPositive x zero    0<x = 0<1
    powPositive x (suc n) 0<x = begin<
      0r              ≡→≤⟨ sym (0LeftAnnihilates (x ^ n)) ⟩
      0r · (x ^ n)      <⟨ ·MonoR< 0r x (x ^ n) (powPositive x n 0<x) 0<x ⟩
      x · (x ^ n)       ◾

    powNonnegative : ∀ x n → 0r ≤ x → 0r ≤ x ^ n
    powNonnegative x zero    0≤x = 0≤1
    powNonnegative x (suc n) 0≤x = begin≤
      0r              ≡→≤⟨ sym (0LeftAnnihilates (x ^ n)) ⟩
      0r · (x ^ n)      ≤⟨ ·MonoR≤ 0r x (x ^ n) (powNonnegative x n 0≤x) 0≤x ⟩
      x · (x ^ n)       ◾

    one<pow : ∀ x n → 1r < x → 1r < x ^ suc n
    one<pow x zero 1<x =
      subst (1r <_) (sym (·IdR x)) 1<x
    one<pow x (suc n) 1<x = begin<
      1r                ≡→≤⟨ sym (·IdR 1r) ⟩
      1r · 1r             <⟨ ·Mono< 1r x 1r (x ^ suc n)
                              0≤1 0≤1 1<x (one<pow x n 1<x) ⟩
      x · (x ^ suc n)     ◾

    pow<one : ∀ x → 0r ≤ x → ∀ n → x < 1r → x ^ suc n < 1r
    pow<one x _ zero x<1 =
      subst (_< 1r) (sym (·IdR x)) x<1
    pow<one x 0≤x (suc n) x<1 = begin<
      x · (x ^ suc n) <⟨ ·Mono< x 1r (x ^ suc n) 1r
                           0≤x (powNonnegative x (suc n) 0≤x)
                           x<1 (pow<one x 0≤x n x<1) ⟩
      1r · 1r          ≡→≤⟨ ·IdR 1r ⟩
      1r                 ◾

    pow≤one : ∀ x → 0r ≤ x → ∀ n → x ≤ 1r → x ^ n ≤ 1r
    pow≤one x _ zero _ = is-refl 1r
    pow≤one x 0≤x (suc n) x≤1 = begin≤
      x · (x ^ n) ≤⟨ ·Mono≤ x 1r (x ^ n) 1r
                        0≤1 (powNonnegative x n 0≤x)
                        x≤1 (pow≤one x 0≤x n x≤1) ⟩
      1r · 1r       ≡→≤⟨ ·IdR 1r ⟩
      1r              ◾

    powStrictMono : ∀ {x y} n → 0 <ℕ n → 0r ≤ x → 0r ≤ y → x < y
                  → x ^ n < y ^ n
    powStrictMono zero 0<n _ _ _ = ⊥.rec (ℕ.¬-<-zero 0<n)
    powStrictMono {x} {y} (suc zero) _ _ _ x<y =
      subst2 _<_ (sym (·IdR x)) (sym (·IdR y)) x<y
    powStrictMono {x} {y} (suc (suc n)) _ 0≤x 0≤y x<y =
      ·Mono< x y (x ^ suc n) (y ^ suc n)
        0≤x (powNonnegative x (suc n) 0≤x) x<y
        (powStrictMono (suc n) (ℕ.suc-≤-suc ℕ.zero-≤)
          0≤x 0≤y x<y)

    powMono : ∀ {x y} n → 0r ≤ x → x ≤ y → x ^ n ≤ y ^ n
    powMono zero _ _ = is-refl 1r
    powMono {x} {y} (suc n) 0≤x x≤y =
      ·Mono≤ x y (x ^ n) (y ^ n)
        (is-trans≤ 0r x y 0≤x x≤y) (powNonnegative x n 0≤x)
        x≤y (powMono n 0≤x x≤y)

    powReflects≤ : ∀ {x y} n → 0 <ℕ n → 0r ≤ x → 0r ≤ y
                 → x ^ n ≤ y ^ n → x ≤ y
    powReflects≤ {x} {y} n 0<n 0≤x 0≤y xⁿ≤yⁿ =
      ¬<→≥ y x
        (≤→¬> (x ^ n) (y ^ n) xⁿ≤yⁿ ∘
          powStrictMono n 0<n 0≤y 0≤x)

    one#pow : ∀ x → 0r ≤ x → ∀ n → 1r # x → 1r # (x ^ suc n)
    one#pow x _ n (inl 1<x) = inl (one<pow x n 1<x)
    one#pow x 0≤x n (inr x<1) = inr (pow<one x 0≤x n x<1)

    powExponentStrictMono : ∀ {x} m n → 1r < x → m <ℕ n → x ^ m < x ^ n
    powExponentStrictMono m zero _ m<n = ⊥.rec (ℕ.¬-<-zero m<n)
    powExponentStrictMono {x} zero (suc n) 1<x _ = one<pow x n 1<x
    powExponentStrictMono {x} (suc m) (suc n) 1<x sm<sn =
      ·MonoL< (x ^ m) (x ^ n) x
        (≤-<-trans 0r 1r x 0≤1 1<x)
        (powExponentStrictMono m n 1<x (ℕ.predℕ-≤-predℕ sm<sn))

    powExponentAntitone : ∀ x → 0r ≤ x → x ≤ 1r → ∀ m n
                        → m ≤ℕ n → x ^ n ≤ x ^ m
    powExponentAntitone x 0≤x x≤1 zero n _ =
      pow≤one x 0≤x n x≤1
    powExponentAntitone x 0≤x x≤1 (suc m) zero sm≤0 =
      ⊥.rec (ℕ.¬-<-zero sm≤0)
    powExponentAntitone x 0≤x x≤1 (suc m) (suc n) sm≤sn =
      ·MonoL≤ (x ^ n) (x ^ m) x 0≤x
        (powExponentAntitone x 0≤x x≤1 m n
          (ℕ.pred-≤-pred sm≤sn))

    ·CancelL≤ : ∀ x y z → 0r < z → z · x ≤ z · y → x ≤ y
    ·CancelL≤ x y z 0<z zx≤zy = ¬<→≥ y x $ ≤→¬> _ _ zx≤zy ∘ ·MonoL< _ _ z 0<z

    ·CancelR≤ : ∀ x y z → 0r < z → x · z ≤ y · z → x ≤ y
    ·CancelR≤ x y z 0<z zx≤zy = ¬<→≥ y x $ ≤→¬> _ _ zx≤zy ∘ ·MonoR< _ _ z 0<z

    ·MonoL≤≃ : ∀ x y z → 0r < z → (x ≤ y) ≃ (z · x ≤ z · y)
    ·MonoL≤≃ x y z 0<z =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (·MonoL≤ x y z (<-≤-weaken 0r z 0<z))
        (·CancelL≤ x y z 0<z)

    ·MonoR≤≃ : ∀ x y z → 0r < z → (x ≤ y) ≃ (x · z ≤ y · z)
    ·MonoR≤≃ x y z 0<z =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (·MonoR≤ x y z (<-≤-weaken 0r z 0<z))
        (·CancelR≤ x y z 0<z)

    -- NOTE:
    -- These properties don't seems like to be derivable.
    -- However we can prove their double negations, so they are classically valid
    -- Moreover, in a Ordered Heyting Field (where elements are invertible iff they
    -- are apart form zero) we can prove them by multiplying by z⁻¹
    --
    -- ·CancelL< : ∀ x y z → 0r < z → z · x < z · y → x < y
    -- ·CancelL< = ?
    --
    -- ·CancelR< : ∀ x y z → 0r < z → x · z < y · z → x < y
    -- ·CancelR< = ?

    -- These are intended to be used in the order reasoning
    [_]+<_ : ∀ {x y} z → x < y → z + x < z + y
    [_]+<_ z x<y = +MonoL< _ _ z x<y

    _<+[_] : ∀ {x y} → x < y → ∀ z → x + z < y + z
    _<+[_] x<y z = +MonoR< _ _ z x<y

    [_]+≤_ : ∀ {x y} z → x ≤ y → z + x ≤ z + y
    [_]+≤_ z x≤y = +MonoL≤ _ _ z x≤y

    _≤+[_] : ∀ {x y} → x ≤ y → ∀ z → x + z ≤ y + z
    _≤+[_] x≤y z = +MonoR≤ _ _ z x≤y

    [_,_]·<_ : ∀ {x y} z → 0r < z → x < y → z · x < z · y
    [_,_]·<_ z 0<z x<y = ·MonoL< _ _ z 0<z x<y

    _<·[_,_] : ∀ {x y} → x < y → ∀ z → 0r < z → x · z < y · z
    _<·[_,_] x<y z 0<z = ·MonoR< _ _ z 0<z x<y

    [_,_]·≤_ : ∀ {x y} z → 0r ≤ z → x ≤ y → z · x ≤ z · y
    [_,_]·≤_ z 0≤z x≤y = ·MonoL≤ _ _ z 0≤z x≤y

    _≤·[_,_] : ∀ {x y} → x ≤ y → ∀ z → 0r ≤ z → x · z ≤ y · z
    _≤·[_,_] x≤y z 0≤z = ·MonoR≤ _ _ z 0≤z x≤y

    private
      example : ∀ a b c d e f g
              → (0r < f) → a < (b + c) → b ≤ d → (d + c) < (e · f) → e < g
              → a < (g · f)
      example a b c d e f g 0<f a<b+c b≤d d+c<e·f e<g = begin<
        a     <⟨ a<b+c ⟩
        b + c ≤⟨ b≤d ≤+[ c ] ⟩
        d + c <⟨ d+c<e·f ⟩
        e · f <⟨ e<g <·[ f , 0<f ] ⟩
        g · f ◾

    <SumLeftPos : ∀ x y → 0r < y → x < x + y
    <SumLeftPos x y 0<y = begin< x ≡→≤⟨ sym (+IdR x) ⟩ x + 0r <⟨ [ x ]+< 0<y ⟩ x + y ◾

    <SumRightPos : ∀ x y → 0r < y → x < y + x
    <SumRightPos x y 0<y = begin< x ≡→≤⟨ sym (+IdL x) ⟩ 0r + x <⟨ 0<y <+[ x ] ⟩ y + x ◾

    ≤→<SumLeftPos : ∀ x y z → x ≤ y → 0r < z → x < y + z
    ≤→<SumLeftPos x y z x≤y 0<z =
      ≤-<-trans x y (y + z) x≤y (<SumLeftPos y z 0<z)

    ≤SumLeftNonNeg : ∀ x y → 0r ≤ y → x ≤ x + y
    ≤SumLeftNonNeg x y 0≤y = begin≤ x ≡→≤⟨ sym (+IdR x) ⟩ x + 0r ≤⟨ [ x ]+≤ 0≤y ⟩ x + y ◾

    ≤SumRightNonNeg : ∀ x y → 0r ≤ y → x ≤ y + x
    ≤SumRightNonNeg x y 0≤y = begin≤ x ≡→≤⟨ sym (+IdL x) ⟩ 0r + x ≤⟨ 0≤y ≤+[ x ] ⟩ y + x ◾

    -Flip< : ∀ x y → x < y → - y < - x
    -Flip< x y x<y = begin<
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   <⟨ +MonoR< x y (- x - y) x<y ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    -Flip≤ : ∀ x y → x ≤ y → - y ≤ - x
    -Flip≤ x y x≤y = begin≤
      - y           ≡→≤⟨ solve! RCR ⟩
      x + (- x - y)   ≤⟨ +MonoR≤ x y (- x - y) x≤y ⟩
      y + (- x - y) ≡→≤⟨ solve! RCR ⟩
      - x             ◾

    -Flip<≃ : ∀ x y → (x < y) ≃ (- y < - x)
    -Flip<≃ x y =
      propBiimpl→Equiv (is-prop-valued< _ _) (is-prop-valued< _ _)
        (-Flip< x y)
        (subst2 _<_ (solve! RCR) (solve! RCR) ∘ -Flip< (- y) (- x))

    -Flip≤≃ : ∀ x y → (x ≤ y) ≃ (- y ≤ - x)
    -Flip≤≃ x y =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (-Flip≤ x y)
        (subst2 _≤_ (solve! RCR) (solve! RCR) ∘ -Flip≤ (- y) (- x))

    negHalfLineStrictIso : ∀ x₀ →
      Iso (Σ R (x₀ <_)) (Σ R (_< (- x₀)))
    negHalfLineStrictIso x₀ .Iso.fun (x , x₀<x) =
      - x , -Flip< x₀ x x₀<x
    negHalfLineStrictIso x₀ .Iso.inv (x , x<-x₀) =
      - x , subst (_< - x) (solve! RCR) (-Flip< x (- x₀) x<-x₀)
    negHalfLineStrictIso x₀ .Iso.sec _ =
      Σ≡Prop (λ _ → is-prop-valued< _ _) (solve! RCR)
    negHalfLineStrictIso x₀ .Iso.ret _ =
      Σ≡Prop (λ _ → is-prop-valued< _ _) (solve! RCR)

    negHalfLineIso : ∀ x₀ →
      Iso (Σ R (x₀ ≤_)) (Σ R (_≤ (- x₀)))
    negHalfLineIso x₀ .Iso.fun (x , x₀≤x) =
      - x , -Flip≤ x₀ x x₀≤x
    negHalfLineIso x₀ .Iso.inv (x , x≤-x₀) =
      - x , subst (_≤ - x) (solve! RCR) (-Flip≤ x (- x₀) x≤-x₀)
    negHalfLineIso x₀ .Iso.sec _ =
      Σ≡Prop (λ _ → is-prop-valued≤ _ _) (solve! RCR)
    negHalfLineIso x₀ .Iso.ret _ =
      Σ≡Prop (λ _ → is-prop-valued≤ _ _) (solve! RCR)

    negHalfLineStrictIso' : ∀ x₀ →
      Iso (Σ R ((- x₀) <_)) (Σ R (_< x₀))
    negHalfLineStrictIso' x₀ .Iso.fun (x , -x₀<x) =
      - x , subst (- x <_) (solve! RCR) (-Flip< (- x₀) x -x₀<x)
    negHalfLineStrictIso' x₀ .Iso.inv (x , x<x₀) =
      - x , -Flip< x x₀ x<x₀
    negHalfLineStrictIso' x₀ .Iso.sec _ =
      Σ≡Prop (λ _ → is-prop-valued< _ _) (solve! RCR)
    negHalfLineStrictIso' x₀ .Iso.ret _ =
      Σ≡Prop (λ _ → is-prop-valued< _ _) (solve! RCR)

    negHalfLineIso' : ∀ x₀ →
      Iso (Σ R ((- x₀) ≤_)) (Σ R (_≤ x₀))
    negHalfLineIso' x₀ .Iso.fun (x , -x₀≤x) =
      - x , subst (- x ≤_) (solve! RCR) (-Flip≤ (- x₀) x -x₀≤x)
    negHalfLineIso' x₀ .Iso.inv (x , x≤x₀) =
      - x , -Flip≤ x x₀ x≤x₀
    negHalfLineIso' x₀ .Iso.sec _ =
      Σ≡Prop (λ _ → is-prop-valued≤ _ _) (solve! RCR)
    negHalfLineIso' x₀ .Iso.ret _ =
      Σ≡Prop (λ _ → is-prop-valued≤ _ _) (solve! RCR)

    negHalfLineFnIso : ∀ x₀ y₀ →
      Iso ((Σ R (x₀ ≤_)) → (Σ R (y₀ ≤_)))
          ((Σ R (_≤ (- x₀))) → (Σ R (_≤ (- y₀))))
    negHalfLineFnIso x₀ y₀ =
      compIso
        (codomainIso (negHalfLineIso y₀))
        (domIso (negHalfLineIso x₀))

    negHalfLineFnStrictIso : ∀ x₀ y₀ →
      Iso ((Σ R (x₀ <_)) → (Σ R (y₀ <_)))
          ((Σ R (_< (- x₀))) → (Σ R (_< (- y₀))))
    negHalfLineFnStrictIso x₀ y₀ =
      compIso
        (codomainIso (negHalfLineStrictIso y₀))
        (domIso (negHalfLineStrictIso x₀))

    negHalfLineFnIso' : ∀ x₀ y₀ →
      Iso ((Σ R ((- x₀) ≤_)) → (Σ R ((- y₀) ≤_)))
          ((Σ R (_≤ x₀)) → (Σ R (_≤ y₀)))
    negHalfLineFnIso' x₀ y₀ =
      compIso
        (codomainIso (negHalfLineIso' y₀))
        (domIso (negHalfLineIso' x₀))

    negHalfLineFnStrictIso' : ∀ x₀ y₀ →
      Iso ((Σ R ((- x₀) <_)) → (Σ R ((- y₀) <_)))
          ((Σ R (_< x₀)) → (Σ R (_< y₀)))
    negHalfLineFnStrictIso' x₀ y₀ =
      compIso
        (codomainIso (negHalfLineStrictIso' y₀))
        (domIso (negHalfLineStrictIso' x₀))

    joinNeg≡negMeet : ∀ x y → (- x) ⊔ (- y) ≡ - (x ⊓ y)
    joinNeg≡negMeet x y = is-antisym _ _
      (⊔LUB (-Flip≤ (x ⊓ y) x ⊓≤L) (-Flip≤ (x ⊓ y) y ⊓≤R))
      (begin≤
        - (x ⊓ y)                 ≤⟨ -Flip≤ _ _ (⊓GLB
          (begin≤
            - ((- x) ⊔ (- y))     ≤⟨ -Flip≤ _ _ L≤⊔ ⟩
            - (- x)             ≡→≤⟨ solve! RCR ⟩
            x                     ◾)
          (begin≤
            - ((- x) ⊔ (- y))     ≤⟨ -Flip≤ _ _ R≤⊔ ⟩
            - (- y)             ≡→≤⟨ solve! RCR ⟩
            y                     ◾)) ⟩
        - (- ((- x) ⊔ (- y)))   ≡→≤⟨ solve! RCR ⟩
        (- x) ⊔ (- y)             ◾)

    0<→-<0 : ∀ x → 0r < x → - x < 0r
    0<→-<0 x = subst (- x <_) (solve! RCR) ∘ -Flip< 0r x

    <0→0<- : ∀ x → x < 0r → 0r < - x
    <0→0<- x = subst (_< - x) (solve! RCR) ∘ -Flip< x 0r

    0≤→-≤0 : ∀ x → 0r ≤ x → - x ≤ 0r
    0≤→-≤0 x = subst (- x ≤_) (solve! RCR) ∘ -Flip≤ 0r x

    ≤0→0≤- : ∀ x → x ≤ 0r → 0r ≤ - x
    ≤0→0≤- x = subst (_≤ - x) (solve! RCR) ∘ -Flip≤ x 0r

    <→0<Δ : ∀ x y → x < y → 0r < y - x
    <→0<Δ x y x<y = begin< 0r ≡→≤⟨ solve! RCR ⟩ x - x <⟨ +MonoR< _ _ _ x<y ⟩ y - x ◾

    ≤→0≤Δ : ∀ x y → x ≤ y → 0r ≤ y - x
    ≤→0≤Δ x y x≤y = begin≤ 0r ≡→≤⟨ solve! RCR ⟩ x - x ≤⟨ +MonoR≤ _ _ _ x≤y ⟩ y - x ◾

    0<Δ→< : ∀ x y → 0r < y - x → x < y
    0<Δ→< x y 0<y-x = subst2 _<_ (solve! RCR) (solve! RCR) (+MonoR< _ _ x 0<y-x)

    0≤Δ→≤ : ∀ x y → 0r ≤ y - x → x ≤ y
    0≤Δ→≤ x y 0≤y-x = subst2 _≤_ (solve! RCR) (solve! RCR) (+MonoR≤ _ _ x 0≤y-x)

    <≃0<Δ : ∀ x y → (x < y) ≃ (0r < y - x)
    <≃0<Δ x y =
      propBiimpl→Equiv (is-prop-valued< _ _) (is-prop-valued< _ _)
        (<→0<Δ x y) (0<Δ→< x y)

    ≤≃0≤Δ : ∀ x y → (x ≤ y) ≃ (0r ≤ y - x)
    ≤≃0≤Δ x y =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (≤→0≤Δ x y) (0≤Δ→≤ x y)

    <→Δ<0 : ∀ x y → x < y → x - y < 0r
    <→Δ<0 x y x<y =
      subst2 _<_ (solve! RCR) (solve! RCR)
        (+MonoR< x y (- y) x<y)

    Δ<0→< : ∀ x y → x - y < 0r → x < y
    Δ<0→< x y x-y<0 =
      subst2 _<_ (solve! RCR) (solve! RCR)
        (+MonoR< (x - y) 0r y x-y<0)

    <≃Δ<0 : ∀ x y → (x < y) ≃ (x - y < 0r)
    <≃Δ<0 x y =
      propBiimpl→Equiv (is-prop-valued< _ _) (is-prop-valued< _ _)
        (<→Δ<0 x y) (Δ<0→< x y)

    ≤→Δ≤0 : ∀ x y → x ≤ y → x - y ≤ 0r
    ≤→Δ≤0 x y x≤y =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ x y (- y) x≤y)

    Δ≤0→≤ : ∀ x y → x - y ≤ 0r → x ≤ y
    Δ≤0→≤ x y x-y≤0 =
      subst2 _≤_ (solve! RCR) (solve! RCR)
        (+MonoR≤ (x - y) 0r y x-y≤0)

    ≤≃Δ≤0 : ∀ x y → (x ≤ y) ≃ (x - y ≤ 0r)
    ≤≃Δ≤0 x y =
      propBiimpl→Equiv (is-prop-valued≤ _ _) (is-prop-valued≤ _ _)
        (≤→Δ≤0 x y) (Δ≤0→≤ x y)

    0≤² : ∀ x → 0r ≤ x · x
    0≤² x = ≥Using< (x · x) 0r λ x²<0 →
      let
        0≤x : 0r ≤ x
        0≤x = ¬<→≥ x 0r λ x<0 → is-irrefl 0r $ begin<
          0r             ≡→≤⟨ sym $ 0LeftAnnihilates (- x) ⟩
          0r · (- x)       <⟨ ∘diag (·MonoR< _ _ _) (<0→0<- x x<0) ⟩
          (- x) · (- x)  ≡→≤⟨ solve! RCR ⟩
          x · x            <⟨ x²<0 ⟩
          0r               ◾
      in
        subst (_≤ x · x) (solve! RCR) (∘diag (·MonoR≤ _ _ _) 0≤x)

    #→0<² : ∀ x → x # 0r → 0r < x · x
    #→0<² x (inl x<0) =
      subst2 _<_ (solve! RCR) (solve! RCR) (∘diag (·MonoR< _ _ _) (<0→0<- x x<0))
    #→0<² x (inr 0<x) =
      subst (_< x · x) (solve! RCR) (∘diag (·MonoR< _ _ _) 0<x)

    ≤abs : ∀ z → z ≤ abs z
    ≤abs z = L≤⊔

    -≤abs : ∀ z → - z ≤ abs z
    -≤abs z = R≤⊔

    0≤abs : ∀ z → 0r ≤ abs z
    0≤abs z = ¬<→≥ (abs z) 0r λ ∣z∣<0 → is-irrefl 0r $ begin<
      0r      ≡→≤⟨ solve! RCR ⟩
      - 0r      <⟨ -Flip< _ _ ∣z∣<0 ⟩
      - abs z   ≤⟨ -Flip≤ _ _ (≤abs z) ⟩
      - z       ≤⟨ -≤abs z ⟩
      abs z     <⟨ ∣z∣<0 ⟩
      0r        ◾

    abs≤0→≡0 : ∀ z → abs z ≤ 0r → z ≡ 0r
    abs≤0→≡0 z ∣z∣≤0 = is-antisym z 0r
      (begin≤
        z     ≤⟨ ≤abs z ⟩
        abs z ≤⟨ ∣z∣≤0 ⟩
        0r         ◾)
      (begin≤
        0r        ≡→≤⟨ solve! RCR ⟩
        - 0r        ≤⟨ -Flip≤ _ _ ∣z∣≤0 ⟩
        - (abs z)   ≤⟨ -Flip≤ _ _ $ -≤abs z ⟩
        - - z     ≡→≤⟨ solve! RCR ⟩
        z           ◾)

    #→0<abs : ∀ z → z # 0r → 0r < abs z
    #→0<abs z (inl z<0) = begin<
      0r    ≡→≤⟨ solve! RCR ⟩
      - 0r    <⟨ -Flip< z 0r z<0 ⟩
      - z     ≤⟨ -≤abs _ ⟩
      abs z   ◾
    #→0<abs z (inr 0<z) = begin<
      0r    <⟨ 0<z ⟩
      z     ≤⟨ ≤abs _ ⟩
      abs z ◾

    abs- : ∀ x → abs (- x) ≡ abs x
    abs- x =
      abs (- x)       ≡⟨⟩
      (- x) ⊔ (- - x) ≡⟨ cong ((- x) ⊔_) (solve! RCR) ⟩
      (- x) ⊔ x       ≡⟨ ⊔Comm ⟩
      x ⊔ (- x)       ≡⟨⟩
      abs x           ∎

    private
      +R≤→≤-R : ∀ x y z → x + z ≤ y → x ≤ y - z
      +R≤→≤-R x y z x+z≤y = begin≤
        x               ≡→≤⟨ solve! RCR ⟩
        (x + z) + (- z)   ≤⟨ +MonoR≤ _ _ (- z) x+z≤y ⟩
        y - z             ◾

      ≤-R→+R≤ : ∀ x y z → x ≤ y - z → x + z ≤ y
      ≤-R→+R≤ x y z x≤y-z = begin≤
        x + z             ≤⟨ +MonoR≤ _ _ z x≤y-z ⟩
        (y - z) + z     ≡→≤⟨ solve! RCR ⟩
        y                 ◾

      +DistR⊔′ : ∀ x y z → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
      +DistR⊔′ x y z = is-antisym _ _
        (≤-R→+R≤ (x ⊔ y) ((x + z) ⊔ (y + z)) z
          (⊔LUB
            (+R≤→≤-R x ((x + z) ⊔ (y + z)) z L≤⊔)
            (+R≤→≤-R y ((x + z) ⊔ (y + z)) z R≤⊔)))
        (⊔LUB
          (+MonoR≤ x (x ⊔ y) z L≤⊔)
          (+MonoR≤ y (x ⊔ y) z R≤⊔))

      +DistL⊔′ : ∀ z x y → z + (x ⊔ y) ≡ (z + x) ⊔ (z + y)
      +DistL⊔′ z x y =
        +Comm z (x ⊔ y)
        ∙ +DistR⊔′ x y z
        ∙ cong₂ _⊔_ (+Comm x z) (+Comm y z)

    abs≡⊔-⊓ : ∀ x y → (x ⊔ y) - (x ⊓ y) ≡ abs (x - y)
    abs≡⊔-⊓ x y =
      (x ⊔ y) - (x ⊓ y)
        ≡⟨ cong ((x ⊔ y) +_) (sym (joinNeg≡negMeet x y)) ⟩
      (x ⊔ y) + ((- x) ⊔ (- y))
        ≡⟨ +DistL⊔′ (x ⊔ y) (- x) (- y) ⟩
      ((x ⊔ y) + (- x)) ⊔ ((x ⊔ y) + (- y))
        ≡⟨ cong₂ _⊔_ (+DistR⊔′ x y (- x)) (+DistR⊔′ x y (- y)) ⟩
      ((x + (- x)) ⊔ (y + (- x))) ⊔
        ((x + (- y)) ⊔ (y + (- y)))
        ≡⟨ cong₂ _⊔_
             (cong₂ _⊔_ (solve! RCR) (solve! RCR))
             (cong₂ _⊔_ (solve! RCR) (solve! RCR)) ⟩
      (0r ⊔ (y - x)) ⊔ ((x - y) ⊔ 0r)
        ≡⟨ sym ⊔Assoc ⟩
      0r ⊔ ((y - x) ⊔ ((x - y) ⊔ 0r))
        ≡⟨ cong (0r ⊔_) ⊔Assoc ⟩
      0r ⊔ (((y - x) ⊔ (x - y)) ⊔ 0r)
        ≡⟨ cong (λ z → 0r ⊔ (z ⊔ 0r)) ⊔Comm ⟩
      0r ⊔ (((x - y) ⊔ (y - x)) ⊔ 0r)
        ≡⟨ cong (0r ⊔_) (≥→⊔≡Left 0≤absΔ) ⟩
      0r ⊔ ((x - y) ⊔ (y - x))
        ≡⟨ ≤→⊔≡Right 0≤absΔ ⟩
      (x - y) ⊔ (y - x)
        ≡⟨ cong ((x - y) ⊔_) (solve! RCR) ⟩
      abs (x - y) ∎
      where
      0≤absΔ : 0r ≤ (x - y) ⊔ (y - x)
      0≤absΔ =
        subst (0r ≤_)
          (cong ((x - y) ⊔_) (solve! RCR))
          (0≤abs (x - y))

    abs-alternate : ∀ n x → abs (alternate n x) ≡ abs x
    abs-alternate zero x = refl
    abs-alternate (suc zero) x = abs- x
    abs-alternate (suc (suc n)) x = abs-alternate n x

    0≤→abs≡id : ∀ x → 0r ≤ x → abs x ≡ x
    0≤→abs≡id x 0≤x = is-antisym (abs x) x
      (⊔LUB (is-refl x) (begin≤ - x ≤⟨ 0≤→-≤0 x 0≤x ⟩ 0r ≤⟨ 0≤x ⟩ x ◾))
      (≤abs x)

    abs-monotoneOnNonNeg : (x y : Σ R (0r ≤_)) →
      fst x ≤ fst y → abs (fst x) ≤ abs (fst y)
    abs-monotoneOnNonNeg x y x≤y =
      subst2 _≤_
        (sym (0≤→abs≡id (fst x) (snd x)))
        (sym (0≤→abs≡id (fst y) (snd y)))
        x≤y

    ≤0→abs≡- : ∀ x → x ≤ 0r → abs x ≡ - x
    ≤0→abs≡- x x≤0 = sym (abs- x) ∙ 0≤→abs≡id (- x) (≤0→0≤- x x≤0)

    0<→abs≡id : ∀ x → 0r < x → abs x ≡ x
    0<→abs≡id x = 0≤→abs≡id x ∘ <-≤-weaken 0r x

    <0→abs≡- : ∀ x → x < 0r → abs x ≡ - x
    <0→abs≡- x = ≤0→abs≡- x ∘ <-≤-weaken x 0r

    ·DistL⊔≥ : ∀ x y z → 0r ≤ x → (x · y) ⊔ (x · z) ≤ x · (y ⊔ z)
    ·DistL⊔≥ _ _ _ 0≤x = ⊔LUB (·MonoL≤ _ _ _ 0≤x L≤⊔) (·MonoL≤ _ _ _ 0≤x R≤⊔)

    0≤→abs·≤ : ∀ k x → 0r ≤ k → abs (k · x) ≤ k · abs x
    0≤→abs·≤ k x 0≤k = ⊔LUB
      (begin≤
        k · x ≤⟨ ·MonoL≤ x (abs x) k 0≤k (≤abs x) ⟩
        k · abs x ◾)
      (begin≤
        - (k · x) ≡→≤⟨ solve! RCR ⟩
        k · (- x)   ≤⟨ ·MonoL≤ (- x) (abs x) k 0≤k (-≤abs x) ⟩
        k · abs x   ◾)

    abs²≡² : ∀ x → abs x · abs x ≡ x · x
    abs²≡² x = is-antisym (abs x · abs x) (x · x)
      (¬<→≥ (x · x) (abs x · abs x) λ x²<∣x∣² →
        let
          0≤x : 0r ≤ x
          0≤x = ¬<→≥ x 0r λ x<0 → is-irrefl (x · x) (begin<
            x · x           <⟨ x²<∣x∣² ⟩
            abs x · abs x ≡→≤⟨ cong (∘diag _·_) (<0→abs≡- x x<0) ∙ solve! RCR ⟩
            x · x           ◾)
        in
          is-irrefl (x · x) (begin<
            x · x           <⟨ x²<∣x∣² ⟩
            abs x · abs x ≡→≤⟨ cong (∘diag _·_) (0≤→abs≡id x 0≤x) ⟩
            x · x           ◾))
      (0≤Δ→≤ (x · x) (abs x · abs x) (begin≤
        0r                          ≡→≤⟨ solve! RCR ⟩
        0r · (abs x - - x)            ≤⟨ ·MonoR≤ 0r _ _ (≤→0≤Δ _ _ (-≤abs x))
                                                        (≤→0≤Δ _ _ (≤abs x)) ⟩
        (abs x - x) · (abs x - - x) ≡→≤⟨ solve! RCR ⟩
        abs x · abs x - x · x         ◾))

    abs²≡²' : ∀ x → abs(x · x) ≡ x · x
    abs²≡²' x = 0≤→abs≡id (x · x) (0≤² x)

    triangularInequality : ∀ x y → abs (x + y) ≤ abs x + abs y
    triangularInequality x y = ⊔LUB
      (begin≤
        x     + y     ≤⟨ +Mono≤ _ _ _ _ (≤abs x) (≤abs y) ⟩
        abs x + abs y ◾)
      (begin≤
        - (x + y)    ≡→≤⟨ solve! RCR ⟩
        (- x) - y      ≤⟨ +Mono≤ _ _ _ _ (-≤abs x) (-≤abs y) ⟩
        abs x + abs y ◾)

    abs-abs≤abs- : ∀ x y → abs x - abs y ≤ abs (x - y)
    abs-abs≤abs- x y =
      subst2 _≤_
        (cong (λ z → abs z - abs y) (solve! RCR))
        (solve! RCR)
        (+MonoR≤ _ _ (- abs y) (triangularInequality (x - y) y))

    triangularInequality- : ∀ x y z → abs (x - y) ≤ abs (x - z) + abs (z - y)
    triangularInequality- x y z = begin≤
      abs (x - y)               ≡→≤⟨ cong abs (solve! RCR) ⟩
      abs ((x - z) + (z - y))     ≤⟨ triangularInequality (x - z) (z - y) ⟩
      abs (x - z) + abs (z - y)   ◾

    abs-Comm : ∀ x y → abs (x - y) ≡ abs (y - x)
    abs-Comm x y =
      abs (x - y)             ≡⟨⟩
      (x - y) ⊔ (- (x - y))   ≡⟨ ⊔Comm ⟩
      (- (x - y)) ⊔ (x - y)   ≡⟨ cong₂ _⊔_ (solve! RCR) (solve! RCR) ⟩
      (y - x) ⊔ (- (y - x))   ≡⟨⟩
      abs (y - x)             ∎

    abs0 : abs 0r ≡ 0r
    abs0 = 0≤→abs≡id 0r (is-refl 0r)

    abs1 : abs 1r ≡ 1r
    abs1 = 0≤→abs≡id 1r 0≤1

    abs-alternatingSign : ∀ n → abs (alternatingSign n) ≡ 1r
    abs-alternatingSign n = abs-alternate n 1r ∙ abs1

  -- TO DO:
  -- - Move the definitions and basic properties of Hom/Mono to a "Mappings" module
  -- - Move the module below to a separate file (either "Mappings" or "Mappings.Properties")
  module CanonicalEmbeddings where
    open OrderedCommRingTheory
    open CanonicalHomFromℤ RCR using (isHomFromℤ ; isContrHom[ℤCR,-])

    1≤fromℕsuc : ∀ n → 1r ≤ R.fromℕ (suc n)
    1≤fromℕsuc zero    = is-refl 1r
    1≤fromℕsuc (suc n) = begin≤
      1r                   ≡→≤⟨ sym (+IdL 1r) ⟩
      0r + 1r                ≤⟨ +Mono≤ _ _ _ _ 0≤1 (1≤fromℕsuc n) ⟩
      1r + R.fromℕ (suc n)  ◾

    0<fromℕsuc : ∀ n → 0r < R.fromℕ (suc n)
    0<fromℕsuc n = <-≤-trans _ _ _ 0<1 (1≤fromℕsuc n)

    0≤fromℕ : ∀ n → 0r ≤ R.fromℕ n
    0≤fromℕ zero    = is-refl 0r
    0≤fromℕ (suc n) = <-≤-weaken _ _ (0<fromℕsuc n)

    fromℕ-pres≤ᵗ : ∀ m n → m ℕ.≤ᵗ n → R.fromℕ m ≤ R.fromℕ n
    fromℕ-pres≤ᵗ zero          n             t = 0≤fromℕ n
    fromℕ-pres≤ᵗ one           (suc n)       t = 1≤fromℕsuc n
    fromℕ-pres≤ᵗ (suc (suc m)) (suc (suc n)) t =
      +MonoL≤ _ _ _ (fromℕ-pres≤ᵗ (suc m) (suc n) t)

    fromℕ-pres≤ : ∀ m n → m ≤ℕ n → R.fromℕ m ≤ R.fromℕ n
    fromℕ-pres≤ m n = fromℕ-pres≤ᵗ m n ∘ ℕ.≤→≤ᵇ

    fromℕ-pres<ᵗ : ∀ m n → m ℕ.<ᵗ n → R.fromℕ m < R.fromℕ n
    fromℕ-pres<ᵗ zero          (suc n)       t = 0<fromℕsuc n
    fromℕ-pres<ᵗ one           (suc (suc n)) t = <SumLeftPos 1r _ (0<fromℕsuc n)
    fromℕ-pres<ᵗ (suc (suc m)) (suc (suc n)) t =
      +MonoL< _ _ _ (fromℕ-pres<ᵗ (suc m) (suc n) t)

    fromℕ-pres< : ∀ m n → m <ℕ n → R.fromℕ m < R.fromℕ n
    fromℕ-pres< m n = fromℕ-pres<ᵗ m n ∘ ℕ.<→<ᵇ

    fromℤ-pres≤ : ∀ m n → m ℤ.≤ n → R.fromℤ m ≤ R.fromℤ n
    fromℤ-pres≤ (pos m)    (pos n)    (pos≤pos p)       = fromℕ-pres≤ᵗ m n p
    fromℤ-pres≤ (negsuc m) (pos n)    negsuc≤pos        = begin≤
      - R.fromℕ (suc m) ≤⟨ 0≤→-≤0 _ (0≤fromℕ (suc m)) ⟩
      0r                ≤⟨ 0≤fromℕ n ⟩
      R.fromℕ n         ◾
    fromℤ-pres≤ (negsuc m) (negsuc n) (negsuc≤negsuc p) =
      -Flip≤ _ _ (fromℕ-pres≤ᵗ (suc n) (suc m) p)

    fromℤ-pres< : ∀ m n → m ℤ.< n → R.fromℤ m < R.fromℤ n
    fromℤ-pres< (pos m)    (pos n)    (pos<pos p)       = fromℕ-pres<ᵗ m n p
    fromℤ-pres< (negsuc m) (pos n)    negsuc<pos        = begin<
      - R.fromℕ (suc m) <⟨ 0<→-<0 _ (0<fromℕsuc m) ⟩
      0r                ≤⟨ 0≤fromℕ n ⟩
      R.fromℕ n         ◾
    fromℤ-pres< (negsuc m) (negsuc n) (negsuc<negsuc p) =
      -Flip< _ _ (fromℕ-pres<ᵗ (suc n) (suc m) p)

    fromℤ-reflect< : ∀ m n → R.fromℤ m < R.fromℤ n → m ℤ.< n
    fromℤ-reflect< m n fm<fn with m ℤ.≟ n
    ... | lt m<n = m<n
    ... | eq m≡n = ⊥.rec (is-irrefl _ (subst (_< _) (cong R.fromℤ m≡n) fm<fn))
    ... | gt m>n = ⊥.rec (is-asym _ _ fm<fn (fromℤ-pres< n m m>n))

    isOCRHomFromℤ : IsOrderedCommRingHom (str ℤOrderedCommRing) R.fromℤ (str R')
    isOCRHomFromℤ .IsOrderedCommRingHom.isCommRingHom = isHomFromℤ
    isOCRHomFromℤ .IsOrderedCommRingHom.pres≤         = fromℤ-pres≤
    isOCRHomFromℤ .IsOrderedCommRingHom.reflect<      = fromℤ-reflect<

    isOCRMonoFromℤ : IsOrderedCommRingMono (str ℤOrderedCommRing) R.fromℤ (str R')
    isOCRMonoFromℤ .IsOrderedCommRingMono.isOrderedCommRingHom = isOCRHomFromℤ
    isOCRMonoFromℤ .IsOrderedCommRingMono.pres<                = fromℤ-pres<

    ℤOCR→R : OrderedCommRingHom ℤOrderedCommRing R'
    fst ℤOCR→R = R.fromℤ
    snd ℤOCR→R = isOCRHomFromℤ

    ℤOCR↣R : OrderedCommRingMono ℤOrderedCommRing R'
    fst ℤOCR↣R = R.fromℤ
    snd ℤOCR↣R = isOCRMonoFromℤ

    isContrHom[ℤOCR,-] : isContr (OrderedCommRingHom ℤOrderedCommRing R')
    fst isContrHom[ℤOCR,-]   = ℤOCR→R
    snd isContrHom[ℤOCR,-] φ = OrderedCommRingHom≡ $
      cong fst (snd isContrHom[ℤCR,-] (fst φ , isCommRingHom))
      where open IsOrderedCommRingHom (snd φ)

    isContrMono[ℤOCR,-] : isContr (OrderedCommRingMono ℤOrderedCommRing R')
    fst isContrMono[ℤOCR,-]   = ℤOCR↣R
    snd isContrMono[ℤOCR,-] φ = OrderedCommRingMono≡ $
      cong fst (snd isContrHom[ℤCR,-] (fst φ , isCommRingHom))
      where open IsOrderedCommRingMono (snd φ)

  module SumTheory where
    open OrderedCommRingTheory
    open Sum (Ring→Semiring (OrderedCommRing→Ring R')) public

    ∑-syntax : ℕ → (ℕ → R) → R
    ∑-syntax n x = ∑ {suc n} λ k → x (toℕ k)

    syntax ∑-syntax n (λ k → xₖ) = ∑[0 ≤ k ≤ n ] xₖ

    ∑Mono≤ : ∀ {n} (x y : FinVec R n) →
             (∀ k → x k ≤ y k) → ∑ x ≤ ∑ y
    ∑Mono≤ {zero} x y x≤y = is-refl 0r
    ∑Mono≤ {suc n} x y x≤y =
      +Mono≤ (x zero) (y zero) (∑ (x ∘ suc)) (∑ (y ∘ suc))
        (x≤y zero) (∑Mono≤ (x ∘ suc) (y ∘ suc) (x≤y ∘ suc))

    ∑Mono< : ∀ {n} (x y : FinVec R n) → 0 <ℕ n →
             (∀ k → x k < y k) → ∑ x < ∑ y
    ∑Mono< {zero} x y 0<n x<y = ⊥.rec (ℕ.¬-<-zero 0<n)
    ∑Mono< {suc n} x y 0<sn x<y = begin<
      x zero + ∑ (x ∘ suc) <⟨ +MonoR< _ _ _ (x<y zero) ⟩
      y zero + ∑ (x ∘ suc) ≤⟨ +MonoL≤ _ _ _
        (∑Mono≤ (x ∘ suc) (y ∘ suc)
          (λ k → <-≤-weaken _ _ (x<y (suc k)))) ⟩
      y zero + ∑ (y ∘ suc) ◾

    pos∑→∃pos : ∀ {n} (x : FinVec R n) →
                0r < ∑ x → ∃[ k ∈ Fin n ] 0r < x k
    pos∑→∃pos {zero} x 0<0 = ⊥.rec (is-irrefl 0r 0<0)
    pos∑→∃pos {suc n} x 0<∑x =
      PT.rec squash₁
        (⊎.rec
          (λ 0<x₀ → ∣ zero , 0<x₀ ∣₁)
          (λ 0<∑tail →
            PT.map (λ (k , 0<xₖ) → suc k , 0<xₖ)
              (pos∑→∃pos (x ∘ suc) 0<∑tail)))
        (posSum→pos∨pos (x zero) (∑ (x ∘ suc)) 0<∑x)

    abs∑≤∑absFinVec : ∀ {n} (x : FinVec R n) →
                      abs (∑ x) ≤ ∑ (abs ∘ x)
    abs∑≤∑absFinVec {zero} x =
      subst (_≤ 0r) (sym abs0) (is-refl 0r)
    abs∑≤∑absFinVec {suc n} x = begin≤
      ∣ x zero + ∑ (x ∘ suc) ∣
        ≤⟨ triangularInequality (x zero) _ ⟩
      ∣ x zero ∣ + ∣ ∑ (x ∘ suc) ∣
        ≤⟨ +MonoL≤ _ _ _ (abs∑≤∑absFinVec (x ∘ suc)) ⟩
      ∣ x zero ∣ + ∑ (abs ∘ x ∘ suc) ◾

    abs∑≤∑abs : ∀ n → (x : ℕ → R) → abs (∑[0 ≤ k ≤ n ] (x k)) ≤ ∑[0 ≤ k ≤ n ] abs (x k)
    abs∑≤∑abs zero    x = flip (subst (abs (x 0 + 0r) ≤_)) (is-refl _) $
      abs (x 0 + 0r) ≡⟨ cong abs (solve! RCR) ⟩
      abs (x 0)      ≡⟨ solve! RCR ⟩
      abs (x 0) + 0r ∎
    abs∑≤∑abs (suc n) x = begin≤
      ∣ x 0 + ∑[0 ≤ k ≤ n ] (x (suc k)) ∣    ≤⟨ triangularInequality (x 0) _ ⟩
      ∣ x 0 ∣ + ∣ ∑[0 ≤ k ≤ n ] (x (suc k)) ∣ ≤⟨ +MonoL≤ _ _ _ (abs∑≤∑abs n (x ∘ suc)) ⟩
      ∑[0 ≤ k ≤ suc n ] ∣ x k ∣              ◾

    geometricSum : ∀ n x → (1r - x) · ∑[0 ≤ k ≤ n ] (x ^ k) ≡ 1r - x ^ (1 +ℕ n)
    geometricSum zero    x = (1r + - x) · (1r + 0r) ≡⟨ solve! RCR ⟩ 1r - (x · 1r) ∎
    geometricSum (suc n) x =
      let
        sₙ = ∑[0 ≤ k ≤ n ] (x ^ k)
        sₙ₊₁ = 1r + ∑[0 ≤ k ≤ n ] (x · (x ^ k))
      in
        (1r - x) · sₙ₊₁                      ≡⟨ step0 ⟩
        (1r - x) · (1r + x · sₙ)             ≡⟨ step1 sₙ ⟩
        (1r - x) + x · ((1r - x) · sₙ)       ≡⟨ step2 ⟩
         1r - x + x · (1r - (x ^ (1 +ℕ n))) ≡⟨ step3 (x ^ (1 +ℕ n)) ⟩
         1r - x ^ (2 +ℕ n)                  ∎
      where
        -- due to the presence of the sum/power term, step1/3 cannot be inlined
        step0 = sym $ cong (((1r - x) ·_) ∘ (1r +_)) (∑Mulrdist {suc n} x ((x ^_) ∘ toℕ))

        step1 : ∀ s → (1r - x) · (1r + x · s) ≡ (1r - x) + x · ((1r - x) · s)
        step1 s = solve! RCR

        step2 = cong ((1r - x +_) ∘ (x ·_)) (geometricSum n x)

        step3 : ∀ p → 1r - x + x · (1r - p) ≡ 1r - x · p
        step3 p = solve! RCR

    0<x<1→x¹⁺ⁿ<1 : ∀ n x → 0r < x → x < 1r → x ^ (1 +ℕ n) < 1r
    0<x<1→x¹⁺ⁿ<1 zero x 0<x x<1 = begin<
      x · 1r ≡→≤⟨ solve! RCR ⟩
      x        <⟨ x<1 ⟩
      1r       ◾
    0<x<1→x¹⁺ⁿ<1 (suc n) x 0<x x<1 = begin<
      x · (x · x ^ n)    <⟨ ·MonoL< _ _ _ 0<x $ 0<x<1→x¹⁺ⁿ<1 n x 0<x x<1 ⟩
      x · 1r           ≡→≤⟨ solve! RCR ⟩
      x                  <⟨ x<1 ⟩
      1r                 ◾

    0<x<1→0<x¹⁺ⁿ : ∀ n x → 0r < x → x < 1r → 0r < x ^ (1 +ℕ n)
    0<x<1→0<x¹⁺ⁿ zero x 0<x x<1 = begin<
      0r        <⟨ 0<x ⟩
      x       ≡→≤⟨ solve! RCR ⟩
      x · 1r    ◾
    0<x<1→0<x¹⁺ⁿ (suc n) x 0<x x<1 = begin<
      0r              ≡→≤⟨ solve! RCR ⟩
      x · 0r            <⟨ ·MonoL< _ _ _ 0<x $ 0<x<1→0<x¹⁺ⁿ n x 0<x x<1 ⟩
      x · (x · x ^ n)   ◾

    GeometricSumPos<1 : ∀ n x → 0r < x → x < 1r
                               → (1r - x) · ∑[0 ≤ k ≤ n ] (x ^ k) ≤ 1r
    GeometricSumPos<1 n x 0<x x<1 = begin≤
      (1r - x) · ∑[0 ≤ k ≤ n ] (x ^ k) ≡→≤⟨ geometricSum n x ∙ sym (+IdR _) ⟩
      1r - x ^ (1 +ℕ n) + 0r             <⟨ +MonoL< _ _ _ (0<x<1→0<x¹⁺ⁿ n x 0<x x<1) ⟩
      1r - x ^ (1 +ℕ n) + x ^ (1 +ℕ n) ≡→≤⟨ lemma (x ^ (1 +ℕ n))  ⟩
      1r                                 ◾
      where
        lemma : ∀ p → (1r - p) + p ≡ 1r
        lemma p = solve! RCR
{-
  module AdditiveSubType
    (P : R → hProp ℓ'')
    (+Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x + y) ⟩)
    where
    open OrderedCommRingTheory

    subtype = Σ[ x ∈ R ] ⟨ P x ⟩

    ι : subtype → R
    ι = fst

    _-subtype_ : subtype → subtype → R
    _-subtype_ x y = ι x - ι y

    _<subtype_ : subtype → subtype → Type ℓ'
    _<subtype_ x y = ι x < ι y

    _≤subtype_ : subtype → subtype → Type ℓ'
    _≤subtype_ x y = ι x ≤ ι y

  module AdditiveAndMultiplicativeSubType
    (P : R → hProp ℓ'')
    (+Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x + y) ⟩)
    (·Closed : (x y : R) → ⟨ P x ⟩ → ⟨ P y ⟩ → ⟨ P (x · y) ⟩)
    where
    open AdditiveSubType P +Closed public

  -- this module can be used to form the positive cone,
  -- using an alternative implementation of the comparison wit 0.
  module Positiveᵗ
    (0<ᵗ_ : R → Type ℓ')
    (is-prop-valued-0<ᵗ : ∀ x → isProp (0<ᵗ x))
    (0<ᵗ→0< : ∀ {x} → (0<ᵗ x) → (0r < x))
    (0<→0<ᵗ : ∀ {x} → (0r < x) → (0<ᵗ x))
    where
    open OrderedCommRingTheory
    open Positive using (0<+Closed ; 0<·Closed) renaming (selfSeparated to selfSeparated')

    0<≃0<ᵗ : ∀ {x} → (0r < x) ≃ (0<ᵗ x)
    0<≃0<ᵗ = propBiimpl→Equiv (is-prop-valued< 0r _) (is-prop-valued-0<ᵗ _) 0<→0<ᵗ 0<ᵗ→0<

    0<≡0<ᵗ : ∀ x → (0r < x) ≡ (0<ᵗ x)
    0<≡0<ᵗ x = ua 0<≃0<ᵗ

    0<ᵗ+Closed : ∀ x y → 0<ᵗ x → 0<ᵗ y → 0<ᵗ (x + y)
    0<ᵗ+Closed x y 0<x 0<y = 0<→0<ᵗ (0<+Closed x y (0<ᵗ→0< 0<x) (0<ᵗ→0< 0<y))

    0<ᵗ·Closed : ∀ x y → 0<ᵗ x → 0<ᵗ y → 0<ᵗ (x · y)
    0<ᵗ·Closed x y 0<x 0<y = 0<→0<ᵗ (0<·Closed x y (0<ᵗ→0< 0<x) (0<ᵗ→0< 0<y))

    open AdditiveAndMultiplicativeSubType
      (λ x → 0<ᵗ x , is-prop-valued-0<ᵗ x) 0<ᵗ+Closed 0<ᵗ·Closed renaming (
        subtype to R₊ ; ι to ⟨_⟩₊
      ; _-subtype_ to _-₊_ ; _≤subtype_ to _≤₊_ ; _<subtype_ to _<₊_) public

    R₊≡ = Σ≡Prop is-prop-valued-0<ᵗ

    R₊AdditiveSemigroup : Semigroup _
    fst R₊AdditiveSemigroup = R₊
    SemigroupStr._·_ (snd R₊AdditiveSemigroup) = _+₊_ where
      _+₊_ : R₊ → R₊ → R₊
      (x +₊ y) .fst = fst x + fst y
      (x +₊ y) .snd = 0<ᵗ+Closed (fst x) (fst y) (snd x) (snd y)
    SemigroupStr.isSemigroup (snd R₊AdditiveSemigroup) = isSG
      where
        isSG : IsSemigroup _
        isSG .IsSemigroup.is-set = isSetΣSndProp is-set is-prop-valued-0<ᵗ
        isSG .IsSemigroup.·Assoc = λ _ _ _ → R₊≡ (+Assoc _ _ _)

    open SemigroupStr (snd R₊AdditiveSemigroup) using () renaming (_·_ to _+₊_) public

    R₊MultiplicativeCommMonoid : CommMonoid _
    fst R₊MultiplicativeCommMonoid = R₊
    CommMonoidStr.ε   (snd R₊MultiplicativeCommMonoid) = 1r , 0<→0<ᵗ 0<1
    CommMonoidStr._·_ (snd R₊MultiplicativeCommMonoid) = _·₊_ where
      _·₊_ : R₊ → R₊ → R₊
      (x ·₊ y) .fst = fst x · fst y
      (x ·₊ y) .snd = 0<ᵗ·Closed (fst x) (fst y) (snd x) (snd y)
    CommMonoidStr.isCommMonoid (snd R₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        (isSetΣSndProp is-set is-prop-valued-0<ᵗ)
        (λ _ _ _ → R₊≡ (·Assoc _ _ _))
        (λ _     → R₊≡ (·IdR _))
        (λ _ _   → R₊≡ (·Comm _ _))

    open CommMonoidStr (snd R₊MultiplicativeCommMonoid) using () renaming (
      ε to 1₊ ; _·_ to _·₊_) public

    _⊔₊_ : R₊ → R₊ → R₊
    (x ⊔₊ y) .fst = ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊
    (x ⊔₊ y) .snd = 0<→0<ᵗ (<-≤-trans _ _ _ (0<ᵗ→0< (snd x)) L≤⊔)

    selfSeparated : ∀ (x y : R) → (∀ (z : R₊) → abs(x - y) < ⟨ z ⟩₊) → x ≡ y
    selfSeparated x y = subst
      (λ (X : R → Type _) → (((z : Σ R X) → abs(x - y) < (fst z)) → x ≡ y))
      (λ i x → 0<≡0<ᵗ x i)
      (selfSeparated' x y)
-}
  module AdditiveSubType
    (P : R → Type ℓ'')
    (P-prop : ∀ x → isProp (P x))
    (+Closed : (x y : R) → P x → P y → P (x + y))
    where
    open OrderedCommRingTheory

    subtype = Σ[ x ∈ R ] P x

    isSetSubtype : isSet subtype
    isSetSubtype = isSetΣSndProp is-set P-prop

    ι : subtype → R
    ι = fst

    subtype≡ : ∀ {x y} → ι x ≡ ι y → x ≡ y
    subtype≡ = Σ≡Prop P-prop

    _+subtype_ : subtype → subtype → subtype
    (x +subtype y) .fst = fst x + fst y
    (x +subtype y) .snd = +Closed (fst x) (fst y) (snd x) (snd y)

    _-subtype_ : subtype → subtype → R
    _-subtype_ x y = ι x - ι y

    _<subtype_ : subtype → subtype → Type ℓ'
    _<subtype_ x y = ι x < ι y

    _≤subtype_ : subtype → subtype → Type ℓ'
    _≤subtype_ x y = ι x ≤ ι y

    infixl 6 _+subtype_ _-subtype_
    infix  4 _<subtype_ _≤subtype_

  module AdditiveAndMultiplicativeSubType
    (P : R → Type ℓ'')
    (P-prop : ∀ x → isProp (P x))
    (+Closed : (x y : R) → P x → P y → P (x + y))
    (·Closed : (x y : R) → P x → P y → P (x · y))
    where
    open AdditiveSubType P P-prop +Closed public

    opaque
     ·subtype-prf : (x y : R) → P x → P y → P (x · y)
     ·subtype-prf = ·Closed
    
    _·subtype_ : subtype → subtype → subtype
    (x ·subtype y) .fst = fst x · fst y
    (x ·subtype y) .snd = ·subtype-prf (fst x) (fst y) (snd x) (snd y)

    infixl 7 _·subtype_

  -- Of course +Closed and ·Closed are derivable, but for concrete instances
  -- (like the rationals) it's more efficient to use alternative proofs
  module Positive
    (0<+Closed : (x y : R) → 0r < x → 0r < y → 0r < x + y)
    (0<·Closed : (x y : R) → 0r < x → 0r < y → 0r < x · y)
    where

    open AdditiveAndMultiplicativeSubType
      (0r <_) (is-prop-valued< 0r) 0<+Closed 0<·Closed public renaming (
        subtype to R₊ ; isSetSubtype to isSetR₊ ; ι to ⟨_⟩₊ ; subtype≡ to R₊≡
      ; _+subtype_ to _+₊_ ; _·subtype_ to _·₊_ ; _-subtype_ to _-₊_
      ; _≤subtype_ to _≤₊_ ; _<subtype_ to _<₊_)

    open OrderedCommRingTheory

    R₊AdditiveSemigroup : Semigroup _
    fst R₊AdditiveSemigroup = R₊
    SemigroupStr._·_ (snd R₊AdditiveSemigroup) = _+₊_
    SemigroupStr.isSemigroup (snd R₊AdditiveSemigroup) = isSG
      where
        isSG : IsSemigroup _
        isSG .IsSemigroup.is-set = isSetR₊
        isSG .IsSemigroup.·Assoc = λ _ _ _ → R₊≡ (+Assoc _ _ _)

    open SemigroupStr (snd R₊AdditiveSemigroup) public hiding (_·_) renaming (
      ·Assoc to +₊Assoc)

    R₊MultiplicativeCommMonoid : CommMonoid _
    fst R₊MultiplicativeCommMonoid = R₊
    CommMonoidStr.ε   (snd R₊MultiplicativeCommMonoid) = 1r , 0<1
    CommMonoidStr._·_ (snd R₊MultiplicativeCommMonoid) = _·₊_
    CommMonoidStr.isCommMonoid (snd R₊MultiplicativeCommMonoid) =
      makeIsCommMonoid
        isSetR₊
        (λ _ _ _ → R₊≡ (·Assoc _ _ _))
        (λ _     → R₊≡ (·IdR _))
        (λ _ _   → R₊≡ (·Comm _ _))

    open CommMonoidStr (snd R₊MultiplicativeCommMonoid) public hiding (_·_) renaming (
      ε to 1₊ ; ·Assoc to ·₊Assoc ; ·IdR to ·₊IdR ; ·Comm to ·₊Comm)

    infix 9 _^₊_
    _^₊_ : R₊ → ℕ → R₊
    (x ^₊ n) .fst = ⟨ x ⟩₊ ^ n
    (x ^₊ n) .snd = powPositive ⟨ x ⟩₊ n (snd x)

    selfSeparated : ∀ (x y : R) → (∀ (z : R₊) → abs(x - y) < ⟨ z ⟩₊) → x ≡ y
    selfSeparated x y ∀[•]∣x-y∣<• =
      let
        ∣x-y∣≤0 : abs(x - y) ≤ 0r
        ∣x-y∣≤0 = ¬<→≥ 0r (abs(x - y)) λ 0<∣x-y∣ → is-irrefl (abs(x - y)) $ begin<
          abs(x - y) <⟨ ∀[•]∣x-y∣<• (abs(x - y) , 0<∣x-y∣) ⟩
          abs(x - y) ◾

        x-y≡0 : x - y ≡ 0r
        x-y≡0 = abs≤0→≡0 (x - y) ∣x-y∣≤0
      in
        equalByDifference x y x-y≡0

    _⊔₊_ : R₊ → R₊ → R₊
    (x ⊔₊ y) .fst = ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊
    (x ⊔₊ y) .snd = begin< 0r <⟨ snd x ⟩ ⟨ x ⟩₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₊ ⊔ ⟨ y ⟩₊ ◾

    plusMinus₊ : ∀ x y → (x +₊ y) -₊ y ≡ ⟨ x ⟩₊
    plusMinus₊ (x , _) (y , _) = solve! RCR

    minusPlus₊ : ∀ x y → x -₊ y + ⟨ y ⟩₊ ≡ ⟨ x ⟩₊
    minusPlus₊ (x , _) (y , _) = solve! RCR

    ≡₊→0< : ∀ {x} y → x ≡ ⟨ y ⟩₊ → 0r < x
    ≡₊→0< y p = subst (0r <_) (sym p) (snd y)

    infixl 6 -₊<
    -₊< : ∀ x y → y <₊ x → R₊
    -₊< x y y<x .fst = x -₊ y
    -₊< x y y<x .snd = <→0<Δ ⟨ y ⟩₊ ⟨ x ⟩₊ y<x

    syntax -₊< x y y<x = x -₊[ y<x ] y

    [_-₊_]⟨_⟩ : ∀ x y → y <₊ x → R₊
    [_-₊_]⟨_⟩ = -₊<

    <₊SumLeft : ∀ x y → x <₊ x +₊ y
    <₊SumLeft (x , _) (y , 0<y) = begin<
      x ≡→≤⟨ solve! RCR ⟩ x + 0r <⟨ +MonoL< _ _ _ 0<y ⟩ x + y ◾

    <₊SumRight : ∀ x y → x <₊ y +₊ x
    <₊SumRight (x , _) (y , 0<y) = begin<
      x ≡→≤⟨ solve! RCR ⟩ 0r + x <⟨ +MonoR< _ _ _ 0<y ⟩ y + x ◾

    Δ<₊ : ∀ x y → x -₊ y < ⟨ x ⟩₊
    Δ<₊ (x , _) (y , 0<y) = begin<
      x - y <⟨ +MonoL< _ _ _ (-Flip< 0r y 0<y) ⟩ x - 0r ≡→≤⟨ solve! RCR ⟩ x ◾

  module NonNegative
    (0≤+Closed : (x y : R) → 0r ≤ x → 0r ≤ y → 0r ≤ x + y)
    (0≤·Closed : (x y : R) → 0r ≤ x → 0r ≤ y → 0r ≤ x · y)
    where

    open AdditiveAndMultiplicativeSubType
      (0r ≤_) (is-prop-valued≤ 0r) 0≤+Closed 0≤·Closed public renaming (
        subtype to R₀₊ ; isSetSubtype to isSetR₀₊ ; ι to ⟨_⟩₀₊ ; subtype≡ to R₀₊≡
      ; _+subtype_ to _+₀₊_ ; _·subtype_ to _·₀₊_ ; _-subtype_ to _-₀₊_
      ; _≤subtype_ to _≤₀₊_ ; _<subtype_ to _<₀₊_)

    open OrderedCommRingTheory

    R₀₊CommSemiring : CommSemiring _
    fst R₀₊CommSemiring = R₀₊
    CommSemiringStr.0r  (snd R₀₊CommSemiring) = 0r , is-refl _
    CommSemiringStr.1r  (snd R₀₊CommSemiring) = 1r , <-≤-weaken _ _ 0<1
    CommSemiringStr._+_ (snd R₀₊CommSemiring) = _+₀₊_
    CommSemiringStr._·_ (snd R₀₊CommSemiring) = _·₀₊_
    CommSemiringStr.isCommSemiring (snd R₀₊CommSemiring) =
      makeIsCommSemiring
        isSetR₀₊
        (λ _ _ _ → R₀₊≡ (+Assoc _ _ _))
        (λ _     → R₀₊≡ (+IdR _))
        (λ _ _   → R₀₊≡ (+Comm _ _))
        (λ _ _ _ → R₀₊≡ (·Assoc _ _ _))
        (λ _     → R₀₊≡ (·IdR _))
        (λ _ _ _ → R₀₊≡ (·DistR+ _ _ _))
        (λ _     → R₀₊≡ (0LeftAnnihilates _))
        (λ _ _   → R₀₊≡ (·Comm _ _))

    open CommSemiringStr (snd R₀₊CommSemiring) public hiding (_+_ ; _·_)
      renaming (
        0r to 0₀₊ ; 1r to 1₀₊
      ; +Assoc to +₀₊Assoc ; +IdL to +₀₊IdL ; +IdR to +₀₊IdR ; +Comm to +₀₊Comm
      ; ·Assoc to ·₀₊Assoc ; ·IdL to ·₀₊IdL ; ·IdR to ·₀₊IdR ; ·Comm to ·₀₊Comm
      ; ·DistL+ to ·₀₊DistL+₀₊ ; ·DistR+ to ·₀₊DistR+₀₊
      ; AnnihilL to AnnihilL₀₊ ; AnnihilR to AnnihilR₀₊)

    infix 9 _^₀₊_
    _^₀₊_ : R₀₊ → ℕ → R₀₊
    (x ^₀₊ n) .fst = ⟨ x ⟩₀₊ ^ n
    (x ^₀₊ n) .snd = powNonnegative ⟨ x ⟩₀₊ n (snd x)

    _⊔₀₊_ : R₀₊ → R₀₊ → R₀₊
    (x ⊔₀₊ y) .fst = ⟨ x ⟩₀₊ ⊔ ⟨ y ⟩₀₊
    (x ⊔₀₊ y) .snd = begin≤ 0r ≤⟨ snd x ⟩ ⟨ x ⟩₀₊ ≤⟨ L≤⊔ ⟩ ⟨ x ⟩₀₊ ⊔ ⟨ y ⟩₀₊ ◾

    _⊓₀₊_ : R₀₊ → R₀₊ → R₀₊
    (x ⊓₀₊ y) .fst = ⟨ x ⟩₀₊ ⊓ ⟨ y ⟩₀₊
    (x ⊓₀₊ y) .snd = ⊓GLB (snd x) (snd y)

    plusMinus₀₊ : ∀ x y → (x +₀₊ y) -₀₊ y ≡ ⟨ x ⟩₀₊
    plusMinus₀₊ (x , _) (y , _) = solve! RCR

    minusPlus₀₊ : ∀ x y → x -₀₊ y + ⟨ y ⟩₀₊ ≡ ⟨ x ⟩₀₊
    minusPlus₀₊ (x , _) (y , _) = solve! RCR

    ≡₀₊→0≤ : ∀ {x} y → x ≡ ⟨ y ⟩₀₊ → 0r ≤ x
    ≡₀₊→0≤ y p = subst (0r ≤_) (sym p) (snd y)

    infixl 6 -₀₊≤
    -₀₊≤ : ∀ x y → y ≤₀₊ x → R₀₊
    -₀₊≤ x y y≤x .fst = x -₀₊ y
    -₀₊≤ x y y≤x .snd = ≤→0≤Δ ⟨ y ⟩₀₊ ⟨ x ⟩₀₊ y≤x

    syntax -₀₊≤ x y y≤x = x -₀₊[ y≤x ] y

    [_-₀₊_]⟨_⟩ : ∀ x y → y ≤₀₊ x → R₀₊
    [_-₀₊_]⟨_⟩ = -₀₊≤


    ≤₀₊SumLeft : ∀ x y → x ≤₀₊ x +₀₊ y
    ≤₀₊SumLeft (x , _) (y , 0≤y) = begin≤
      x ≡→≤⟨ solve! RCR ⟩ x + 0r ≤⟨ +MonoL≤ _ _ _ 0≤y ⟩ x + y ◾

    ≤₀₊SumRight : ∀ x y → x ≤₀₊ y +₀₊ x
    ≤₀₊SumRight (x , _) (y , 0≤y) = begin≤
      x ≡→≤⟨ solve! RCR ⟩ 0r + x ≤⟨ +MonoR≤ _ _ _ 0≤y ⟩ y + x ◾

    Δ≤₀₊ : ∀ x y → x -₀₊ y ≤ ⟨ x ⟩₀₊
    Δ≤₀₊ (x , _) (y , 0≤y) = begin≤
      x - y ≤⟨ +MonoL≤ _ _ _ (-Flip≤ 0r y 0≤y) ⟩ x - 0r ≡→≤⟨ solve! RCR ⟩ x ◾

  private
    2r = 1r + 1r

  module Characteristic≠2 (1/2 : R) (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r) where
    open OrderedCommRingTheory

    1/2+1/2≡1 : 1/2 + 1/2 ≡ 1r
    1/2+1/2≡1 =
      1/2 + 1/2 ≡⟨ solve! RCR ⟩
      1/2 · 2r  ≡⟨ 1/2≡2⁻¹ ⟩
      1r        ∎

    0<1/2 : 0r < 1/2
    0<1/2 = flip (PT.rec (is-prop-valued< 0r 1/2))
      (posSum→pos∨pos 1/2 1/2 (subst (0r <_) (sym 1/2+1/2≡1) 0<1)) λ
      { (inl 0<1/2) → 0<1/2
      ; (inr 0<1/2) → 0<1/2
      }

    0≤1/2 : 0r ≤ 1/2
    0≤1/2 = <-≤-weaken _ _ 0<1/2

    _/2 : R → R
    _/2 = _· 1/2

    _/4 : R → R
    _/4 = _/2 ∘ _/2

    mean : R → R → R
    mean x y = (x + y) · 1/2

    meanIdem : ∀ x → mean x x ≡ x
    meanIdem x =
      (x + x) · 1/2     ≡⟨ solve! RCR ⟩
      x · (1/2 + 1/2)   ≡⟨ cong (x ·_) 1/2+1/2≡1 ⟩
      x · 1r            ≡⟨ solve! RCR ⟩
      x                 ∎

    <→<mean : ∀ x y → x < y → x < mean x y
    <→<mean x y x<y = begin<
      x             ≡→≤⟨ sym (meanIdem x) ⟩
      (x + x) · 1/2   <⟨ ·MonoR< (x + x) (x + y) 1/2 0<1/2 (+MonoL< x y x x<y) ⟩
      (x + y) · 1/2   ◾

    <→mean< : ∀ x y → x < y → mean x y < y
    <→mean< x y x<y = begin<
      (x + y) · 1/2   <⟨ ·MonoR< (x + y) (y + y) 1/2 0<1/2 (+MonoR< x y y x<y) ⟩
      (y + y) · 1/2 ≡→≤⟨ meanIdem y ⟩
      y               ◾

    /2+/2≡id : ∀ x → x /2 + x /2 ≡ x
    /2+/2≡id x = solve! RCR ∙ meanIdem x

    id-/2≡/2 : ∀ x → x - x /2 ≡ x /2
    id-/2≡/2 x = cong (_- x /2) (sym (/2+/2≡id x)) ∙ solve! RCR

    /4+/4≡/2 : ∀ x → x /4 + x /4 ≡ x /2
    /4+/4≡/2 = /2+/2≡id ∘ (_/2)

    /4+/4+/4+/4≡id : ∀ x → (x /4 + x /4) + (x /4 + x /4) ≡ x
    /4+/4+/4+/4≡id x = cong (∘diag _+_) (/4+/4≡/2 x) ∙ /2+/2≡id x


    /2-/4≡/4 : ∀ x → x /2 - x /4 ≡ x /4
    /2-/4≡/4 = id-/2≡/2 ∘ (_/2)

    id-[/4+/4]≡/2 : ∀ x → x - (x /4 + x /4) ≡ x /2
    id-[/4+/4]≡/2 x = cong (_-_ x) (/4+/4≡/2 x) ∙ id-/2≡/2 x

  module PositiveHalves
    (1/2 : R)
    (1/2≡2⁻¹ : 1/2 · 2r ≡ 1r)
    (0<+Closed : (x y : R) → 0r < x → 0r < y → 0r < x + y)
    (0<·Closed : (x y : R) → 0r < x → 0r < y → 0r < x · y)
    where

    open Characteristic≠2 1/2 1/2≡2⁻¹
    open Positive 0<+Closed 0<·Closed
    open OrderedCommRingTheory

    _/2₊ : R₊ → R₊
    _/2₊ = _·₊ (1/2 , 0<1/2)

    _/4₊ : R₊ → R₊
    _/4₊ = _/2₊ ∘ _/2₊

    /2₊<id : ∀ x → (x /2₊) <₊ x
    /2₊<id x = begin<
      ⟨ x /2₊ ⟩₊            <⟨ <₊SumLeft (x /2₊) (x /2₊) ⟩
      ⟨ x /2₊ +₊ x /2₊ ⟩₊ ≡→≤⟨ /2+/2≡id ⟨ x ⟩₊ ⟩
      ⟨ x ⟩₊                ◾

    /4₊</2₊ : ∀ x → (x /4₊) <₊ (x /2₊)
    /4₊</2₊ = /2₊<id ∘ _/2₊

    /4₊<id : ∀ x → (x /4₊) <₊ x
    /4₊<id x = begin<
      ⟨ x /4₊ ⟩₊ <⟨ /4₊</2₊ x ⟩
      ⟨ x /2₊ ⟩₊ <⟨ /2₊<id x ⟩
      ⟨ x ⟩₊     ◾

    mean₊ : R₊ → R₊ → R₊
    mean₊ x y = (x +₊ y) /2₊

    <₊→<₊mean₊ : ∀ x y → x <₊ y → x <₊ mean₊ x y
    <₊→<₊mean₊ x y = <→<mean ⟨ x ⟩₊ ⟨ y ⟩₊

    <₊→mean₊<₊ : ∀ x y → x <₊ y → mean₊ x y <₊ y
    <₊→mean₊<₊ x y = <→mean< ⟨ x ⟩₊ ⟨ y ⟩₊

    -- -- id-/2₊ : ∀ x → 0r < x -₊ (x /2₊)
    -- -- id-/2₊ x = subst (0r <_) (sym (id-/2≡/2 ⟨ x ⟩₊)) (snd (x /2₊))

    -- -- id-[/4+/4]₊ : ∀ x → 0r < x -₊ (x /4₊ +₊ x /4₊)
    -- -- id-[/4+/4]₊ x = subst (0r <_) (cong (_-_ ⟨ x ⟩₊) (sym (/4+/4≡/2 ⟨ x ⟩₊))) (id-/2₊ x)
