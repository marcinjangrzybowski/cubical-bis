module Cubical.HITs.CauchyReals.Algebra.Order.Addition.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Unit using (tt)

open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance


private
  module ℝOrder = OrderedCommRingTheory ℝOrderedCommRing

  zeroℝ : ℝ
  zeroℝ = ℕ.HasFromNat.fromNat fromNatℝ ℕ.zero {{tt}}


≤-o+-cancel : ∀ m n o → o +ᵣ m ≤ᵣ o +ᵣ n → m ≤ᵣ n
≤-o+-cancel m n o = ℝOrder.+CancelL≤ m n o


≤-+o-cancel : ∀ m n o → m +ᵣ o ≤ᵣ n +ᵣ o → m ≤ᵣ n
≤-+o-cancel m n o = ℝOrder.+CancelR≤ m n o


<-+o-cancel : ∀ m n o → m +ᵣ o <ᵣ n +ᵣ o → m <ᵣ n
<-+o-cancel m n o = ℝOrder.+CancelR< m n o


<ᵣ-o+-cancel : ∀ m n o → o +ᵣ m <ᵣ o +ᵣ n → m <ᵣ n
<ᵣ-o+-cancel m n o = ℝOrder.+CancelL< m n o


opaque
 x+y≤z+y≃x≤z : ∀ x z y → (x +ᵣ y ≤ᵣ z +ᵣ y) ≃ (x ≤ᵣ z)
 x+y≤z+y≃x≤z x z y = ℝOrder.+CancelR≤≃ x z y


 x+y<z+y≃x<z : ∀ x z y → (x +ᵣ y <ᵣ z +ᵣ y) ≃ (x <ᵣ z)
 x+y<z+y≃x<z x z y = ℝOrder.+CancelR<≃ x z y


 x+y<x+z≃y<z : ∀ x z y → (x +ᵣ y <ᵣ x +ᵣ z) ≃ (y <ᵣ z)
 x+y<x+z≃y<z x z y = ℝOrder.+CancelL<≃ y z x


 x≤y→0≤y-x : ∀ x y → x ≤ᵣ y → zeroℝ ≤ᵣ y -ᵣ x
 x≤y→0≤y-x x y = ℝOrder.≤→0≤Δ x y


 x<y≃0<y-x : ∀ x y → (x <ᵣ y) ≃ (zeroℝ <ᵣ y -ᵣ x)
 x<y≃0<y-x x y = ℝOrder.<≃0<Δ x y


 x<y≃-y<-x : ∀ x y → (x <ᵣ y) ≃ (-ᵣ y <ᵣ -ᵣ x)
 x<y≃-y<-x x y = ℝOrder.-Flip<≃ x y


 x<y→x-y<0 : ∀ x y → x <ᵣ y → x -ᵣ y <ᵣ zeroℝ
 x<y→x-y<0 x y = ℝOrder.<→Δ<0 x y


 x-y<0→x<y : ∀ x y → x -ᵣ y <ᵣ zeroℝ → x <ᵣ y
 x-y<0→x<y x y = ℝOrder.Δ<0→< x y


 x<y≃x-y<0 : ∀ x y → (x <ᵣ y) ≃ (x -ᵣ y <ᵣ zeroℝ)
 x<y≃x-y<0 x y = ℝOrder.<≃Δ<0 x y


 x≤y→x-y≤0 : ∀ x y → x ≤ᵣ y → x -ᵣ y ≤ᵣ zeroℝ
 x≤y→x-y≤0 x y = ℝOrder.≤→Δ≤0 x y


 x-y≤0→x≤y : ∀ x y → x -ᵣ y ≤ᵣ zeroℝ → x ≤ᵣ y
 x-y≤0→x≤y x y = ℝOrder.Δ≤0→≤ x y


 x≤y≃x-y≤0 : ∀ x y → (x ≤ᵣ y) ≃ (x -ᵣ y ≤ᵣ zeroℝ)
 x≤y≃x-y≤0 x y = ℝOrder.≤≃Δ≤0 x y


 a-b≤c⇒a-c≤b : ∀ a b c → a -ᵣ b ≤ᵣ c → a -ᵣ c ≤ᵣ b
 a-b≤c⇒a-c≤b a b c = ℝOrder.x-y≤z→x-z≤y a b c


 a-b≤c⇒a≤c+b : ∀ a b c → a -ᵣ b ≤ᵣ c → a ≤ᵣ c +ᵣ b
 a-b≤c⇒a≤c+b a b c = ℝOrder.x-y≤z→x≤z+y a b c


 a<c+b⇒a-b<c : ∀ a b c → a <ᵣ c +ᵣ b → a -ᵣ b <ᵣ c
 a<c+b⇒a-b<c a b c = ℝOrder.x<z+y→x-y<z a b c


 a≤c+b⇒a-c≤b : ∀ a b c → a ≤ᵣ c +ᵣ b → a -ᵣ c ≤ᵣ b
 a≤c+b⇒a-c≤b a b c = ℝOrder.x≤z+y→x-z≤y a b c


 a+b≤c⇒b≤c-b : ∀ a b c → a +ᵣ b ≤ᵣ c → b ≤ᵣ c -ᵣ a
 a+b≤c⇒b≤c-b a b c = ℝOrder.x+y≤z→y≤z-x a b c


 b≤c-b⇒a+b≤c : ∀ a b c → b ≤ᵣ c -ᵣ a → a +ᵣ b ≤ᵣ c
 b≤c-b⇒a+b≤c a b c = ℝOrder.y≤z-x→x+y≤z a b c


 a-b≤c-d⇒a+d≤c+b :
   ∀ a b c d → a -ᵣ b ≤ᵣ c -ᵣ d → a +ᵣ d ≤ᵣ c +ᵣ b
 a-b≤c-d⇒a+d≤c+b a b c d =
   ℝOrder.x-y≤z-w→x+w≤z+y a b c d


 a+d≤c+b⇒a-b≤c-d :
   ∀ a b c d → a +ᵣ d ≤ᵣ c +ᵣ b → a -ᵣ b ≤ᵣ c -ᵣ d
 a+d≤c+b⇒a-b≤c-d a b c d =
   ℝOrder.x+w≤z+y→x-y≤z-w a b c d


 b<c-b⇒a+b<c : ∀ a b c → b <ᵣ c -ᵣ a → a +ᵣ b <ᵣ c
 b<c-b⇒a+b<c a b c = ℝOrder.y<z-x→x+y<z a b c


 a≤b-c⇒c≤b-a : ∀ a b c → a ≤ᵣ b -ᵣ c → c ≤ᵣ b -ᵣ a
 a≤b-c⇒c≤b-a a b c = ℝOrder.x≤y-z→z≤y-x a b c


 a<b-c⇒c<b-a : ∀ a b c → a <ᵣ b -ᵣ c → c <ᵣ b -ᵣ a
 a<b-c⇒c<b-a a b c = ℝOrder.x<y-z→z<y-x a b c


 a<b-c⇒a+c<b : ∀ a b c → a <ᵣ b -ᵣ c → a +ᵣ c <ᵣ b
 a<b-c⇒a+c<b a b c = ℝOrder.x<y-z→x+z<y a b c


 a+c<b⇒a<b-c : ∀ a b c → a +ᵣ c <ᵣ b → a <ᵣ b -ᵣ c
 a+c<b⇒a<b-c a b c = ℝOrder.x+z<y→x<y-z a b c


 a-b<c⇒a-c<b : ∀ a b c → a -ᵣ b <ᵣ c → a -ᵣ c <ᵣ b
 a-b<c⇒a-c<b a b c = ℝOrder.x-y<z→x-z<y a b c


 x<y→0<y-x : ∀ x y → x <ᵣ y → zeroℝ <ᵣ y -ᵣ x
 x<y→0<y-x x y = ℝOrder.<→0<Δ x y


 a-b<c⇒a<c+b : ∀ a b c → a -ᵣ b <ᵣ c → a <ᵣ c +ᵣ b
 a-b<c⇒a<c+b a b c = ℝOrder.x-y<z→x<z+y a b c


 ≤Weaken<+ᵣ : ∀ x y (z : ℝ₊) → x ≤ᵣ y → x <ᵣ y +ᵣ fst z
 ≤Weaken<+ᵣ x y z x≤y =
   ℝOrder.≤→<SumLeftPos x y (fst z) x≤y (snd z)
