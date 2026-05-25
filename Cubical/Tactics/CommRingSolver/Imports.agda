module Cubical.Tactics.CommRingSolver.Imports where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Structure

-- open import Cubical.Data.FinData
-- open import Cubical.Data.Nat using (ℕ;suc;zero;predℕ)
-- import Cubical.Data.Nat as ℕ
-- open import Cubical.Data.Nat.Order as ℕ using (zero-≤)
open import Cubical.Data.Vec as Vec public
-- open import Cubical.Data.Sigma
-- import Cubical.Data.Prod as ×
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.NatPlusOne
open import Cubical.Data.List as L using (_∷_ ; []) public
-- open import Cubical.Data.List.Dependent
-- open import Cubical.Data.Bool as 𝟚 hiding (_≟_)
open import Cubical.Data.Maybe as Mb public

-- open import Cubical.Data.Unit
-- open import Cubical.Data.Sum as ⊎
-- open import Cubical.Relation.Nullary

-- open import Cubical.Reflection.Sugar


-- open import Cubical.Algebra.CommRing
-- open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.RawAlgebra hiding (⟨_⟩) public
open import Cubical.Tactics.CommRingSolver.AlgebraExpression public
open import Cubical.Tactics.CommRingSolver.HornerForms public
open import Cubical.Tactics.CommRingSolver.RawRing hiding (⟨_⟩) public
open import Cubical.Tactics.CommRingSolver.EvalHom public
open import Cubical.Tactics.CommRingSolver.Config public
open import Cubical.Tactics.CommRingSolver.Solver public
open import Cubical.Tactics.CommRingSolver.Reflection public

-- open import Cubical.Algebra.Ring.BigOps
open import Cubical.Data.FinData renaming (punchOut to punchOut' ; elim to elimFin ; rec to elimRec) public
