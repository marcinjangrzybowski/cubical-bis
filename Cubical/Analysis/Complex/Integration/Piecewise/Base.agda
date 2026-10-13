module Cubical.Analysis.Complex.Integration.Piecewise.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Graph.Base
import Cubical.Data.Graph.Path as GraphPath
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base

-- Keep each piece's ordered parameter interval. Adjacent geometric endpoints
-- agree, but velocities need not agree at a corner. The finite chain and its
-- concatenation are the library's existing graph-path construction.
ComplexPathPiece : ℂ → ℂ → Type₀
ComplexPathPiece z w = Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] Σ[ path ∈ UniformComplexPath a b ]
  (pathStart path ≡ z) × (pathFinish path ≡ w)

piecePath : ∀ {z w} (piece : ComplexPathPiece z w) → UniformComplexPath (fst piece) (fst (snd piece))
piecePath piece = fst (snd (snd piece))

pieceStart : ∀ {z w} (piece : ComplexPathPiece z w) → pathStart (piecePath piece) ≡ z
pieceStart piece = fst (snd (snd (snd piece)))

pieceFinish : ∀ {z w} (piece : ComplexPathPiece z w) → pathFinish (piecePath piece) ≡ w
pieceFinish piece = snd (snd (snd (snd piece)))

complexPathGraph : Graph ℓ-zero ℓ-zero
complexPathGraph .Node = ℂ
complexPathGraph .Edge = ComplexPathPiece

PiecewiseComplexPath : ℂ → ℂ → Type₀
PiecewiseComplexPath = GraphPath.Path complexPathGraph

open GraphPath public using () renaming (pnil to emptyPiecewisePath; pcons to prependComplexPiece)

singleComplexPath : ∀ {a b} (path : UniformComplexPath a b) → PiecewiseComplexPath (pathStart path) (pathFinish path)
singleComplexPath {a} {b} path = prependComplexPiece (a , b , path , refl , refl) emptyPiecewisePath

concatenateComplexPaths : ∀ {x y z} → PiecewiseComplexPath x y → PiecewiseComplexPath y z → PiecewiseComplexPath x z
concatenateComplexPaths = GraphPath.ccat

concatenateComplexPathsAssoc : ∀ {w x y z} (p : PiecewiseComplexPath w x)
  (q : PiecewiseComplexPath x y) (r : PiecewiseComplexPath y z) →
  concatenateComplexPaths (concatenateComplexPaths p q) r ≡ concatenateComplexPaths p (concatenateComplexPaths q r)
concatenateComplexPathsAssoc = GraphPath.++assoc

concatenateComplexPathsLeftUnit : ∀ {z w} (chain : PiecewiseComplexPath z w) → concatenateComplexPaths emptyPiecewisePath chain ≡ chain
concatenateComplexPathsLeftUnit = GraphPath.pnil++

concatenateComplexPathsRightUnit : ∀ {z w} (chain : PiecewiseComplexPath z w) → concatenateComplexPaths chain emptyPiecewisePath ≡ chain
concatenateComplexPathsRightUnit = GraphPath.++pnil

AllComplexPieces : (∀ {a b} → UniformComplexPath a b → Type₀) → ∀ {z w} → PiecewiseComplexPath z w → Type₀
AllComplexPieces P emptyPiecewisePath = Unit
AllComplexPieces P (prependComplexPiece piece rest) = P (piecePath piece) × AllComplexPieces P rest

allComplexPieces : ∀ (P : ∀ {a b} → UniformComplexPath a b → Type₀) →
  (∀ {a b} (path : UniformComplexPath a b) → P path) → ∀ {z w} (chain : PiecewiseComplexPath z w) → AllComplexPieces P chain
allComplexPieces P proof emptyPiecewisePath = tt
allComplexPieces P proof (prependComplexPiece piece rest) = proof (piecePath piece) , allComplexPieces P proof rest


mapAllComplexPieces : ∀ (P Q : ∀ {a b} → UniformComplexPath a b → Type₀) →
  (∀ {a b} (path : UniformComplexPath a b) → P path → Q path) →
  ∀ {z w} (chain : PiecewiseComplexPath z w) → AllComplexPieces P chain → AllComplexPieces Q chain
mapAllComplexPieces P Q transform emptyPiecewisePath proof = tt
mapAllComplexPieces P Q transform (prependComplexPiece piece rest) (first , remaining) =
  transform (piecePath piece) first , mapAllComplexPieces P Q transform rest remaining

-- Integrability consists of actual Riemann integrals for the finitely many
-- pieces. Their sum defines the contour integral; endpoint formulas are
-- subsequently proved. No global glued velocity or choice principle is used.
IsPiecewiseComplexLineIntegrable : (ℂ → ℂ) → ∀ {z w} → PiecewiseComplexPath z w → Type₀
IsPiecewiseComplexLineIntegrable f = AllComplexPieces (IsComplexLineIntegrable f)

piecewiseComplexLineIntegral : ∀ f {z w} (chain : PiecewiseComplexPath z w) → IsPiecewiseComplexLineIntegrable f chain → ℂ
piecewiseComplexLineIntegral f emptyPiecewisePath proof = 0ℂ
piecewiseComplexLineIntegral f (prependComplexPiece piece rest) (first , remaining) =
  complexLineIntegral f (piecePath piece) first +ℂ piecewiseComplexLineIntegral f rest remaining

isPropIsPiecewiseComplexLineIntegrable : ∀ f {z w} (chain : PiecewiseComplexPath z w) → isProp (IsPiecewiseComplexLineIntegrable f chain)
isPropIsPiecewiseComplexLineIntegrable f emptyPiecewisePath = isPropUnit
isPropIsPiecewiseComplexLineIntegrable f (prependComplexPiece piece rest) =
  isProp× (isPropIsComplexLineIntegrable f (piecePath piece)) (isPropIsPiecewiseComplexLineIntegrable f rest)

HasPiecewiseComplexLineIntegral : (ℂ → ℂ) → ∀ {z w} → PiecewiseComplexPath z w → ℂ → Type₀
HasPiecewiseComplexLineIntegral f chain value =
  Σ[ integrable ∈ IsPiecewiseComplexLineIntegrable f chain ] piecewiseComplexLineIntegral f chain integrable ≡ value

isPropHasPiecewiseComplexLineIntegral : ∀ f {z w} (chain : PiecewiseComplexPath z w) value → isProp (HasPiecewiseComplexLineIntegral f chain value)
isPropHasPiecewiseComplexLineIntegral f chain value = isPropΣ (isPropIsPiecewiseComplexLineIntegrable f chain)
  (λ integrable → isSetℂ (piecewiseComplexLineIntegral f chain integrable) value)

piecewiseComplexLineIntegralUnique : ∀ f {z w} (chain : PiecewiseComplexPath z w) value other →
  HasPiecewiseComplexLineIntegral f chain value → HasPiecewiseComplexLineIntegral f chain other → value ≡ other
piecewiseComplexLineIntegralUnique f chain value other first second = sym (snd first)
  ∙ cong (piecewiseComplexLineIntegral f chain) (isPropIsPiecewiseComplexLineIntegrable f chain (fst first) (fst second)) ∙ snd second
