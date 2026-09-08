# A proof strategy for real and synthetic sphere homotopy groups

Proposal, 2026-09-07. This document adds no Agda implementation. The
unproved lemmas below are work to do, not assumptions added to the library.

Implementation updates are recorded in [PROGRESS.md](PROGRESS.md). The
first checkpoint proves uniform continuity of bounded normalization by
composition of existing scalar results, so the sharp Euclidean Lipschitz
estimate below is no longer a prerequisite for that continuity step.
The general comparison and finite regularization remain unproved.

**Current implementation gate:**
[SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md) revises the direction under
the user's requirement of inherent scaling. Do not add dimension-specific
realization stages. First supply a constructive general recursion and its
coherent universal property. The candidate to certify uses the cubical
classifying space of the category of real singular cubes; its internal
realization remains an explicit feasibility obstacle.
[UNIFORM_CONSTRUCTIONS.md](UNIFORM_CONSTRUCTIONS.md) records the
subsequent uniform shape proofs and the raw-augmentation-fiber alternative;
neither candidate yet supplies the missing internal realization theorem.

The latest checked analytic step is
[MetricCloseness.agda](../../Spheres/MetricCloseness.agda): for each sphere,
one merely existing positive radius in its maximum premetric guarantees
the squared-distance condition used by the nearby-map homotopies.

[CUBICAL_AUDIT.md](CUBICAL_AUDIT.md) records the subsequent read-only
survey: a degeneracy coherence checkpoint for realization, existing
connectivity tools for a dimension cutoff, constructive finite meshes,
and a simpler proposed cap contraction using stereographic coordinates.

[REALIZATION_EXPERIMENTS.md](REALIZATION_EXPERIMENTS.md) records the next
investigation. Finite cubical latching attachments gave the checked
degree-two prototype. The actual UC-square degeneracy union embeds in
all squares, its coherent attaching map is constructed, and the resulting
stage inclusion is an equivalence for propositional carriers. Coherent
attaching maps in higher dimensions remain unproved.

**Current shape convention:** the user requested a cubical development.
The working singular cells are real cubes, and the preferred sphere
comparison now uses two overlapping caps and a synthetic suspension
pushout. The original many-hemisphere nerve argument is retained below
as an earlier alternative, not as a requirement to introduce simplexes.

## Target and assessment

The target is, for every `n m : ℕ`,

```agda
GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m))
```

Write `k = n + 1` for the homotopy degree. We are comparing **real
homotopy of the real coordinate sphere** with **synthetic homotopy of the
synthetic HIT sphere**. The sphere dimension `m` and homotopy degree `k`
are independent. A proof just of the diagonal groups, or just of their
stable range, would not establish this target.

There is a plausible route with concrete geometric ingredients:

```text
iterated real-loop classes in the real m-sphere
    ≅ boundary-fixed, jointly UC real k-cube classes
    ≅ synthetic π_k of a real cubical singular realization
    ≅ synthetic π_k of an iterated suspension, using two-cap descent
    ≅ synthetic π_k of the library's HIT m-sphere.
```

Here a **real cubical singular realization** would be a new synthetic type
whose cells encode uniformly continuous maps from real cubes, with their
face, degeneracy, and connection structure. It must retain real homotopies
in every dimension. It is distinct from using the real sphere itself as
the target of synthetic homotopy groups.

The preferred geometric idea is that two thick caps contract, while their
overlap retracts onto a real sphere of one lower dimension. If cubical
cover descent is proved, their synthetic realizations form a suspension
pushout. This gives a specific way to reach the synthetic sphere by
induction. Also, the first arrow may only need
regularization of homotopy classes, avoiding an exponential-law theorem
for every element of every iterated loop space.

I regard this as a viable mathematical strategy, but **not yet a complete
constructive proof**. The largest new formalization is the internal
singular-realization and cover-comparison theorem. Defining another
comparison interface with this theorem as a parameter would leave the
main work undone.

## 1. Reach real cubes by finite regularization

The checked [currying theorem](Currying.agda) and its
[boundary-fixed version](CubeCurrying.agda) give inverse maps when a
common slice modulus is supplied. They do not show that this extra
condition holds for every existing iterated real loop.

For the sphere comparison, a weaker statement could suffice:

> Every iterated real-loop class has a jointly uniformly continuous cube
> representative, and real homotopies between such representatives can
> also be represented jointly uniformly continuously, with the prescribed
> endpoints and boundary.

Both parts are necessary: representatives give surjectivity of the cube
model, while the relative homotopy statement gives injectivity.

### Quantitative tool: normalization of nearby vectors

Work temporarily with the Euclidean norm in `R^d`, where `d = m + 1`.
For `N(v) = v / ‖v‖₂`, prove the estimate

```text
‖u‖₂, ‖v‖₂ ≥ c > 0  ⇒  ‖N(u) − N(v)‖₂ ≤ (2/c) ‖u − v‖₂.
```

If unit vectors `v_i` are all within `ρ < 1` of one unit vector `p`,
every convex combination `v = Σ λ_i v_i` satisfies `‖v‖₂ ≥ 1 − ρ`.
Consequently, sufficiently close sphere-valued maps have an explicit
homotopy

```text
H(t,u) = N((1 − t) f(u) + t g(u)).
```

This fixes any part of the domain where `f = g`, including a constant
based boundary. All estimates must be translated to the existing
maximum-coordinate premetric. The bound
`‖z‖∞ ≤ ‖z‖₂ ≤ d ‖z‖∞` permits rational tolerances depending only on
dimension; for example, a maximum-norm error below `1/(8d)` is small enough
for a uniform positive denominator bound.

The same pointwise formulas should induce uniformly continuous operations
on the rounded uniform mapping spaces. Prove this explicitly, then lift
the estimates through each level of `realΩ^`. This is what lets the
homotopy formula operate on a nested loop before it has a joint modulus.

### Representative regularization lemma

The proposed proof is induction on the number of real parameters:

1. Use the outer loop's modulus at one fixed tolerance to choose a finite
   rational mesh. Adjacent sampled slices are uniformly close.
2. Recursively approximate the finitely many sampled lower-dimensional
   loops by jointly UC cubes, with a controlled uniform error. Keep the
   constant boundary slices constant.
3. Interpolate the approximations in ambient coordinate space using
   finite rational tent functions, and normalize. Only nearby samples
   have nonzero weights, so the positive denominator estimate applies.
4. The result has a joint modulus obtained from finitely many estimates.
   The nearby-map formula gives a real homotopy from the original nested
   loop to its approximation, preserving the based boundary.

Tent functions avoid making a decidable choice of the mesh cell containing
an arbitrary real number. Refining the finitely many meshes gives a
common finite grid when needed. The lemma should allow a requested
positive error bound, since the induction uses quantitative control of
the lower-dimensional approximations.

The [cubical audit](CUBICAL_AUDIT.md#finite-meshes-without-choosing-a-real-cell-index)
gives explicit candidate weights by differences of clipped affine ramps;
their sum telescopes to one. It also identifies a smaller first square
construction by concatenating nearby-path strips. Both approaches still
need the lift to rounded uniform mapping spaces and the appropriate
relative approximation proof.

### Relative homotopy regularization lemma

Suppose jointly UC based cubes `q₀` and `q₁`, after currying, are related by
the real homotopy used in the existing loop quotient. Apply regularization
to that homotopy with one more parameter, keeping the spatial boundary
constant. Its new endpoint cubes may only approximate `q₀` and `q₁`.

Insert short time collars using the nearby-map formula to join `q₀` to
the first new endpoint and the last new endpoint to `q₁`. Each endpoint
map is already jointly UC. Finite gluing and reparametrization should then
give a jointly UC cube homotopy with **exactly** the required time faces
and constant spatial boundary. No approximation of the prescribed
endpoints remains in the final statement.

Finally prove compatibility with concatenation in the loop coordinate.
A bijection of classes alone does not give the requested `GroupIso`.
Cubical interchange would also give the expected commutativity for
`k ≥ 2`, but it is not a substitute for the comparison theorem.

### Handling truncated moduli

The existing `UC` predicate gives a propositionally truncated modulus.
The proof above uses a finite number of witnesses at a fixed tolerance,
and can first produce a **merely existing** approximation and homotopy.
It does not require selecting a sequence of moduli for infinitely many
slices or tolerances.

To define an actual map into a homotopy group, prove that all permitted
finite choices give the same class. The library's
[`rec→Set`](../../../PropositionalTruncation/Properties.agda) then eliminates
the truncation into that set using the constancy proof. Merely having a
set-valued target, without independence of choices, would not suffice.

This proposed regularization is specific to sphere targets, using their
ambient linear structure and normalization. It does not claim a cube
comparison for every premetric space.

## 2. Where the ball–cube correspondence fits

For `k ≥ 1`, the geometric identification suggested in the discussion is

```text
(I^k, ∂I^k) ≅ (B^k, S_real^(k−1)),
I^k / ∂I^k ≅ B^k / S_real^(k−1) ≅ S_real^k.
```

The radial map from the Euclidean ball to the centered cube is, away from
zero,

```text
v ↦ (‖v‖₂ / ‖v‖∞) v,
```

with inverse obtained by exchanging the norms. Both send zero to zero;
an affine change of coordinates gives `[0,1]^k`.

A formal proof needs uniformly continuous extensions at zero, boundary
preservation in both directions, and compatibility with maps and real
homotopies. For the collapsed-boundary presentation, also specify and
prove the relevant quotient universal property for UC maps. A bare type
bijection is insufficient. The existing
[`sphereBallBoundaryIso`](../../Spheres/Ball.agda) is an earlier geometric
ingredient, not this complete pair or quotient comparison.

There is a constructive detail to audit: [OnBoundary](Cubes.agda) is a
truncated disjunction of coordinate endpoint equalities. Relating that
predicate to a maximum-norm boundary requires proof; an exact maximizing
coordinate or a decidable zero test cannot simply be assumed. Finite
maxima, strict comparisons with margins, and a selected maximizing index
are different pieces of data.

This correspondence is useful for changing the **real domain model** and
for interpreting cube classes as real sphere-map classes. The recommended
proof can proceed directly with cubes and a cover of the target sphere,
so the ball quotient is not a prerequisite for its real-to-synthetic
step.

## 3. Build the missing real singular model

Use a cubical singular diagram

```text
Singᵤ□(X)_r = UC(CubeSpace r, X),
Rᵤ(X) = its synthetic HIT realization.
```

Faces act by inserting real endpoints, degeneracies by deleting a
coordinate, and connections by suitable real `min`/`max` maps. Coordinate
reversals and permutations can be included where needed. These maps and
their identities need to be implemented for the existing `CubeSpace`.
The realization must account for degeneracies and the chosen connection
structure coherently. Attaching cells with face information alone cannot
silently be substituted for the intended singular realization.

The first acceptance test is `Rᵤ(Unit)` being contractible. Attaching all
singular cubes with faces alone leaves the constant interval as an
unkilled loop even in this case. Using only nondegenerate cubes would
instead require a decomposition and coverage theorem not supplied by
the current data; one cannot assume decidable degeneracy.
Resolve this construction and coherence issue before building a large
skeleton; see the [audit](CUBICAL_AUDIT.md#realization-must-handle-degenerate-cubes).

The follow-up prototypes resolve part of this checkpoint. The corrected
reflexive graph has a contractible terminal instance, and its extra-loop
control example is the synthetic circle. For actual UC squares,

```text
L₂ = Pushout(C₁ ←constant— C₀ —constant→ C₁)
```

has a checked embedding into `C₂`. The implemented degree-two step attaches interiors
relative to both this latching object and the ordinary synthetic boundary,
using a pushout-product. The checked cancellation theorem shows that when
the latching map is an equivalence, this step preserves the previous
stage without truncation. The actual degree-two attaching map and the
relative overlap compatibility of its two degenerate fillings now check.
The scalability audit withdraws the proposal to test successive degrees.
Any use of this construction as a backend must first derive its coherent
attaching maps from a single general construction theorem.
See [the experiment report](REALIZATION_EXPERIMENTS.md).

The proposed theorem for a pointed target is

```text
jointly UC based k-cubes modulo jointly UC relative homotopy
    ≅ synthetic π_k(Rᵤ(X)),
```

as groups. It must describe representatives in both directions, not just
send each real cube to a synthetic cell. In particular, **every synthetic
class in the realization** must admit the required finite singular
presentation, and equality of such classes must give the corresponding
relative real homotopy.

The classical singular-realization comparison provides a model for this
argument: May proves that the realization of the singular complex maps
to a topological space by a weak equivalence, with approximation supplying
the more delicate direction. This is motivation for an internal proof,
not an already available Agda theorem about our UC definitions.
See [May, *A Concise Course in Algebraic Topology*, Chapter 16, §§2–4](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf).
That reference uses simplicial methods; it supplies background rather
than a decision to triangulate our cubical construction.

Concrete new infrastructure would include:

- Finite rectangular subdivision and UC gluing of real cubes, including
  relative faces. A cube times a homotopy interval is another cube.
- A precise synthetic realization with coherent attaching maps. Real
  homotopies must induce synthetic homotopies, for example by a prism
  construction.
- An internal comparison between combinatorial singular homotopy and
  synthetic homotopy of that realization. A Kan-complex approach would
  require open-box extension proofs using geometric retractions and
  finite cubical gluing. Filling an open box does not mean filling an
  arbitrary entire sphere boundary.
- A relative finite-presentation or approximation theorem, including its
  compatibility with concatenation.

The survey found no existing real cubical singular-realization
package providing these statements. [Pushouts](../../../Pushout/Base.agda)
and [sequential colimits](../../../SequentialColimit/Base.agda) are
available building blocks. The current [CW definition](../../../../CW/Base.agda)
has `Fin (f n)` cells in each degree; the full family of singular cells
does not satisfy that restriction. Its skeleton construction cannot just
be reused unchanged. Also, the existing
[CW approximation theorem](../../../../CW/Approximation.agda) concerns
synthetic cellular approximation, and does not itself supply the real
approximation theorem above.

For a fixed `k`, one can investigate a construction through dimension
`k+1`, provided one proves the skeletal connectivity result justifying
that cutoff. Finite dimension does not make the collection of singular
cells finite. A construction with only points, paths, and a set quotient
would discard precisely the higher information the goal asks to compare.

The audit identifies a possible local proof of the dimension cutoff
using `isConnected-CW↪`, `isConnectedIncl∞`, and
`connectedFun→πEquiv`, once a valid singular skeleton exists. This avoids
treating dimension cutoff as the same problem as finite support of
representatives. Neither that cutoff nor ordinary CW approximation
establishes the latter; see
[the connectivity findings](CUBICAL_AUDIT.md#a-dimension-cutoff-is-easier-than-finite-support).

## 4. Preferred cubical route: two caps and suspension

For `m ≥ 1`, write a sphere point as `x = (h,y)` and use the cover

```text
U+ = { x : S_real^m | -1/2 < h },
U− = { x : S_real^m | h < 1/2 },
W  = U+ ∩ U− = { x | -1/2 < h < 1/2 }.
```

The overlap has a fixed positive width. Rational approximation with a
strict comparison gap should let a sufficiently fine cubical subdivision
of any UC representative have each small cube assigned to one cap. The
same must hold relatively for homotopies and prescribed faces; assigning
small cubes alone is not the descent theorem.

**Cap contractions.** The current recommendation is stereographic
contraction. On `U+`, put `p = y/(1+h)`. The sphere equation gives

```text
norm²(p) = (1-h)/(1+h) < 3,
p ↦ (1-t)p,
p ↦ ((1-norm²(p))/(1+norm²(p)), 2p/(1+norm²(p))).
```

The last map is the proposed inverse coordinate map. Scaling preserves
`norm²(p) < 3`, hence preserves the cap. The bounds `1+h > 1/2` and
`1+norm²(p) ≥ 1` permit use of existing bounded reciprocal and scalar
product UC lemmas. Prove the inverse laws, joint UC, and exact identity,
pole, and fixed-pole laws. Reflection gives the negative cap.

These formulas are unimplemented. They replace the earlier normalized
blend proposal, which had a candidate squared-norm lower bound `1/4`
but still needed a separate cap-preservation inequality with negative
dot product. The checked nonnegative-dot interpolation remains the tool
for nearby-map regularization. See
[the stereographic audit](CUBICAL_AUDIT.md#stereographic-cap-contractions).

**Overlap retraction.** In `W`, `norm²(y) = 1-h² > 3/4`. The proposed
uniform isomorphism is

```text
W ↔ (-1/2,1/2) × S_real^(m−1),
(h,y) ↦ (h, normalize(y)),
(h,w) ↦ (h, √(1-h²) w).
```

Its equations and both UC directions need proof. Under this description,
contract the height by `h ↦ (1-t)h`, leaving `w` fixed. This stays in the
overlap and fixes the equatorial sphere exactly. It uses interval
products, with no conversion to simplexes.

**The missing cubical descent theorem.** Show that the inclusions induce
an equivalence, or an appropriately connected comparison sufficient in
each required degree,

```text
Pushout(Rᵤ(W) → Rᵤ(U+), Rᵤ(W) → Rᵤ(U−)) → Rᵤ(S_real^m).
```

This must be built from relative cubical subdivision/gluing and the
internal realization comparison of section 3. Real UC contractions must
induce synthetic contractions of the corresponding realizations; that
homotopy-invariance or prism theorem is also a required proof.

If these steps succeed, the two contractible sides give
`Rᵤ(S_real^m) ≃ Susp(Rᵤ(S_real^(m−1)))`. The library already provides
[`pushoutEquiv`](../../../Pushout/Properties.agda),
[`PushoutSuspIsoSusp`](../../../Pushout/Base.agda), and the sphere
suspension equivalences in [Sn/Properties](../../../Sn/Properties.agda).
Track the real basepoint `e+` to the suspension's north pole. Prove the
base case `Rᵤ(S_real^0) ≃ Bool` by the cubical singular construction; a
carrier bijection alone would not prove that realization statement.

This is induction on the **sphere dimension**, not a claim that
`π_k(S^m)` is always isomorphic to `π_(k-1)(S^(m-1))`. Homotopy groups
are taken only after identifying the entire realizations, or after
establishing comparison maps with the needed connectivity. No stability
assumption is being made.

The two-cap route is a new proposal prompted by the preference for
cubical shapes. Its cover, cap-preservation, overlap, and descent proofs
are not yet implemented. The advantage is that a binary cover can lead
directly to the library's suspension HIT, without constructing a
simplicial nerve or triangulating real cubes.

## 4A. Earlier alternative: the many-hemisphere nerve

The following records the original comparison idea. The current plan
uses section 4 instead; this alternative is not a requirement to add
simplicial shapes to the development.

Let `d = m + 1`, and index `2d` open hemispheres by a coordinate and a sign:

```text
U_(i,σ) = { x : S_real^m | σ x_i > 0 },  σ ∈ {−1,+1}.
```

The basepoint `(1,0,…,0)` belongs to `U_(0,+)` and to no other member.

### Explicit contractions of all nonempty intersections

For a nonempty set `F` of labels containing no opposite signs for the
same coordinate, put

```text
a_F = (Σ_(i,σ)∈F σ e_i) / √|F|,
H_F(t,x) = N((1 − t)x + t a_F).
```

The anchor `a_F` lies in the intersection `U_F`. For `x : U_F`,
`x · a_F > 0`, hence

```text
‖(1 − t)x + t a_F‖₂²
  = (1 − t)² + t² + 2t(1 − t)(x · a_F)
  ≥ (1 − t)² + t²
  ≥ 1/2.
```

Every specified signed coordinate stays positive. Thus this formula
contracts `U_F` to `a_F`, fixes that anchor, and has a uniform denominator
bound even though the intersection is open. The normalization estimates
give joint uniform continuity. Intersections with opposite labels are
empty. These are direct analytic lemmas with dimension-dependent bounds;
they do not need a general compactness theorem for arbitrary open covers.

### Obtain finite subdivisions with a strict margin

Choose `c = 1/(8d)`. At each sphere point one can seek a signed coordinate
strictly greater than `2c`, using rational approximations and finite
decidable comparisons. For example, approximate each coordinate within
`c`. If every rational approximation had absolute value at most `3c`,
then every coordinate would have absolute value below `4c`, contradicting
`Σ x_i² = 1`, since `d(4c)² = 1/(4d) < 1`.

This produces a label with room to spare, without selecting an exact
largest real coordinate. A modulus for a real cube map then gives a
finite subdivision fine enough that the image of each vertex star stays
in its selected hemisphere. Intersecting stars give intersecting
hemispheres, hence a simplex of the nerve. On the based boundary choose
the label `(0,+)`; its strict margin permits boundary stars as well.

The essential new **relative subdivision and carrier lemma** must work
for maps and homotopies, extend prescribed boundary data, and show that
refinements and different permitted labels give the same homotopy class.
The explicit intersection contractions provide the extension data, but
their compatibility across faces must still be constructed.

### Cover comparison, then identify the nerve

Let `N_m` be the abstract finite complex with these labels and a simplex
for every consistent set of labels. Prove that the cover construction
induces group isomorphisms

```text
synthetic π_k(Rᵤ(S_real^m)) ≅ synthetic π_k(|N_m|_synt).
```

A possible organization is a Čech diagram of intersection singular
realizations: prove descent from that diagram to `Rᵤ(S_real^m)`, then use
the contractions to replace its nonempty intersections by points. An
equivalent degreewise proof can use the relative carrier lemma directly.
Either version needs the synthetic coherence and approximation results
from the preceding section. Separate contractions, without a descent
argument, do not prove the displayed isomorphism.

Classically, the homotopy colimit of the Čech diagram of an open cover
recovers its homotopy type; this suggests the organization of this step.
See [Dugger–Isaksen, *Hypercovers in topology*, author overview](https://pages.uoregon.edu/ddugger/hyper.html).
The finite UC and internal synthetic version here remains to be proved.

The nerve has a particularly simple combinatorial description:

```text
N_m = S⁰ * S⁰ * … * S⁰     (d copies),
```

the boundary complex of the `d`-dimensional cross-polytope. Prove that its
synthetic realization carries this finite join decomposition. Then the
existing [`Susp-iso-joinBool`](../../../Susp/Properties.agda) and
[`IsoSucSphereSusp`](../../../Sn/Properties.agda) identify it with `S₊ m`.
Track the vertex `(0,+)` through these equivalences to obtain a pointed
comparison. For `m = 0`, the nerve is just the two-point sphere.

A direct pointed equivalence `Rᵤ(S_real^m) ≃∙ S₊∙ m` would be a strong
outcome. The requested theorem only needs the displayed group
isomorphisms. Do not infer a type equivalence solely from isomorphisms of
all homotopy groups without an applicable, proved Whitehead hypothesis.

## 5. Connect the proof to the existing interface

The checked [Comparison.FromRepresentatives](Comparison.agda) already
packages the last quotient step. The proposed work would supply its five
parameters as follows:

| Required parameter | Intended construction or proof |
| --- | --- |
| `realize` | Regularize the iterated loop, pass to its cubical singular class, and use the two-cap suspension comparison to reach the synthetic sphere. Prove independence of the finite choices. |
| `respects` | Regularize a given real homotopy with its prescribed faces, and use the relative singular and cover constructions. |
| `preserves` | Match concatenation in the chosen cube coordinate with synthetic loop multiplication, including orientation conventions. |
| `complete` | Use the reverse singular/cover comparison to obtain a real cube homotopy from equality of synthetic classes; curry it and compose with the regularization homotopies. |
| `represents` | Give finite cubical singular representatives for every synthetic class through the suspension comparison, realize them geometrically, and curry the resulting cube. Mere existence is sufficient. |

If the construction produces synthetic sphere-map classes, finish with
[`π'Gr≅πGr`](../../../../Homotopy/Group/Base.agda). If it already produces
synthetic loop classes, that additional conversion is unnecessary.

The current [isometry invariance](Invariance.agda) does not yet give
functoriality for arbitrary pointed uniformly continuous equivalences.
Where the geometric construction needs that stronger statement, prove
it by postcomposition on maps and homotopies, including preservation of
the group operation.

## 6. Suggested order and decision points

The degree-two latching attaching map and its overlap coherence are now
checked, together with cancellation of the actual attachment for
propositional carriers. These do not certify scaling. Follow
[SCALABILITY_AUDIT.md](SCALABILITY_AUDIT.md): establish the general
normalized-cocone boundary construction, successor invariant, and
universal property before implementing more stages. The all-dimensional
realization and its terminal contraction remain open. The mathematical
analytic regularization work below is independent of that gate.

1. **Quantitative normalization and finite regularization.** First test
   the induction with a real square versus a double loop, and a real
   three-parameter homotopy with its time faces fixed. This tests whether
   the existing rounded uniform metrics support the proposed analytic
   bridge without changing the definitions of `realπGr`.
2. **The two-cap geometry.** Prove the contractions with cap preservation,
   the overlap retraction, and the strict-margin cubical subdivision
   lemma. These supply concrete inputs for a suspension pushout proof.
3. **Prototype the internal singular and cover comparison in the
   dimensions needed for `π₂(S²)`.** Include both directions and relative
   homotopies, not just an encoding of representatives. This is the main
   feasibility checkpoint before building general realization machinery.
4. **Generalize in `k` and `m`, and discharge the five interface fields.**
   Keep the analytic estimates, finite combinatorics, and quotient/group
   proofs in small modules. No postulates or extra choice principles
   should stand in for a missing construction.
5. **Check compatibility with known results.** In degree one on the
   circle, compare with the checked
   [winding-number comparison](CircleComparison.agda), fixing orientation
   so the chosen positive generator maps to `+1`. Next transport
   [`πₙSⁿ≅ℤ`](../../../../Homotopy/Group/PinSn.agda), including `π₂(S²)`.
   The existing `π₃(S²)` and `π₄(S³)` calculations become further tests
   once the general comparison is available.

One can try to avoid a full singular realization by working directly
with finite cubical representatives and the two-cap pushout. That could
reduce infrastructure for this particular target, but it still requires
an internal theorem relating these finite representatives to **all**
synthetic homotopy classes of the pushout. It does not remove the main
feasibility checkpoint.

This route would relate all the requested unstable homotopy groups
without first computing them individually. The finite regularization and
coordinate-cover calculations make the proposal concrete; the internal
realization and relative comparison theorems are the substantial open
proof obligations.
