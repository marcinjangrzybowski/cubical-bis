# Require an all-dimensional construction before further realization work

Revised direction, 2026-09-07, following the user's explicit requirement.

## Decision

**Do not extend the current square construction one dimension at a time.**
The checked degree-two attachment is retained as a local theorem and a
future regression example. It does not establish that the proposed tower
can be constructed coherently in arbitrary dimension.

The next work is a mathematical construction and proof audit for a
dimension-independent cubical realization. Implementation resumes only
after that audit supplies an actual general recursion and its invariant,
including how every higher compatibility is generated. A record whose
fields simply request the missing attaching maps or coherences does not
satisfy this requirement.

At present **no internal all-dimensional realization has passed that
gate**. The classifying-space architecture below is one candidate
to certify. Its indexing, normalization strategy, and prism formulas are
uniform in dimension; its constructive internal realization theorem still
needs proof. External classical existence results do not close that gap.

[UNIFORM_CONSTRUCTIONS.md](UNIFORM_CONSTRUCTIONS.md) records the next
investigation: checked all-dimensional boundary/cofiber sphere
equivalences, restriction-compatible mapping and relative extension
equivalences with the existing cube types, a checked fiber-correction
lemma, and an alternative
normalization by the fiber of a raw realization's augmentation. The two
candidate realizations still require an internal coherent recursion.

## What the square result establishes, and what it does not

The five new modules recorded in [PROGRESS.md](PROGRESS.md) checked before
this change of direction. In particular, `attach₂` has no remaining
coherence parameters, and its actual stage inclusion is an equivalence
when the real carrier is a proposition.

There are two different coherence problems:

1. **Coherence of real input data.** A real frame contains vertices and
   UC paths. It is a set, so different proofs of its face-normalization
   equations agree. Similar set-valued input arguments can be organized
   in arbitrary dimension.
2. **Coherence of synthetic fillings.** The realization is an arbitrary
   higher type. Equality of two chosen fillings is additional data;
   equality between their comparison paths is further data. Setness of
   the real frame does not produce this hierarchy.

The square proof solves its particular synthetic overlap by path
induction on a contracted loop. That is valid and useful. It is not a
proof that arbitrary higher overlap diagrams admit compatible fillers.
Likewise, `JCube` in
[Cubes/Base.agda](../../../../Foundations/Cubes/Base.agda) permits
induction on complete cubes with varying boundaries. It does not make
fixed-boundary filler types contractible.

The finite-union argument for deleted-coordinate degeneracies addresses
the first problem. The pushout-product cancellation theorem assumes an
attaching map and addresses neither its existence nor its higher
naturality. A succession of degree-three, degree-four, and degree-five
examples would leave the general problem unresolved.

## Candidate to certify: a cubical classifying realization

Keep the real singular input

```text
K(X)_n = UC(I_real^n, X).
E(X) = category of elements of K(X).
R(X) = B_cubical(E(X)).
```

An object of `E(X)` is `(n, σ)`. An arrow `(m, τ) → (n, σ)` consists of
a combinatorial cube map `α : m → n` and the equation `σ ∘ α = τ`.
There is no synthetic evaluation of a real sphere's set carrier here:
the proposed higher type is the classifying realization of this category.

For any such category `E`, use cubical diagrams

```text
N_r(E) = Fun([1]^r, E).
```

Here `[1]^r` is the finite Boolean cube as an ordered category. Faces,
ordinary degeneracies, and connections act by precomposition. The two
dimensions have different roles: `n` labels a real singular cube, while
`r` labels a finite diagram of such cubes. Both range over all natural
numbers from the start. A cutoff in nerve degree does not bound the
dimensions of the real cubes at its vertices. The later finite
representative theorem must address that conversion explicitly.

Category composition supplies the commutative diagrams in every `r`.
It is still necessary to prove that their realization interprets those
diagrams with all required synthetic coherence. Merely defining `N_r`
does not supply a realization functor.

Antolini's paper develops a cubical classifying-space comparison and
distinguishes retaining connection cells from collapsing them. This is
external motivation rather than a certified internal construction.
[Antolini, *Geometric Realisations of Cubical Sets with Connections, and Classifying Spaces of Categories*](https://research.manchester.ac.uk/en/publications/geometric-realisations-of-cubical-sets-with-connections-and-class/).

The source audit found a relevant qualification: Kishimoto–Tong report
that the older argument for the equivalence of the two connection
conventions established fundamental groups and homology, which alone do
not prove a homotopy equivalence. Their 2026 preprint provides a replacement
proof in Proposition 2.14 and a category-of-elements comparison in Lemma
5.13. Those arguments use external homotopy-colimit/model-category tools.
We must audit the actual general proof and its constructive assumptions;
the older abstract is insufficient certification.
[Kishimoto–Tong, *Discrete homotopy groups of cubical sets*, Sections 2.3 and 5.2](https://arxiv.org/html/2606.28693v1#S2.SS3).

### Fix the cube category and product convention first

The proposed site is the ordered cube category generated by endpoint
insertions, coordinate deletions, and the connection
`γ(s,t) = max(s,t)`. Do not add coordinate permutations or diagonals
implicitly. The real interpretation must prove these maps UC and their
equations before treating `K(X)` as a functor.

This site has an established homotopy-theoretic role: Cisinski's Example
1.6 identifies the cube category with this connection as an elegant
strict test category. This is an external theorem, not a claim that our
internal UC realization or its comparison is already proved.
[Cisinski, *Univalent universes for elegant models of homotopy types*](https://www.math.univ-toulouse.fr/~dcisinsk/universe.pdf).

Use the **geometric tensor** of cubes: `m ⊗ n = m+n`. Do not identify a
Cartesian product of representable cubical presheaves with a larger
representable cube. Carranza–Kapulkin explain this distinction and work
with connections; their arguments also allow just the max connection.
[Carranza–Kapulkin, *Homotopy groups of cubical sets*, introduction](https://arxiv.org/pdf/2202.03511).

This site choice also changes latching data. Factoring through `max` is
not the same as being independent of a coordinate. Thus the existing
deleted-coordinate pushout is not a connection-inclusive latching object.

### Uniform normalization of ordinary nerve degeneracies

The following is a proposed constructive proof with explicit data, not
yet an Agda theorem.

A map `m → n` in the proposed cube category can be represented by an
ordered list of `n` outputs. Each output is `1` or the maximum of a finite
subset of the `m` inputs; the empty maximum is `0`. Nonempty supports
are disjoint and occur in increasing order across outputs. Substitution
and normalization of these expressions give a finite combinatorial
equality test. The normal-form presentation and its category laws need
proof; no equality test on UC maps is part of this procedure.

For `F : [1]^r → E(X)`, declare coordinate `i` inactive exactly when
every `i`-directed elementary edge projects to an identity cube map.
There are finitely many such edges. Equality of source and target cube
dimensions is included in the test.

The key implication has a concrete proof obligation. If an element arrow
projects to the identity, its equation `K(id)(σ) = τ`, together with the
functor identity law, gives equality of its two labels. Transport along
that equality identifies the arrow with an identity. The equality is
obtained from the arrow; it is not decided independently. The existing
`ElementHomPathP` and `ElementHom≡` in
[Elements.agda](../../../../Categories/Instances/Elements.agda) support
exactly this transport argument.

Delete all inactive coordinates by restricting them to zero, and keep
the remaining coordinates in increasing order. The proposed general
normalization theorem is

```text
F = core(F) ∘ projection_to_active_coordinates,
core(F) has no inactive coordinate,
this decomposition is unique in the ordered convention.
```

Prove this for arbitrary `r`, including compatibility with every face
restriction, repeated deletion, and postcomposition functor. The
canonical finite procedure avoids a choice of a minimal presentation of
an arbitrary UC function.

This normalizes **ordinary coordinate deletions only**. A diagram such
as `F(s,t)=p(max(s,t))` can have both directions active and still be a
connection cube. The initial classifying-space convention proposed here
retains these connection cubes as cells. Its comparison with a realization
that also collapses connections must be proved, not silently assumed.

There is also a uniform proposed factorization test if connection
normalization is needed later. For an inverse map
`q : [1]^r → [1]^k`, write each output as the maximum over a nonempty
ordered block of inputs; the blocks are disjoint. Define a monotone
section `s` by copying each output to its block and setting ignored inputs
to `1`. Then `q s = id` and `v ≤ s(q(v))`. Consequently,

```text
F factors through q
  iff every F(v → s(q(v))) is an identity.
```

On success take `core = F ∘ s`; the identity paths and naturality give
`F = core ∘ q`. This is a finite test for every `r` and `q`, using the
same element-arrow criterion. The section is a functor of the finite
indexing posets; it need not be a map in the chosen cube category, so
its repeated coordinates do not add diagonals to that site. Selecting a
unique normal form among all successful inverse maps still requires a
separate decomposition/uniqueness proof. This observation does not
change the initial convention or resolve the realization gate below.

### The central gate: generic realization and its universal property

Before adding more realization code, give a constructive proof of the
following package for the normalized nerve, uniformly in `r`:

- A recursively specified boundary and interior in every dimension.
- A finite-stage invariant recording the entire evaluation cocone,
  including compatibility with all face and normalization operations.
- One successor construction that produces the next attaching map
  **and preserves that invariant**, using only data already constructed.
- A sequential colimit and a mapping-out equivalence into arbitrary
  higher types, expressing the fully coherent cubical cocone property.
- Functoriality, including the action on natural transformations and
  compatibility of its prisms with normalization and faces.

The mapping-out target must be defined independently of the proposed
realization. Writing “coherent cocone” as an unspecified field, or defining
it to mean maps out of the result, would not prove the claimed universal
property. In particular, the recursively defined cocone type must itself
support an all-dimensional boundary computation; it cannot take that
computation as an unspecified argument. A construction that needs a newly chosen overlap filler at
each successor has not passed this gate.

This is a recognized foundational issue, not merely a missing convenient
lemma. Sato describes how a skeletal attaching map requires functoriality
of the lower realization, which recursively requires higher functoriality.
The construction discussed there is meta-parametric in the truncation
degree. This does not prove impossibility in Cubical Agda, but it rules
out citing a finite-stage recipe as an internal all-dimensional theorem.
[Sato, *Geometric realization of truncated semi-simplicial sets meta-constructed within HoTT*](https://hott-uf.github.io/2018/abstracts/HoTTUF18_paper_13.pdf).

Reedy theory gives a general skeletal presentation by latching
pushout-products in its categorical setting. The realization argument
uses an already defined weighted colimit and its functoriality. It is
therefore not a substitute for constructing an internal untruncated
realization with coherent elimination.
[Riehl–Verity, *The theory and practice of Reedy categories*, Proposition 6.3 and Observation 10.7](https://arxiv.org/pdf/1304.6871).

The available library pieces do not already supply this package:

| Existing construction | What remains missing for this use |
| --- | --- |
| [Graph colimit](../../../Colimit/Base.agda) | Identity and composition coherences of the indexing category. |
| [Presheaf coend](../../../../Categories/Presheaf/KanExtension.agda) | It uses a set quotient; the intended higher target is untruncated. |
| [CW skeleton](../../../../CW/Base.agda) | Attaching maps are inputs, and each degree has a finite cell index; singular coefficients need not be finite. |
| [Sequential colimit](../../../SequentialColimit/Base.agda) | It combines a constructed tower but does not construct its coherent stages. |

These modules may supply components. None justifies replacing the central
gate with a direct call to an existing realization function.

### Two dimension-independent consequences to derive from that package

These are mathematical proof sketches conditional on the generic
realization theorem, not implemented theorems.

**Terminal contraction.** For a terminal real space, `E(*)` identifies
with the cube category, whose terminal object is dimension zero.
The natural transformation `id ⇒ const(0)` extends each diagram
`[1]^r → E(*)` to a prism `[1]^(r+1) → E(*)`. Every inactive coordinate
stays inactive. A generic prism theorem therefore contracts the entire
realization at once. This is the required all-dimensional terminal test;
repeated cancellation tests in individual degrees are weaker.

**Real-homotopy invariance.** For a jointly UC map
`H : I_real × X → Y`, define

```text
P_H(n, σ) = (n+1, (t,u) ↦ H(t, σ(u))),
P_H(α) = id_I ⊗ α.
```

The two endpoint insertions give a natural-transformation span

```text
(H at 0)_* ⇒ P_H ⇐ (H at 1)_*.
```

Applying a classifying functor that sends natural transformations to
homotopies gives the comparison homotopy in all dimensions. No arbitrary
Cartesian-product preservation theorem is needed for this argument.
Pointed and relative versions must additionally track the constant
subdiagram and prescribed faces; the unbased formula alone is not a
based homotopy-group comparison.

## Acceptance order

1. **Certify the generic construction on paper.** Fix the site and
   realization convention, prove the finite normalization criterion,
   and give the full constructive successor/universal-property argument.
   If that argument cannot be supplied, report the precise obstruction
   and leave realization implementation paused.
2. **Implement that general theorem.** Definitions must take arbitrary
   natural-number dimensions. Derive the existing square case as a
   specialization or compare it afterwards; do not build the theorem by
   accumulating separately chosen low-dimensional coherences.
3. **Prove uniform structural consequences.** Functoriality, terminal
   contraction, relative prisms, and standard cubical boundary/cofiber
   comparisons must follow from the same construction. In particular,
   identify each synthetic cubical boundary with the appropriate
   synthetic sphere by induction, not by a dimension-specific analogy.
4. **Prove the comparison with real homotopy and spheres.** Keep finite
   regularization, relative representatives, multiplication, cubical
   subdivision/cover descent, and the two-cap sphere induction explicit.
   The classifying realization alone does not prove these theorems.

The target remains

```text
GroupIso (realπGr n (RealSphere∙ m)) (Synthetic.πGr n (S₊∙ m)).
```

The geometric sphere dimension `m` and homotopy degree `n+1` remain
independent. An auxiliary category or cubical nerve must not change either
side of this goal, require decidable equality of UC functions, or replace
the synthetic target by the set carrier of a real sphere.

## Status of the revision

The former instruction to try the degree-three overlap next is withdrawn.
Direct latching attachments remain a possible implementation of a proved
generic realization theorem; they are not currently an established
all-dimensional algorithm. The cubical classifying-space candidate has
uniform source formulas and established external motivation, but the
internal constructive realization gate remains open. This is the exact
obstacle to resolve before further implementation.

Two agents audited the source and construction without running Agda or
editing files. This initial revision made no Agda changes. Subsequent
independent uniform constructions are recorded in
[UNIFORM_CONSTRUCTIONS.md](UNIFORM_CONSTRUCTIONS.md); they do not add
another realization stage. The earlier five checked modules are preserved;
verification is recorded in [PROGRESS.md](PROGRESS.md).
