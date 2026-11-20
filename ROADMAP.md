# Roadmap

Known mathematics awaiting formalization, and the reconnaissance
that decides where the open questions of [`README.md`](README.md)
(Q1–Q7) actually lie. Every target
names
its landing; these results stay useful whatever the experiments
say.

The abstract lattice calculus belongs to **Descent**; Theaetetus
owns its Gaussian and arithmetic realization. Reuse across that
boundary should be an ordinary Lake dependency pinned to an
immutable revision, with a narrow imported surface and a local
bridge module. A mutable sibling-path dependency would make builds
checkout-dependent, while copying the hierarchy would create two
sources of truth. That boundary has landed: Descent is a Lake
dependency pinned to an immutable revision, and the bridge module
`Theaetetus.HigherInteraction` identifies the four-term
`fieldDefect` of any partition field with `Descent.defect` of its
fixed-scale logarithmic context field on the carrier of positive
naturals under divisibility (`fieldDefect_eq_defect`); the same
imported surface carries `Theaetetus.SublatticeDiamond` on the
subgroup lattice of `ℤ²`. The abstract hierarchy is consumed,
never forked. The dependency is
passive as well as one-way: Theaetetus does not schedule changes in
Descent, advance its roadmap, or require its active development to
accommodate this project. Adapter lemmas and application-specific
corollaries live here against the pinned release. A result that may
belong upstream is recorded only as a **Consider upstreaming to
Descent** note; Descent's own team decides whether and when to
harvest it, and Theaetetus continues without waiting.

Formalization targets:

01. **Higher-rank defect duality** — done. The defect construction
    applies to any partition field (`fieldDefect`), with the
    scalar, tower, and Gram defects as instances
    (`defect_eq_fieldDefect`,
    `PartitionTower.defect_eq_fieldDefect`,
    `gramDefect_eq_fieldDefect`), and the law the four-term
    alternating sum obeys is isolated once: **the defect
    annihilates affine log weights**
    (`fieldDefect_dual_of_log_reflect`) — the constant by sign
    count zero, the log-linear part by `gcd·lcm = q·q′`. The
    structural laws are generic too — symmetry, vanishing on
    chains, vanishing on the diagonal (`fieldDefect_comm`,
    `fieldDefect_eq_zero_of_dvd`, `fieldDefect_self`) — and the
    scalar and tower instances inherit them rather than reprove
    them. The Gram
    chart engine (`Theaetetus.GramDuality`): the Boltzmann sum of
    a positive-definite Gram form reflects through the dual Gram,
    `gramTheta M⁻¹(π²/α) = (α/π)^(d/2)·det(M)^(1/2)·gramTheta M α`
    (`gramTheta_dual`, from the Gaussian Poisson summation of
    `Theaetetus.Periodization`) — an affine log weight, so the
    Gram defect reflects with no weight at all
    (`gramDefect_dual`), only the coupling moving at coprime
    resolutions (`gramDefect_dual_coprime`); at rank one with unit
    Gram this is the scalar theory (`gramTheta_one_eq_theta`,
    `gramDefect_one_eq_defect`), `defect_dual` the rank-one case
    and `theta_rect_dual` the multiplicative engine beneath it.
    The intrinsic lift (`Theaetetus.LatticeDuality`): every Gram
    chart computes the basis-free partition function
    (`QuadLatticeAction.scaledPartFn_eq_gramTheta`), so two
    integral bases produce the same Gram defect
    (`QuadLatticeAction.gramDefect_gram_eq`), the intrinsic defect
    (`QuadLatticeAction.defect`) is chart-computed
    (`QuadLatticeAction.defect_eq_gramDefect`) and at unit scale
    is the tower defect
    (`QuadLatticeAction.toPartitionTower_defect`); the dual
    lattice is intrinsic — the `ℤ`-dual module with the
    inverse-Gram pairing (`QuadLatticeAction.dual`), whose chart
    at the dual basis of *every* integral basis is the inverse
    Gram (`QuadLatticeAction.dual_gram_at`, with
    `QuadLatticeAction.dual_gram` the chosen-chart instance), so
    the basis hidden in the construction does not matter — and the
    duality lands on `L` and `L*`:
    `QuadLatticeAction.defect_dual`.

02. **Strict Q5 for positive diagonal forms** — done
    (`diagTheta_rect_strict`, `diagTheta_sq_lt`, lifted from
    `theta_rect_strict` by the `Theaetetus.Diagonal` pattern), and
    the orthogonal-sum reduction with it
    (`Theaetetus.OrthogonalSum`): the orthogonal sum of two
    lattice actions (`QuadLatticeAction.orthSum`) multiplies
    partition functions (`QuadLatticeAction.orthSum_scaledPartFn`,
    with positivity `QuadLatticeAction.scaledPartFn_pos`), adds
    defects (`QuadLatticeAction.orthSum_defect`, through the
    generic laws `fieldDefect_congr` and `fieldDefect_mul`), and —
    because every factor's defect is nonpositive — vanishes iff
    every factor's defect vanishes
    (`QuadLatticeAction.orthSum_defect_eq_zero_iff`): any
    zero-defect witness descends past every orthogonal
    decomposition. At real scale the strict rectangle inequality
    is preserved by orthogonal sums
    (`QuadLatticeAction.orthSum_rect_strict`), so any failure of
    Q5 strictness descends to a factor
    (`QuadLatticeAction.rect_strict_descend`) — the promised
    counterexample reduction.

03. **The Regev–Stephens-Davidowitz implication** — done. The
    substrate (`Theaetetus.ShiftedMass`): the shifted Gaussian
    mass `gramMass M α x = ∑_{k∈ℤᵈ} e^{−α·Q(x+k)}`, its residue
    decomposition mod `n` (`gramMass_coset`), and the parity
    transport of a product — the parallelogram law splits the
    Gaussian, parity splits the image (`gramMass_mul_gramMass`).
    The geometry (`Theaetetus.Correlation`): the **parity feature
    vector** (`parityVector`) with its two identities — a product
    of masses is an inner product of feature vectors
    (`gramMass_mul_eq_inner`), and a squared norm is a mass
    product (`sum_sq_parityVector`) — so Cauchy–Schwarz gives the
    correlation inequality `m(x)²·m(y)² ≤ m(0)²·m(x+y)·m(x−y)`
    (`gramMass_sq_mul_sq_le`), its averaged form
    (`gramMass_mul_le_avg`), monotonicity under scalar dilation
    (`gramMass_dilate_mul_le`), and positive correlation at
    coprime dilations (`gramMass_coprime_mul_le`). With the
    coprime reduction of the field defect
    (`fieldDefect_div_gcd`), the sign lands: the defect is
    nonpositive for every positive-definite Gram form
    (`gramDefect_nonpos`) and every lattice action
    (`QuadLatticeAction.defect_nonpos`) — Q1's inequality half,
    at every rank. The defect is logarithmic correlation slack
    whose sign is controlled by the parity-vector Cauchy–Schwarz
    geometry; equality demands simultaneous saturation —
    collinearity of the feature vectors, the AM–GM equality, and
    every residue-class inequality in the chain.

04. **The Q2 recovery formula** — done
    (`tendsto_defect_row_sub_succ` at `PartitionTower` level,
    instantiated at rank one as `tendsto_defect_recovery`), in the
    datum-honest form: a single limit of differences of entries of
    one fixed-scale defect matrix,
    `D_s(m, km+1) − D_s(k+1, k+2) → F_s(m)`.

05. **The certification chain** for higher-rank numerics — done:
    coercivity, tails, moments, shell counts, and two-sided
    spectral bounds, all reduced to finitely many checkable
    inequalities. `Theaetetus.Fluctuation`'s geometric-domination
    bounds were the rank-one shapes. Coercivity
    (`Theaetetus.Certification`): `μ` is a coercivity constant for
    a Gram form — `μ·∑xᵢ² ≤ xᵀQx` — iff it lower-bounds every
    eigenvalue (`Matrix.IsHermitian.mul_sum_sq_le_quadForm`,
    `Matrix.IsHermitian.le_eigenvalues_of_mul_sum_sq_le`,
    `Matrix.IsHermitian.mul_sum_sq_le_quadForm_iff`), and the same
    holds above (`Matrix.IsHermitian.quadForm_le_mul_sum_sq`,
    `Matrix.IsHermitian.eigenvalues_le_of_quadForm_le`,
    `Matrix.IsHermitian.quadForm_le_mul_sum_sq_iff`); row dominance
    `μ + ∑_{j≠i}|Qᵢⱼ| ≤ Qᵢᵢ` — finitely many entrywise
    inequalities, rational arithmetic when the entries are
    rational — certifies the lower bound, positive definiteness,
    and a spectrum-wide `μ ≤ λ`
    (`mul_sum_sq_le_quadForm_of_dominant`, `posDef_of_dominant`,
    `le_eigenvalues_of_dominant`), dominance from above caps the
    spectrum (`quadForm_le_mul_sum_sq_of_dominant`,
    `eigenvalues_le_of_dominant`), and a single form evaluation at
    a concrete vector drives an eigenvalue out of a half-line in
    either direction (`Matrix.IsHermitian.exists_eigenvalues_lt`,
    `Matrix.IsHermitian.exists_lt_eigenvalues`) — the interval
    algebra for extremal eigenvalues. Coercivity transfers to
    lattice energies (`QuadraticAction.mul_sum_sq_le_energy`).
    Tails (`Theaetetus.Tails`): the lattice sum of a product weight
    factorizes exactly (`QuadraticAction.tsum_finPi_prod`), the
    scalar tail beyond radius `N` is geometrically dominated
    (`theta_tail_le`), any energy dominating `ν·∑kᵢ²` has its
    Boltzmann sum outside the sup-norm box bounded by
    `r·θ(ν)^{r−1}` copies of the scalar tail (`tail_exp_le`,
    instantiated as `QuadraticAction.tail_le`), the partition
    function splits into a finite box plus a certified truncation
    error (`QuadraticAction.partFn_le_box_add_tail`, packaged as
    the enclosure `QuadraticAction.partFn_mem_box_Icc`), and
    polynomial energy weights absorb at half coupling —
    `xᵐ·e^{−x} ≤ 2ᵐ·m!·e^{−x/2}` — so every energy-moment tail is
    the plain tail at `μ/2` with the factorial constant
    (`QuadraticAction.moment_tail_le`). Shell counts
    (`Theaetetus.Shells`): coercivity confines energy sublevels to
    boxes (`QuadraticAction.abs_le_of_energy_le`), so they are
    finite (`QuadraticAction.finite_energy_sublevel`) with at most
    `(2N+1)^r` sectors once `R < μ(N+1)²`
    (`QuadraticAction.energy_sublevel_ncard_le`), and every energy
    shell obeys the same bound
    (`QuadraticAction.energy_shell_ncard_le`). Certified this way,
    a reconnaissance sign is a certificate — and a counterexample
    arrives pre-packaged for its own formalization.

06. **`Theaetetus/Status.lean`** — done: the statement-level
    manifest exists — every claim this document makes of the
    tree, restated as an `example` discharged by the theorem it
    cites, so statement drift fails `lake build`. The companion
    docstring sweep is also done: no Lean docstring or comment
    references a prose coordinate (the one-way rule, now in
    `AGENTS.md`).

07. **The higher-interaction bridge** — done. Descent remains the
    source of truth for the order-separated hierarchy: `defect3`,
    `defectFam`, the raw-cube isolation identity
    (`mixedDiff_triple_inf`), distributive decomposition
    (`defect3_decompose`, `gauge3_eq_gauge`), and universal
    saturation (`gaugeFam_eq_gauge3`). The Theaetetus landing is a
    thin bridge, not a reimplementation:

    - identify its positive-natural `fieldDefect` with Descent's
      pairwise defect on the arithmetic carrier — done
      (`fieldDefect_eq_defect` in `Theaetetus.HigherInteraction`,
      through the logarithmic context field `logField`);
    - prove the pairwise-coprime family telescope and compose it with
      `defect_neg_of_incomparable` and
      `QuadLatticeAction.defect_nonpos`, giving the strict rank-one
      and non-strict all-lattice sign laws for every corrected order
      — done (`defectFam_logField_eq_telescope`, from Descent's
      coprime telescope through the coprime join
      `supFam_of_pairwiseCoprime`, with elimination order immaterial
      by `telescope_eq_of_perm`; signs in `defectFam_theta_neg` and
      `QuadLatticeAction.defectFam_nonpos`);
    - isolate the raw `2,3,5` mixed difference as a combination of
      pairwise entries, explaining its sign change without promoting
      it to a new observable — done
      (`mixedDiff_triple_of_pairwiseCoprime` generically,
      `mixedDiff_two_three_five` at the observed triple, against the
      corrected sign `defect3_theta_235_neg`);
    - formalize the canonical `M₃` witness from the three index-two
      sublattices of `ℤ²` — done (`Theaetetus.SublatticeDiamond`).
      The five sublattices
      `2ℤ² ≤ {a even}, {b even}, {a+b even} ≤ ℤ²` realize the
      diamond faithfully in the subgroup lattice of `ℤ²`
      (`diamondHom`, `diamondSub_injective`), with distinct atoms meeting at `2ℤ²` and joining to `ℤ²`. Each is priced by
      its own convergent Gaussian mass (`latMass`, `latMass_pos`),
      and the table is exact — `ρ(ℤ²) = θ(s)²`, `ρ(2ℤ²) = θ(4s)²`,
      `ρ({a even}) = ρ({b even}) = θ(s)·θ(4s)`,
      `ρ({a+b even}) = θ(2s)²` (`latMass_top`, `latMass_evenBoth`,
      `latMass_evenFst`, `latMass_evenSnd`, `latMass_evenSum`, the
      last through the parity rotation `(u,v) ↦ (u+v, u−v)`, whose
      energy is `2(u²+v²)`). The coordinate pair splits
      orthogonally and has zero defect
      (`defect_evenFst_evenSnd`); the other two pairs share the
      strict midpoint defect
      `2·log θ(2s) − log θ(s) − log θ(4s) < 0`
      (`defect_evenFst_evenSum_eq_evenSnd`,
      `defect_evenFst_evenSum_neg`, `defect_evenSnd_evenSum_neg`).
      The exact order-3 recurrence kills all three pairwise terms
      and leaves the field gap across the distributivity-defect
      interval `[2ℤ², {a+b even}]` (`distrib_interval`), so
      `D₃ = 2·log(θ(2s)/θ(4s)) > 0` (`defect3_diamond`,
      `defect3_diamond_eq`, `defect3_diamond_pos`, using the strict
      decrease of `theta` on positive couplings, `theta_lt_theta`),
      and `D₃ → log 2` as `s → 0⁺` (`tendsto_defect3_diamond`).
      The contrast is packaged: every pairwise observation on the
      realized diamond is nonpositive
      (`defect_diamondHom_nonpos`) while this order-three one is
      positive. And the limit is an index: each atom has index two
      in `ℤ²` (`index_evenFst`, `index_evenSnd`, `index_evenSum`),
      the doubled lattice has index two inside the checkerboard
      (`relIndex_evenBoth_evenSum`), and the boundary value is the
      logarithm of that relative index
      (`tendsto_defect3_diamond_index`).

    This closes the original resolution-tower question and opens the
    genuinely new one on non-distributive sublattice carriers.

    **Where the telescope lives:** the abstraction is Descent's —
    the telescope of a family (`Descent.telescope`), its value on
    telescopic and pairwise disjoint families in a distributive
    lattice (`Descent.defectFam_eq_telescope`,
    `Descent.defectFam_eq_telescope_of_pairwise_disjoint`), and its
    coprime specialization on the arithmetic carrier
    (`Descent.Arith.defectFam_eq_telescope_of_pairwise_coprime`).
    Theaetetus keeps the arithmetic reading — the coprime join as a
    product, the telescope as a sum of field defects
    (`telescope_eq_descent_telescope`) — and the sign corollaries.

08. **The star obstruction** — done (`deficit_not_psd`,
    `cnd_not_psd` in `Theaetetus.StarObstruction`): the explicit
    star-weight witness closed it without eigenvalue machinery.
    What remains under this heading is the rate (Q4-PSD).

09. **Spectral peeling** — done (`Theaetetus.Peeling`): local
    finiteness, attainment, both extraction limits with sampled
    forms, the residual subtower with its bridge, strict
    progress, the telescoped peel sequence, every layer as a
    limit of the original data alone, and exhaustion — the
    composite carrier embedding (`peelEmbed`) eventually excludes
    every nonmodal sector (`exists_notMem_range_peelEmbed`), so
    the residual tail vanishes (`tendsto_peel_Z`) and the layers
    sum to the whole excess, `Σₙ Nₙ·e^{−β·λₙ} = Z(β) − 1` for
    `β ≥ 1` (`hasSum_peel_layers`, `tsum_peel_layers`). One fixed
    defect matrix determines the full spectrum with
    multiplicities.

10. **The equality chain.** Zero defect forces simultaneous
    saturation of every inequality in the correlation proof:
    collinearity of the parity feature vectors in Cauchy–Schwarz,
    the AM–GM equality `m(x+y) = m(x−y)`, and the saturation of
    each residue-class instance in the dilation and coprime
    telescopes. The two analytic links are done
    (`Theaetetus.CorrelationEquality`), and as biconditionals:
    Cauchy–Schwarz equality is exactly positive collinearity of the
    two parity feature vectors (`ParityCollinear`,
    `gramMass_sq_mul_sq_eq_iff`), resting on a general criterion
    for strictly positive finite vectors
    (`sum_mul_sq_eq_sq_mul_sq_iff_of_pos`, by the Lagrange
    identity), and the averaged bound is an equality exactly when
    that collinearity holds together with the reflected-mass
    equality `m(x+y) = m(x−y)` (`gramMass_mul_eq_avg_iff`) — which
    collapses further to literal equality of the two parity feature
    vectors (`gramMass_mul_eq_avg_iff_parityVector_eq`), the
    canonical form for the chain, the conjunction being kept to
    expose the two links separately. The dilation-level residue
    saturation is done too: both sides of `gramMass_dilate_mul_le`
    are sums over residue classes of the same averaged bound at the
    named shifts `dilateShift n x` and `residueShift n c`
    (`gramMass_dilate_mul_eq_sum`, `gramMass_dilate_avg_eq_sum`),
    a dominated sum meets its dominating sum exactly when every
    term does (`sum_eq_iff_of_le`), and so scalar dilation is an
    equality exactly when every residue class is
    reflection-invariant (`gramMass_dilate_mul_eq_iff`). The
    coprime resummation closes the same way one grid out: both
    sides of `gramMass_coprime_mul_le` are sums over the `b`-grid
    of the two sides of dilation monotonicity at the outer shifts
    `dilatedResidueShift a b r` (`gramMass_coprime_mul_eq_sum`,
    `gramMass_coprime_avg_eq_sum`, the second through the named
    unit resummation `sum_gramMass_dilatedResidueShift`), so
    equality is class-by-class saturation
    (`gramMass_coprime_mul_eq_iff_forall_class`), and since the
    outer shift normalizes
    (`dilateShift_dilatedResidueShift`) the criterion is two-grid
    (`gramMass_coprime_mul_eq_iff`): correlation at coprime
    dilations is an equality exactly when

    ```
    P(v_r + v_c) = P(v_r − v_c)   for all r mod b, c mod a,
    ```

    with `P` the parity feature vector at the joint scale — every
    point of the `b`-grid a reflection center for the `a`-grid.
    Each equality has reflection form, and that question is now
    settled — negatively, and modulo the lattice, which is the
    widest closure a periodic mass can offer. Chaining two
    instances needs the reflected point of one to be a sampled
    point of the other only up to an integer vector; even so, at
    coprime dilations that forces twice the composed displacement
    to be integral (`chain_displacement_int`) and the two outer
    points to be congruent modulo `ℤ^d` (`chain_endpoints_int`), so
    the composed equality holds by periodicity alone, criterion or
    not (`gramMass_chain_eq`). The sampled fibers close only
    trivially, and no rigidity follows from composition.
    The chain now reaches
    the defect itself. For a positive field, vanishing at a coprime
    pair is exactly multiplicativity across the rectangle
    `{a, b, 1, a·b}` (`fieldDefect_eq_zero_iff_mul_eq`, generic and
    logarithm-only), so a vanishing Gram defect is exactly the mass
    identity (`gramDefect_eq_zero_iff_mul_eq`) and hence exactly
    the criterion (`TwoGridReflection`,
    `gramDefect_eq_zero_iff_twoGridReflection`); intrinsically, a
    lattice action has zero defect at a coprime pair exactly when
    the criterion holds in an integral chart
    (`QuadLatticeAction.defect_eq_zero_iff_twoGridReflection`), and
    therefore in one chart exactly when in every other
    (`QuadLatticeAction.twoGridReflection_gram_iff`). The equality
    chain is complete through the intrinsic two-grid criterion.

    The sole mathematical remainder is one rigidity statement: in
    positive rank, for coprime `a, b > 1`, the two-grid parity
    reflection condition is impossible. It now has a Fourier form
    (`Theaetetus.ReflectionFourier`). The shifted mass is the
    periodized Gaussian of the rescaled form
    (`gramMass_eq_periodization`), so it expands in cosines over
    the dual lattice with strictly positive Gaussian coefficients
    (`massFourierCoeff_pos`, `hasSum_massFourier` in character form
    and `hasSum_massFourier_cos` in real form); reflection
    about `y` under displacement `t` is exactly the vanishing of
    `∑ C_m·sin(2π⟨m,y⟩)·sin(2π⟨m,t⟩)` (`gramMass_reflect_iff`);
    and the criterion is that family over anchors of the
    parity-refined `b`-grid — which is the `2b`-grid,
    `anchorShift_eq_residueShift` — and displacements of the half
    `a`-grid (`twoGridReflection_iff_fourier`). That cancellation
    question now has its exact finite form. The criterion is
    symmetric in the pair (`twoGridReflection_comm`), so orient it
    with `a` odd; then `a` is coprime to `2b`, the anchor and
    displacement digits fuse into a single index on the `2ba`-grid
    (`jointIndex`, bijective), and reflection is multiplication of
    that index by a CRT involution — `1` mod `2b`, `−1` mod `a`
    (`exists_crtInvolution`, `crtInvolution_dvd`), nontrivial for a
    nontrivial pair (`crtInvolution_nontrivial`). The criterion is
    then a dilation invariance of the sampled mass
    (`twoGridReflection_iff_crt`), and grouping the dual lattice
    into residue classes turns it into invariance of the alias
    sums, each strictly positive (`aliasSum`, `aliasSum_pos`,
    `gramMass_eq_sum_aliasSum`):

    ```
    A_ν = A_{Uν}   for every dual class ν
    ```

    (`twoGridReflection_iff_alias`, by linear independence of the
    grid characters). At rank one the invariance already fails,
    since the strict sign theorem makes an incomparable defect
    negative (`not_twoGridReflection_rankOne`,
    `exists_aliasSum_ne_rankOne`); the open statement is that the
    failure persists in every positive rank. The first falsify-first
    campaign against that statement is recorded under
    reconnaissance: no counterexample in the committed samples
    (ranks 2–3, every slack sign certified by ball arithmetic), an
    observed `residual ≈ ½·√slack` along one profile of the only
    sampled route toward zero, a certified crossing that stops
    symmetry from reading as a uniform strengthening or weakening of
    the obstruction, and — by an exact but unformalized argument —
    the exclusion, in every positive rank, of an integral isometry
    inducing the CRT dilation: Minkowski's lemma makes `S² = I`, so
    `(I − S)/2` is an integral idempotent divisible by `b > 1` and
    therefore zero. What remains is an accidental equality of
    Gaussian mass values with no isometry behind it, which is an
    analytic question, not a structural one.

    The same positivity gives the first purely analytic rigidity
    statement about the mass itself (`Theaetetus.MassMaximum`).
    Against the expansion at the origin, where every character
    contributes its full weight, any other shift loses `1 − cos` of
    each, so the mass is maximal on the lattice and strictly
    submaximal off it: `gramMass M α x ≤ gramMass M α 0` with
    equality exactly at lattice shifts
    (`gramMass_le_gramMass_zero`, `gramMass_lt_gramMass_zero`,
    `gramMass_eq_gramMass_zero_iff`, transported entrywise by
    `parityVector_eq_max_iff`). No accidental maximizer exists at
    any positive coupling in any rank. That principle also settles
    what it can do against the criterion on its own: the two
    reflected shifts differ by the displacement `residueShift a c`,
    both can be maximal only if that displacement is a lattice shift
    (`isLatticeShift_of_add_of_sub`), and a residue shift is a
    lattice shift only at the zero class — for every positive
    modulus, no coprimality needed
    (`isLatticeShift_residueShift_iff`) — where the criterion is an
    identity anyway (`parityVector_zero_displacement`). So every
    nonzero-displacement pair sits strictly below the maximum on
    both sides (`twoGridReflection_lt_max`, a conjunction of the two
    strict inequalities), and the equality the criterion asserts is
    always between two strictly submaximal masses. The maximum
    principle alone therefore cannot contradict the criterion; what
    it contributes alongside a second comparison principle is open.
    The next analytic mechanism has to control the shape or
    multiplicity of a submaximal level set, not merely locate the
    top.

    The submaximal geometry has a classical name. Writing `ĉ` for
    the parity digit and expanding
    `parityVector(M,α,z)_c = gramMass(M, 2α, (z + ĉ)/2)` around
    `n = k + ĉ/2` gives, exactly,

    ```
    parityVector(M,α,z)_c
      = e^{−α zᵀMz/2} · Θ[c]( iαM/π , iαMz/(2π) ),
    ```

    under the convention
    `Θ[σ](τ,w) = Σ_{n ∈ ℤᵈ + σ/2} exp(2πi nᵀτn + 4πi nᵀw)`. The
    period matrix is a genuine Siegel point, since `Im τ = αM/π` is
    positive definite, and the prefactor `e^{−α zᵀMz/2}` is common
    to every coordinate — so equality of raw parity vectors already
    implies equality in the projective map. Those `Θ[σ]` are the
    second-order theta coordinates, and for an **indecomposable**
    principally polarized abelian variety the map they define is the
    Kummer embedding: two-to-one, identifying `z` with `−z` and
    nothing else. A decomposable variety instead carries one sign
    per factor, so no single global sign describes its fibers. (For
    the standard coordinates and the embedding see Grushevsky,
    [*Cubic equations for the hyperelliptic locus*](https://archive.intlpress.com/site/pub/files/_fulltext/journals/ajm/2004/0008/0001/AJM-2004-0008-0001-a012.pdf).)

    The real locus is what turns that geometry into exactly the
    predicate used here. The theta argument is
    `W(z) = iαMz/(2π) = τz/2`, so Kummer separation says
    `W(z) ≡ ±W(w)` modulo the period lattice `ℤᵈ + τℤᵈ`, that is
    `τ(z ∓ w)/2 = m + τn` with `m, n ∈ ℤᵈ`. But `z` and `w` are
    real and `τ` is purely imaginary, so both `τ(z ∓ w)/2` and `τn`
    are purely imaginary while `m` is real: hence `m = 0`. Since
    `τ = iαM/π` is invertible for `α > 0` and `M` positive definite,
    `(z ∓ w)/2 = n ∈ ℤᵈ` — precisely the two alternatives of
    `ParitySeparating`. The predicate is not merely reminiscent of
    Kummer geometry; it is that injectivity statement restricted to
    the real locus, written in these coordinates.

    Siegel theta is not constructed in this development, so
    `Theaetetus.ParitySeparation` takes that property as a named
    hypothesis in the normalization above (`ParitySeparating`) and
    settles what it is worth. It is worth the whole statement: the
    criterion asserts
    `parityVector (v_r + v_c) = parityVector (v_r − v_c)` for every
    residue pair, separation turns each such equality into
    `v_c ∈ ℤᵈ` or `v_r ∈ ℤᵈ`, and a residue shift is a lattice shift
    only at the zero class, so at `a, b > 1` in positive rank both
    can be chosen nonzero at once and the criterion fails
    (`not_twoGridReflection_of_paritySeparating`,
    `gramDefect_neg_of_paritySeparating`).

    One direction of its unavailability is proved. If the
    coordinates split into blocks with no cross terms, negating one
    block preserves the form and the lattice, hence every entry of
    the parity vector (`gramMass_flipCoords`,
    `parityVector_flipCoords`), while moving the point off `±z`; so
    every proper coordinate block splitting destroys separation
    (`not_paritySeparating_of_split`). Such a form carries one sign
    per block, not one sign overall. The converse — that separation
    holds whenever no such splitting exists — is not proved, and
    neither is the reduction of a split form to its blocks.

    Separation is classically proved through the zero divisor of the
    theta function, and the shifted mass has no zeros, so that
    argument does not descend directly to one phrased in the
    positive real mass alone. It could still be imported through
    complex geometry; `Theaetetus.EvenPartSeparation` opens a purely
    real alternative, and completing it requires the Fourier
    certificate described below. That module isolates what the real
    locus
    actually consumes. It is one application of the addition
    identity `gramMass_mul_eq_inner`, which is the theta addition
    formula in this normalization. Pairing both sides of a parity
    equality against the vector at an arbitrary displacement turns
    the `2^d`-entry equality into a one-parameter family of scalars,

    ```
    m((z+u)/2)·m((z−u)/2) = m((w+u)/2)·m((w−u)/2)
    ```

    (`gramMass_reflect_prod_of_parityVector_eq`), and taking
    logarithms — legitimate, the masses being positive — says that
    the even part of `logMass` about `z/2` equals the even part
    about `w/2` (`logMass_even_part_eq_of_parityVector_eq`). So
    separation follows from a property of the logarithmic mass
    alone: that its even part about a point determines the point up
    to sign (`EvenPartSeparating`,
    `paritySeparating_of_evenPartSeparating`,
    `gramDefect_neg_of_evenPartSeparating`). The block obstruction
    transports by contraposition
    (`not_evenPartSeparating_of_split`).

    That reduction settles the shape of the remaining work. Writing
    `L = logMass M α` — real-valued, `ℤᵈ`-periodic, and even;
    positivity belongs to `gramMass`, not to its logarithm — with
    Fourier coefficients `ℓ_ν` on `ℝᵈ/ℤᵈ`, the even-part equation
    reads coefficientwise as

    ```
    ℓ_ν · cos(2πν·a) = ℓ_ν · cos(2πν·b)   for every ν ∈ ℤᵈ,
    ```

    and at a frequency with `ℓ_ν ≠ 0` this says `ν·(a−b) ∈ ℤ` or
    `ν·(a+b) ∈ ℤ`. The frequencies `ν = e_i` put each coordinate on
    at least one branch — possibly both, and such a coordinate is
    *flexible*. The frequencies `ν = e_i + e_j`, `i ≠ j`, rule out
    the coexistence of a coordinate *forced* onto the difference
    branch with one *forced* onto the sum branch: for such a pair
    both `(a−b)_i + (a−b)_j` and `(a+b)_i + (a+b)_j` are
    nonintegral. Flexible coordinates then adopt whichever branch
    survives, and one branch serves the whole vector. That step is
    pure arithmetic and is already proved
    (`isLatticeShift_or_of_pairwise`), flexible coordinates handled
    explicitly, so the subtlety cannot become a hidden gap in the
    analytic layer.

    The sufficient hypothesis is therefore nonvanishing of `ℓ_ν` on
    the **finite** family `{e_i} ∪ {e_i + e_j : i ≠ j}` — not on all
    `ν ≠ 0`, which is a much stronger demand than target 10 makes,
    may fail at special forms or couplings, and has not been
    investigated. In the other direction one implication is proved:
    a proper coordinate block splitting destroys
    `EvenPartSeparating`. Fourier analysis explains that
    obstruction — for `M = M₁ ⊕ M₂` the mass factorizes, so
    `L(x) = L₁(x₁) + L₂(x₂)` and `ℓ_ν = 0` at every block-mixing
    frequency, exactly at every coupling, because the logarithm
    turns the product into a sum. Nothing yet shows that every
    vanishing coefficient, or every failure of separation, arises
    from a splitting: the Fourier support is a certificate and a
    diagnostic until that relationship is proved. The certificate is
    also **chart-dependent**: the conclusion it yields is
    geometrically meaningful, but the frequencies `e_i` and
    `e_i + e_j` are those of a particular integral chart, so
    nonvanishing on that family is a sufficient condition in that
    chart, not an intrinsic characterization of indecomposability.

    Two consequences for the roadmap. First, the route needs a
    Fourier layer on `ℝᵈ/ℤᵈ` for the logarithmic mass, not a Siegel
    theta library and not a symplectic decomposition layer: the real
    argument never constructs the abelian variety, and the classical
    statement now serves only as motivation for a predicate that a
    purely real one implies. Second, the question of whether
    decomposability of the associated principally polarized abelian
    variety coincides with orthogonal decomposability of `(ℤᵈ, M)`
    is therefore off the critical path, and it is **not settled
    here**. What is settled about it: the two notions have different
    invariance groups — `Sp(2d,ℤ)` against `GL_d(ℤ)` — and the
    period map is not injective on quadratic lattices, since
    `τ ↦ −τ⁻¹` carries `iT` to `iT⁻¹`, so `(ℤ, t)` and `(ℤ, 1/t)`
    give the same elliptic curve while they are not isometric
    lattices. That non-injectivity does not by itself produce a
    decomposability mismatch, because `UᵀTU = T₁ ⊕ T₂` gives
    `(U⁻¹)ᵀT⁻¹U⁻¹ = T₁⁻¹ ⊕ T₂⁻¹`, so orthogonal splitting survives
    inversion. Whether some `Sp(2d,ℤ)` element outside that
    subgroup makes a lattice-indecomposable `M` decomposable as a
    ppav at special couplings is open, and no claim either way is
    made.

    That certificate has been through a falsification gate before
    any of it is formalized (`recon/logfourier.py`, record in
    `log_fourier.json`, findings in `recon/README.md`;
    **not certified** — high-precision floating point with a spectral
    quadrature whose aliasing is estimated by grid doubling, not
    bounded). It computes `ℓ_ν` on exactly
    `{e_i} ∪ {e_i + e_j : i < j}` over ranks 1–3: the diagonal
    controls, `hexagonal` and `fcc`, unimodular recharts of each, a
    non-integral shear, and near-decomposable probes `[[1,ε],[ε,1]]`.
    The self-dual coupling of the raw form is `α* = π/det(M)^{1/d}`,
    equal to `π` only after determinant normalization, and the grid
    varies by form — rank one and most rank-two forms straddle the
    centre; `diag2_r16` and the rank-three forms do not.

    Three checks anchor it. The rank-one coefficient matches the
    closed form `q/(1−q²)` from the Jacobi triple product. Exact
    references cover every diagonal form and, through
    `ℓ′_ν = ℓ_{U⁻ᵀν}`, every unimodular rechart of one — which makes
    the sheared square lattices sharp controls rather than suggestive
    ones. And an independent Poisson evaluation of the mass agrees to
    `1.6e−30`, at one recorded probe point per row.

    It did **not** falsify the certificate. Each form carries an exact
    structural audit — a rational search for a `v` with
    `ℤᵈ = ℤv ⊕ (v^⊥ ∩ ℤᵈ)`, exhaustive for rank at most three — and
    against that classification the 32 rows resolving nonzero at every
    frequency are exactly the rows on indecomposable forms, the 20
    with an unresolved frequency exactly those on decomposable ones.
    Which frequency fails is chart dependent, at exactly the place the
    rechart predicts: the square lattice loses `(1,1)` in the standard
    chart and `(1,0)` in the `t = 1` shear chart. Signs are chart
    dependent too, while nonvanishing survives every rechart sampled,
    no resolved coefficient changes sign across the coupling grid, and
    the two near-decomposable probes are positive and smaller at the
    smaller `ε`. That is evidence for attempting the analytic layer,
    not a proof of nonvanishing, and the split against decomposability
    is an observation on the sample, not a proved equivalence.

    That conditional layer is now formal
    (`Theaetetus.LogMassFourier`). The logarithmic mass descends to
    the unit torus through the Gaussian periodization already there
    (`logMassTorus`, `logMassTorus_mk`), positivity makes the
    logarithm continuous (`continuous_logMassTorus`), and Mathlib's
    multivariate transform supplies the coefficients
    (`logMassCoeff`). Evenness and reality of the mass make every
    coefficient real and symmetric in the frequency
    (`logMassCoeff_neg`, `logMassCoeff_conj`,
    `logMassCoeff_eq_ofReal`). The coefficient equation is obtained
    by applying the functional to two functions that are literally
    equal — no reconstruction of the field from its series — using
    only translation invariance, since evenness rewrites `L(a − v)`
    as `L(v − a)`: from equality of even parts,
    `ℓ_ν·cos(2π⟨ν,a⟩) = ℓ_ν·cos(2π⟨ν,b⟩)` at every frequency
    (`logMassCoeff_cos_eq`). With the singleton and distinct-pair
    frequencies named (`freqSingle`, `freqPair`), nonvanishing on
    exactly that finite family
    (`FiniteCertificate`) implies the even-part property
    (`evenPartSeparating_of_finiteCertificate`) and hence strict
    negativity of the coprime defect
    (`gramDefect_neg_of_finiteCertificate`). Composed with the block
    obstruction, the certificate is formally a splitting diagnostic
    as well: a form whose coordinates split with no cross terms
    admits no finite certificate
    (`not_finiteCertificate_of_split`) — that direction only.
    Nonvanishing itself is not proved, assumed, or estimated there.

    The first analytic foothold under that certificate is the
    cluster normalization (`Theaetetus.ClusterExpansion`). Dividing
    the positive dual expansion by its zero-frequency weight puts the
    mass in the form `zeroMode·(1 + residual)`
    (`gramMass_eq_zeroMode_mul`), where the residual carries only
    nonzero dual modes (`hasSum_residual`) and is bounded uniformly
    in the shift by their total relative weight
    (`abs_residual_le_totalWeight`). That weight is exactly the
    excess of the mass at the origin over its zero mode, and is
    literally the sum of the nonzero relative mode weights
    (`hasSum_totalWeight`), so the determinant-normalized asymptotic
    measures it: as the coupling falls to zero the dual energies,
    scaling like `π²/α`, spread out and the weight vanishes
    (`totalWeight_eq_scaled`,
    `tendsto_totalWeight_nhdsGT_zero`,
    `eventually_totalWeight_lt`). Below unit weight the logarithm
    expands convergently in the residual
    (`hasSum_logMass_residual`), with an error after `K` terms
    bounded by `W^{K+1}/(1−W)` in the weight alone, uniformly in the
    shift (`abs_logMass_sub_partialSum_le`). This is the
    sparse-dual, small-coupling regime; it controls small `α` and
    says nothing about `α → ∞`.

    That expansion is now read on coefficients
    (`Theaetetus.ClusterCoefficient`). A nontrivial character
    integrates to zero — translate the integral to a point where the
    character is not `1` (`integral_mFourier`) — so the characters are
    orthogonal under the coefficient functional
    (`mFourierCoeff_mFourier`), and a function given by an absolutely
    summable character series has exactly those coefficients
    (`HasCharSum`, `HasCharSum.mFourierCoeff_eq`). Multiplying two
    such series and regrouping by the sum of the indices gives the
    convolution (`convolve`, `HasCharSum.mul`), and iterating gives
    the convolution powers (`convPow`, `HasCharSum.pow`). The residual
    is such a series with its zero mode deleted (`modeCoeff`,
    `hasCharSum_residual`), so the coefficient of its `k`-th power is
    the `k`-fold convolution power — a sum over the decompositions
    `ν = ν₁ + ⋯ + ν_k` into nonzero modes.

    Applying the functional to the **finite** `K`-term truncation,
    where linearity is elementary, and bounding the remainder by the
    supremum norm of the uniform pointwise estimate
    (`norm_mFourierCoeff_le`) gives, at every nonzero frequency,

    ```
    ‖ℓ_ν − clusterPartial K ν‖ ≤ W^{K+1}/(1 − W)
    ```

    (`norm_logMassCoeff_sub_clusterPartial_le`) — with no interchange
    with the infinite logarithm series hidden inside. At second order
    this reads `ℓ_ν = w_ν − ½ Σ_μ w_μ w_{ν−μ} + O(W³)`
    (`norm_logMassCoeff_sub_second_order_le`). At `ν = e₁ + e₂`, the
    two ordered decompositions `(e₁, e₂)` and `(e₂, e₁)` contribute
    exactly `−w_{e₁}w_{e₂}` to the second-order cluster polynomial,
    explaining the term seen in the hexagonal reconnaissance. Proving
    that this contribution dominates the direct mode, the other
    decompositions, and the certified remainder remains the analytic
    nonvanishing problem.

    The remaining chain is therefore: the analytic nonvanishing
    theorem, kept separate; and the reduction of split forms to their
    blocks through the orthogonal-sum defect theorem
    (`orthSum_defect`, `orthSum_defect_eq_zero_iff`).

    The earlier CRT/alias transform closes a loop rather than
    opening a mechanism.
    The alias sums are not bare positive aggregates: up to one
    positive prefactor each is a shifted Gaussian mass of the
    *inverse* Gram at the reflected coupling
    (`massFourierCoeff_eq`, `aliasSum_eq_dual`), and the reflected
    coupling is exactly the one the criterion for `M⁻¹` at scale
    `π²/(a²b²s)` uses. So alias invariance is that dual criterion
    (`aliasSum_invariant_iff_dual`), and the criterion was already
    self-dual (`twoGridReflection_dual`, from
    `gramDefect_dual_coprime`). Positivity equates the alias sums
    across the involution and stops there; it has created no new
    strictness mechanism, and a proof of rigidity must break the
    symmetry the transform preserves. Once the
    rigidity theorem exists,
    `fieldDefect_div_gcd` reduces an arbitrary pair to its coprime
    base and turns the equivalence into the full equality
    classification. The target is specifically scalar dilations:
    the index-two diamond shows that arbitrary incomparable
    sublattices may saturate by orthogonal splitting
    (`defect_evenFst_evenSnd`), so the rigidity must use
    coprimality of the scalar pair, not merely incomparability.
    This is the route to Q1's equality classification that is
    independent of higher-rank Q5.

11. **The resolution metric** — done (`Theaetetus.ResolutionMetric`):
    Descent's join-kernel chamber geometry, instantiated through the
    same package boundary as target 7 with the normalized field
    `K(q) = −log Z(q²s)` (`resField`, whose defect is the negated
    field defect, `defect_resField`). The distance is that join
    kernel (`resDist`), in closed form (`resDist_eq`)

    ```
    d_s(q,q′) = log (Z(q²s)·Z(q′²s) / Z(lcm(q,q′)²s)²),
    ```

    a pseudometric on positive resolutions for every lattice action
    and every positive scale (`resPseudoMetricSpace`). The two
    halves have different scope, and the file says so. The triangle
    inequality is the correlation theorem: it needs the normalized
    field in the submodular chamber (`submodular_resField`, from
    `QuadLatticeAction.defect_nonpos`), which an arbitrary partition
    tower does not supply. Separation is generic: strict Boltzmann
    decay at one nonmodal sector makes the scaled partition function
    strictly decreasing above the base on any nontrivial tower
    (`PartitionTower.Z_lt_Z`), hence for a nontrivial lattice action
    at any positive scale (`QuadLatticeAction.scaledPartFn_lt`),
    hence the normalized field strictly monotone
    (`strictMono_resField`) and the distance zero only on the
    diagonal (`resDist_eq_zero_iff`) — so the resolution carrier is
    a metric space (`resMetricSpace`). Two facts say what the
    geometry means: on a comparable pair the join kernel is the cost
    gap itself (`resDist_of_le`), so a divisibility chain embeds in
    the real cost line; and at rank one and coprime `p,q` the
    pairing is a distance difference,
    `⟨p,q⟩_s = d_s(1,pq) − d_s(p,q)`
    (`pairing_eq_resDist_sub`), so a nontrivial incomparable pair
    sits strictly closer than its full span,
    `d_s(p,q) < d_s(1,pq)` (`resDist_lt_resDist_base`). This
    supplies the intrinsic metric
    geometry in which Q4's CND/Schoenberg question naturally lives.
    Completion and diameter claims remain outside the target until
    they are proved.

12. **The distributivity-index law** — done
    (`Theaetetus.SublatticeAsymptotics`), for finite-index subgroups
    of the standard integer lattice with its euclidean Gaussian.
    With `U = (A+B) ∩ C` and `V = (A∩C) + (B∩C)` the two ends of the
    distributivity-defect interval, the landing is

    ```
    D₃,s(A,B,C) → log [U : V]   as   s → 0⁺,
    ```

    the order-three defect at the boundary reading off the index
    of the interval the recurrence leaves behind. The proved `M₃`
    diamond of target 7 is its first nontrivial case: there
    `[U : V] = 2` (`relIndex_evenBoth_evenSum`) and the limit is
    `log 2` (`tendsto_defect3_diamond_index`). The route follows
    that proof: at the boundary every pairwise term vanishes by
    multiplicativity of covolume in the Gaussian mass, and
    `defect3_recurrence` leaves the mass gap from `V` to `U`,
    whose ratio tends to the index. First prove the Gaussian
    mass-ratio limit for a finite-index inclusion `V ≤ U`; then
    combine it with pairwise covolume cancellation and
    `defect3_recurrence`. The analytic layer of that first step has
    landed (`Theaetetus.GramAsymptotics`): the Boltzmann sum of a
    positive-definite Gram form saturates at large coupling
    (`tendsto_gramTheta_atTop`, the tower saturation applied to
    `gramTower`), the reflection carries that to the small-scale
    asymptotic

    ```
    (s/π)^(d/2)·gramTheta(M,s) → det(M)^(−1/2)   as s → 0⁺
    ```

    (`gramTheta_eq_dual`, `tendsto_gramTheta_nhdsGT_zero`), and the
    normalization cancels between two forms of the same rank, so
    their sums compare by the square root of the reciprocal
    determinant ratio — the ratio of covolumes
    (`tendsto_gramTheta_ratio`). The finite-index bridge has landed
    on top of it (`Theaetetus.FiniteIndex`): a `ℤ`-basis of a
    full-rank subgroup of the integer lattice gives a chart whose
    determinant is the index up to sign (`natAbs_det_subChart`),
    hence a positive-definite pulled-back Gram form
    (`subGram_posDef`) of squared-index determinant
    (`det_subGram`), through which the intrinsic mass is a Gram
    Boltzmann sum (`subMass_eq_gramTheta`). For a full-rank
    finite-index inclusion `V ≤ U` the normalization cancels:

    ```
    ρ_s(U)/ρ_s(V) → [U:V],
    log ρ_s(U) − log ρ_s(V) → log [U:V]   as s → 0⁺
    ```

    (`tendsto_subMass_ratio`, `tendsto_log_subMass_sub`) — the field
    gap `defect3_recurrence` consumes, with full rank and finite
    index carried as explicit hypotheses. The pairwise half has
    landed too (`Theaetetus.SublatticeAsymptotics`): the
    logarithmic mass is a context field on the subgroups
    (`subField`), and at the boundary its pairwise defect vanishes
    (`tendsto_defect_subField`) — the inclusions `A ≤ A+B` and
    `A∩B ≤ B` contribute the indices `[A+B : A]` and `[B : A∩B]`,
    which the second isomorphism theorem equates, so covolume is
    multiplicative across meet and join and the boundary field loses
    its pairwise curvature.

    The two halves compose in one rewrite of `defect3_recurrence`:
    its three pairwise defects go to zero, its field gap goes to the
    logarithm of the interval's index, and

    ```
    D₃,s(A,B,C) → log [(A+B)∩C : (A∩C)+(B∩C)]
    ```

    (`tendsto_defect3_subField`, over `distribUpper`,
    `distribLower`, `distribLower_le_upper`). The statement's only
    inputs are the three subgroups and their nonzero indices; the
    charts are internal (`subBasis`, from
    `Int.addSubgroup_index_ne_zero_iff`) and the chart-level
    theorems remain as implementation API. The reading is plain: the
    Gaussian field becomes pairwise modular at the boundary, but
    non-distributivity leaves a finite interval, and the entire
    surviving third-order interaction is the logarithm of that
    interval's index. What is *not* claimed: the same law over an
    arbitrary positive-definite ambient form, or across rank loss or
    infinite index.

13. **Coset duality and the classwise sign** — done
    (`Theaetetus.CosetDuality`, `Theaetetus.CosetSign`). The shifted
    mass reflects onto the character-twisted dual Boltzmann sum
    (`gramMass_dual`), so the shifted and classwise defects reflect
    shift for shift and class by class (`shiftDefect_dual`,
    `cosetDefect_dual`); the odd class of `ℤ ⧸ 2ℤ` has positive
    defect at `s = 1`, `(2, 3)` (`cosetDefect_odd_pos`). In adelic
    terms `cosetMass` is the `S = {∞, 2}` local θ-function of a
    Gaussian times a residue indicator, `twistTheta` its character
    twist, and `cosetDefect_dual` the Tate functional equation
    `f ↦ f̂` read through the logarithmic cross-ratio.

14. **Coset separation, rank four** — done
    (`Theaetetus.CosetSeparation`): class pairs are an isometry
    invariant (`classPairs_ncard_eq_of_isometry`) and separate
    Schiemann's pair, `10` against `18` at energy `12`
    (`schiemann_not_isometric`). Not formalized: equality of the
    pair's theta series (a level-1729 weight-2 modular-form
    computation).

15. **Class moments are Siegel data** — landed at `k = 2`
    (`Theaetetus.SiegelDegree`): class pairs at energy `m` are the
    disjoint union over `t ≠ 0` of the representation sets of
    `!![m, −t; −t, t]` (`classPairsEquivSigma`), so equal
    degree-two representation numbers force equal class-pair counts
    (`classPairs_ncard_eq_of_siegelSet`) and Schiemann's pair has
    distinct degree-two representation numbers
    (`schiemann_siegelSet_ne`). General `k` has landed too
    (`Theaetetus.SiegelTuples`): class tuples are a Gram predicate
    in first-sector and half-difference coordinates
    (`classTuplesEquivPred`), sorted by Gram matrix
    (`gramFiberEquiv`), so equal representation numbers in degree
    `k + 1` give equivalent class tuples
    (`classTuplesEquivOfSiegel`); with the frame bounds, `E8 ⊕ E8`
    and `D16⁺` differ in degree 17 (`e8sq_d16plus_siegel_ne`). The
    known separation is in degree 4; reaching it needs the
    fourth class moments themselves, not only the frame maxima.
    The original plan: ordered `k`-tuples of
    distinct sectors of energy `m` in one class mod `2` biject with
    `k`-tuples `(x, y₂, …, y_k)` whose Gram matrix lies in an
    explicit set (`Q(x) = m`, `⟨x, yᵢ⟩ = −Q(yᵢ)`, `yᵢ ≠ 0`,
    `yᵢ ≠ yⱼ` — all Gram conditions under positive definiteness),
    so the `k`-th falling moment of the class counts is a sum of
    degree-`k` representation numbers. Landing first at `k = 2`,
    where it makes `schiemann_not_isometric` a statement about
    degree-two theta series: some binary Gram matrix is represented
    a different number of times by the pair.

16. **The frame separation of `E8 ⊕ E8` and `D16⁺`** — done
    (`Theaetetus.FrameSeparation`): in an even positive form,
    energy-four sectors of one class are equal, opposite or
    orthogonal (`pairing_of_congr_four`), so a class holds at most
    `2n` of them (`frame_card_le`, by linear independence over `ℚ`);
    on `E8 ⊕ E8` the block split sharpens this to `16`
    (`e8sq_class_card_le`), `D16⁺` has the 32-sector class `±2eᵢ`
    (`d16plus_frame`), and no integral isometry joins them
    (`e8sq_not_isometric_d16plus`). The original plan: one class of
    `D16⁺ ⧸ 2D16⁺` holds the 32 vectors `±2eᵢ`; no class of
    `E8² ⧸ 2E8²` holds more than 16. A structural proof avoids the
    61920-vector enumeration: in an even unimodular lattice, norm-4
    vectors congruent mod `2` are equal up to sign or orthogonal,
    so a class is a frame, and the frames of `E8` have 8 pairs.

17. **The degree-four separation law.** Summed over classes, the
    classwise defect of a theta-equivalent pair with equal
    moments through order three separates at fourth order in the
    twisted masses: `ΔΣ_c D_c ~ (|L/2L|/4)·ΔN₄·e^{−8t}`
    (numerically to `3·10⁻⁵` on `E8²`, `D16⁺`). The statement needs
    only the cluster expansion of `log twistTheta` and the moment
    identities; the pair-specific input is `ΔN₄`.

Reconnaissance, falsify-first:

1. **Higher-rank Q5.** Normalize every Gram matrix to determinant
   one before profiling: the repo's hexagonal form
   `(a² − ab + b²)/3` has determinant `1/12` with `M⁻¹ ≅ 12M`, so
   it is self-similar under duality with reflection center
   `β* = π·√12`, not `π` — the `√12`-rescaling is the genuinely
   isodual normalization. Test dual pairs together on the
   half-profile `u ≥ log π` only: the reflection makes
   `[π, ∞) × {L, L*}` a complete search domain
   (`gramCurvature_pos_of_ge_pi`). Sweep whole
   half-profiles, never the center alone — an isodual profile
   constrains a failure window to be symmetric, not absent. Start
   at the normalized hexagonal form, then the binary shear family
   toward degeneracy; record `λ₁(L)·λ₁(L*)` per form as a
   candidate degeneration coordinate. First runs committed (`recon/data`:
   baselines, the unit-circle arc, the shear ray with its fine
   scan; findings in `recon/README.md`). Ternary runs committed
   as well — rank-3 baselines, the cubic→FCC path, the FCC
   squash family with two fine scans; under genuine dual
   asymmetry the sampled minimum leaves the duality center.
   Next: apply the certification chain (target 5) to the
   deep-degeneration margins.

2. **Q4 phase geometry** — first uncertified sweep complete
   (`recon/q4.py`; `q4_sweep_*.json`, `q4_witness.json`;
   findings in `recon/README.md`): correctly-oriented extremal
   eigenvalues, one detected sign change per statistic per
   sampled grid with brackets bisected, and the historically
   cited transitions and `s = 0.12` witness reproduced from
   committed code. Next: apply the crossing algebra (target 5) to
   certify the entry intervals and brackets, further intervality
   falsification, and the star-obstruction rate against its
   `s_PSD ~ (1/6)·log n` benchmark.

3. **Two-grid rigidity** — first campaign complete
   (`recon/rigidity.py`, deterministic record in
   `rigidity_two_grid.json`, wired into `nu tasks.nu recon`;
   findings in `recon/README.md`). Sampled: pairs `(3,2)` and
   `(5,2)`, ranks 2–3, named symmetric forms, diagonal ratios,
   shears, degenerations, scales `s/s* ∈ {1,4,16,32,64}` on the
   profiled forms, all in the half-domain `s ≥ s*` whose convention
   is checked at the sampled scale for every form (28 checks, each
   enclosing zero within `4e−24`). Every slack in the record carries
   a **certified positive sign** — exact rational forms, a certified
   `λ_min`, shifts canonicalized into `[−1/2,1/2]^d`, an infinite
   geometric tail majorant, and, replacing every floating-point
   step, rigorous Arb ball arithmetic from π through the
   logarithms, with precision escalating until each claimed sign is
   decided. Findings, scoped to those samples: no counterexample;
   orthogonal sums add exactly; **the symmetry profiles cross** —
   at the self-dual scale the denser member of each pair carries the
   larger slack (`hexagonal − square2 = +0.0198909`,
   `fcc − cubic3 = +0.0434768`), but by `4s*` both signs reverse
   (`−0.00940326`, `−0.0202102`), all four certified as differences
   of balls, so symmetry strengthens the obstruction at the centre
   and weakens it into the large-scale chamber rather than acting
   uniformly; the only sampled route toward zero is the scale
   boundary, the rank-two degeneration being that same route (an
   orthogonal sum at reciprocal scales); and along the `square2`
   profile the observed ratio `residual/√slack` is `0.5` to five
   digits, consistent with a quadratic Cauchy–Schwarz gap, though
   the `hexagonal` profile has not stabilized over the sampled
   range. Separately, an exact but **unformalized** argument
   **closes the one structural mechanism outright**: if an integral
   isometry `S` of finite order induces the CRT dilation, Minkowski's
   lemma gives `S² = I`, so `P = (I − S)/2` is an integral idempotent
   divisible by `b > 1`; infinite divisibility forces `P = 0` and
   `S = I`, which contradicts `S ≡ −I (mod a)` in positive rank since
   odd `a > 1` cannot divide `2`. No such isometry exists in **any**
   positive rank. Next: the remaining possibility is an accidental
   equality of Gaussian mass values with no isometry inducing it, so
   the question is analytic rather than structural.

4. **Log-mass Fourier certificate** — falsification gate complete
   (`recon/logfourier.py`, deterministic record in
   `log_fourier.json`, wired into `nu tasks.nu recon`; findings in
   `recon/README.md`). **Not certified**: high-precision floating
   point with a spectral quadrature whose aliasing is estimated by
   grid doubling, not bounded. The gate probes the finite family
   `{e_i} ∪ {e_i + e_j : i < j}` of Fourier coefficients of
   `log gramMass`, whose nonvanishing implies `EvenPartSeparating`
   and hence coprime rigidity. Anchored by the exact `q/(1−q²)` from
   the Jacobi triple product at rank one, by exact references for
   every diagonal form and every unimodular rechart of one, and by an
   independent Poisson evaluation of the mass agreeing to `1.6e−30`
   at one probe point per row. Each form also carries an exact
   orthogonal-decomposability audit, exhaustive for rank at most
   three. The certificate was not falsified: against that audit, the
   32 rows resolving nonzero at every frequency are exactly those on
   indecomposable forms and the 20 with an unresolved frequency
   exactly those on decomposable ones, no resolved coefficient
   changes sign across the coupling grid, and the two probes
   `[[1,ε],[ε,1]]` are positive and smaller at the smaller `ε`. Both
   which frequency fails and the signs are chart dependent — the
   square lattice loses `(1,1)` in the standard chart and `(1,0)` in
   the `t = 1` shear chart, each at the frequency the rechart
   predicts — while nonvanishing survives every rechart sampled. The
   split against decomposability is an observation on the sample, not
   a proved equivalence. Next: the Lean torus Fourier layer, with
   analytic nonvanishing kept separate.

Open: the equality chain (target 10), complete through the
intrinsic two-grid criterion and awaiting only the rigidity theorem
that the criterion is impossible for coprime `a, b > 1`. The
verdicts to date: Q5 stays a universal conjecture, with margins
vanishing toward every degenerate boundary probed and its binding
point leaving the duality center under dual asymmetry; Q4's
uniform-PSD question is resolved negatively by the star
obstruction, leaving the rate and intervality open.
