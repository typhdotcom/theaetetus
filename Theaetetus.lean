-- The scalar layer: the analytic primitive and θ
import Theaetetus.SectorAction
import Theaetetus.Theta

-- The Gibbs bridge: termwise derivatives of the primitive
import Theaetetus.Gibbs

-- The functional equation: the reflection law differentiated
import Theaetetus.FunctionalEquation

-- The fluctuation inequality: Fact 1 at large coupling
import Theaetetus.Fluctuation

-- The refined log-convexity: the strict rectangle inequality at rank one
import Theaetetus.LogConvexity

-- The field defect and the annihilation of affine log weights
import Theaetetus.FieldDefect

-- The rank-one defect on the divisibility lattice, and its witness
import Theaetetus.Defect
import Theaetetus.Witness

-- The reflection law: duality as a weight-zero symmetry of the defect
import Theaetetus.Duality

-- The sign at (2, 3), all scales: the birth certificate
import Theaetetus.Sign

-- The sign closed at rank one: strict submodularity at every incomparable pair
import Theaetetus.Submodular

-- The coarse midpoint inequality: the sign's b → a limit
import Theaetetus.Midpoint

-- The sign for diagonal forms, every rank: orthogonal sums add defects
import Theaetetus.Diagonal

-- The strict rectangle inequality for diagonal forms: curvature is inherited
import Theaetetus.DiagonalCurvature

-- The defect as conditional association of divisibility events
import Theaetetus.Factorization

-- The prime pairing, its bounds, and saturation at the base
import Theaetetus.Pairing

-- The kernel interface: quadratic forms on finite prime sets
import Theaetetus.Kernel

-- The deep-scale limit: the normalized pairing asymptotic
import Theaetetus.LargeScale

-- The large-scale chamber: saturation flattens the kernel
import Theaetetus.Flattening

-- The small-scale chamber: no three primes stay CND
import Theaetetus.SmallScale

-- The star obstruction: no uniform deficit-PSD threshold
import Theaetetus.StarObstruction

-- Residue complexity as a polymatroid-like rank function
import Theaetetus.RankFunction

-- The graph substrate, the theta instance, and the ℤ-homology spine
import Theaetetus.IncidenceGraph
import Theaetetus.ThetaGraph
import Theaetetus.GraphHomology

-- The matrix quadratic layer and the Gaussian periodization bound
import Theaetetus.QuadraticAction
import Theaetetus.Periodization

-- Certified coercivity: the least Gram eigenvalue and the dominance certificate
import Theaetetus.Certification

-- Certified Boltzmann tails: the box truncation error, dominated
import Theaetetus.Tails

-- Certified shell counts: energy sublevels confined to boxes
import Theaetetus.Shells

-- Higher-rank defect duality: reflection through the dual Gram
import Theaetetus.GramDuality

-- The shifted Gaussian mass and its lattice decompositions
import Theaetetus.ShiftedMass

-- Fiber products and Boltzmann coarse-graining
import Theaetetus.Pullback
import Theaetetus.CoarseGrain

-- The priced carrier: Gram data, lattice actions, periods, the class action
import Theaetetus.GramData
import Theaetetus.LatticeAction
import Theaetetus.Periods
import Theaetetus.Carrier

-- Concrete carriers: the cycle and theta lattice bases
import Theaetetus.GraphInstances

-- The residue tower: reductions, residue actions, tower maps
import Theaetetus.Tower

-- The defect on the tower: the cross-ratio law, CRT, the C₃ bridge
import Theaetetus.CrossRatio

-- The abstract partition tower: the interface behind the classification
import Theaetetus.PartitionTower

-- Spectral peeling: the least energy and its multiplicity from the samples
import Theaetetus.Peeling

-- The zero-defect classification: lattices, carriers, and C₃'s kernel
import Theaetetus.Classification

-- Intrinsic defect duality: the lattice and its dual
import Theaetetus.LatticeDuality

-- Higher-rank curvature: the mean-energy and curvature reflections
import Theaetetus.GramCurvature

-- Positive correlation and the sign of the defect
import Theaetetus.Correlation

-- The equality cases of the correlation inequalities
import Theaetetus.CorrelationEquality

-- The Fourier form of the two-grid reflection criterion
import Theaetetus.ReflectionFourier

-- The strict maximum of the shifted Gaussian mass, and its reach on
-- the two-grid criterion
import Theaetetus.MassMaximum

-- Separation of the parity feature vectors: conditional coprime
-- rigidity, and its failure on decomposable forms
import Theaetetus.ParitySeparation

-- The real Gaussian core: separation reduced to the even part of the
-- logarithmic mass
import Theaetetus.EvenPartSeparation

-- The torus Fourier coefficients of the logarithmic mass, and the
-- finite frequency certificate
import Theaetetus.LogMassFourier

-- The cluster normalization of the logarithmic mass, and its
-- truncation estimate in the sparse-dual regime
import Theaetetus.ClusterExpansion

-- The cluster expansion read on Fourier coefficients: convolution
-- powers and the finite cluster approximation
import Theaetetus.ClusterCoefficient

-- The resolution metric: the join kernel of the normalized field
import Theaetetus.ResolutionMetric

-- The pairing as a sampled defect matrix: the chambers in Descent's
-- definiteness vocabulary, and the base point that forbids CND
import Theaetetus.DefinitenessBridge

-- The scale asymptotics of a Gram Boltzmann sum
import Theaetetus.GramAsymptotics

-- The Gaussian mass ratio at a finite-index inclusion
import Theaetetus.FiniteIndex

-- The pairwise boundary of the sublattice field
import Theaetetus.SublatticeAsymptotics

-- The orthogonal sum: partition functions multiply, defects add
import Theaetetus.OrthogonalSum

-- The arithmetic realization of the abstract defect calculus, and
-- the coprime telescope of its corrected orders
import Theaetetus.HigherInteraction

-- The Gaussian diamond: irreducible order-three interaction on the
-- non-distributive carrier of sublattices of ℤ²
import Theaetetus.SublatticeDiamond

-- Scalar bounds and the rank-two witness on the theta graph
import Theaetetus.ThetaBounds
import Theaetetus.RankTwo

-- Coset duality: the shifted and classwise defects reflect onto the
-- character-twisted dual Boltzmann sums
import Theaetetus.CosetDuality

-- The classwise defect has no sign: the odd class of ℤ/2ℤ
import Theaetetus.CosetSign

-- Coset separation: the mod-2 residue datum separates a theta-equivalent
-- quaternary pair, and class pairs are an isometry invariant
import Theaetetus.CosetSeparation

-- Class pairs are degree-two Siegel data
import Theaetetus.SiegelDegree

-- Frames: energy-four classes of even lattices, and the separation of
-- E8 ⊕ E8 from D16⁺
import Theaetetus.FrameSeparation

-- Class tuples are Siegel data in every degree; degree 17 separates
-- E8 ⊕ E8 from D16⁺
import Theaetetus.SiegelTuples

-- The manifest: public statements restated as compiler-checked examples
import Theaetetus.Status
