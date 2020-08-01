# agda-categories library

Welcome to what will hopefully become the standard Category Theory library for Agda.

The current library release, v0.1.2, works with Agda-2.6.1 and stdlib-1.3.  The master
branch should also work with same, but may contain various incompatibilities.

Note that this should be considered pre-beta software, and that backwards compability
is not assured (although we don't intend to break things whimsically).

## Origins

This library is a rewrite of [copumpin's version](https://github.com/copumpkin/categories)
of a previous library, which worked very well up to Agda 2.4.3 or so, but began bit-rotting and
was completely broken by 2.6 (with various stages of 'functioning' in between). That library
itself has older origins, which are well documented in that project's own documentation.

## Design

One of the main reasons that the old library started bit-rotting was that it used
*proof-irrelevance* quite extensively. And that this feature started misbehaving in later
versions of Agda (it does not seem to be used much in the standard library, so gets less
testing). And the desire to see how far one could go in Category Theory while being
*proof relevant*. This proof relevance does not have a large effect, at least not until some
definitions that use natural transformation-based identities (like that for Monad); here
the classical definition is "sloppy", omitting some coherence natural isomorphisms that
are expanded away in the proof-irrelevant case, but must be inserted here. Along with
proof relevance, it also makes sense to develop under the conditions of *--without-K* and
*--safe*.  And to stay away from strict category theory -- being Setoid-enriched doesn't
play well with that at all.

A second aim is to make this library 'ready' to be, in whole or in part, incorporated into
the main standard library. Thus that means removing many custom-made parts written for
Setoid-based reasoning from the previous version, amongst others, and instead rely on the
standard library as much as possible. Also, the style should be adapted to use that of the
standard library.

Another clear design decision, already present in the original, is to internalize to each
category a version of Hom-equality, i.e. as mentioned above, to be
Setoid-enriched.  In practice what this means is that here and there, the flavour is that
of bicategory theory instead of category theory.

All non-trivial proofs are done in equational style. One-liner proofs are not; some very
short proofs (obvious 2- or 3-steps) are done combinator-style. Very large proofs with
trivial sequences of steps "in the middle" have those done combinator-style too.

Some of the lower-level design decisions (naming conventions, organization) are (will be) 
documented in the proto-contributor's guide.

### Places to find more design notes
- [Category.Discrete](Categories/Category/Discrete.agda)
- [Category.Monoidal](Categories/Category/Monoidal.agda)
- (all the stuff about Mates)
- (bicategory is defined as Enriched over (Monoidal) Cats instead of 'by hand')
- (definition of Pseudofunctor is in Benabou style rather than 'by hand')
- (closed) Issue 5 in the github repository contains more discussion.
- The library relies on eta expansion of records. However, due to a bug in Agda
  2.6.0.1, we need to switch this on in related records. In the next release of Agda,
  hopefully we can remove these switches. See also [this agda
  issue](https://github.com/agda/agda/issues/4142).
- We add `sym-assoc` and `identity²` in order to achieve better definitional equality
  of `Category`. The rationale can be found in [this
  paper](https://arxiv.org/pdf/1401.7694.pdf). 
- We also add other "redundant" axioms into other definitions so that we achieve a better
  definitional equality property for definitions with opposites.
- Use (private) modules instead of local renaming to resolve name clashes that
  would occur with opening the same module twice, such as when working with
  two categories, two functors, etc.

### Smaller Design decisions
- Do not make implicit fields that can rarely be inferred (like what had been done in
  Category and Functor)
- Do not use Heterogeneous equality at all. Really, never ever.
- Minimize all use of propositional equality. Try to make things Setoid-enriched instead
  of Set-enriched.

## Contributing

We welcome contributions! Please submit PRs, issues, etc. A full-fledged contributor's guide
will be written, eventually.

### Organization

Right now, one can browse [everything](https://agda.github.io/agda-categories/) in 
nicely highlighted HTML. The basic layout:
- All code that shouldn't (eventually) be in stdlib is under Categories.
- If something is some kind of Category, it should be under Category/
- Instances, i.e. if you say "X is a category", or "X is a functor", go under Instances/
- Constructions, i.e. if you say "given W then we can build a Category" (or Functor, etc)
  got under Constructions/
- Properties that follow from a definition or concept X go under X.Properties
- The important concepts of Category Theory have their own directories:
  - Adjoint
  - Object
  - Morphism
  - Diagram
  - Functor
  - Kan
  - Yoneda
- There are sub-directories for:
  - Enriched Categories
  - Minus2 Categories
  - Minus1 Categories
  - Bicategories
  - Bifunctors
- To be precise, a lot of the usual definitions about categories are under that
  directory, namely:
  - Complete, Cocomplete
  - Close, Cartesian, CartesianClosed
  - Discrete, Finite
  - Monoidal (it has its own rich hierarchy as well)
  - Product
  - Slice
  - Topos
  - WithFamilies

### Naming Conventions

(Some conventions are slowly arising, document them)
- Some definitions (like that of Category) are in Category.Core, to avoid various kinds
  of import loops, and re-exported. .Core modules should only be imported if doing otherwise
  causes an import cycle.
- Various 'examples' of categories used to be scattered about; these are now gathered
  together in Category.Instance. More generally, Function.Instance, etc.
- Various *constructions* of categories (like the Arrow category of a category) are in
  Category.Construction. And more generally, Functor.Construction, etc.
- The basic rule of thumb is that constructions are parametrized over some input in a
  non-trivial way, whereas instances are not parametrics (like the (large) Category of
  (small) Categories, the Category of Types and functions, the Category of Setoids, etc.
- Named modules are often used when multiple structures are in concurrent use; for example,
  if the 'components' of two categories (say A and B) are used in the same context, then
  (private) modules A and B are defined for easier access.
- Components of larger structures use long English names instead of the more usual
  Categorical 1-Greek-letter short-hands.  So unitor<sup>l</sup> rather than
  &lambda; and associator rather than &alpha;.

