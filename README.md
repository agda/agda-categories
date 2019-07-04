# categories-agda library

Welcome to what will hopefully become the standard Category Theory library for Agda.

## Origins

This library is a rewrite of [copiumpin's version](https://github.com/copumpkin/categories)
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
the classical definition is ``sloppy'', omitting some coherence natural isomorphisms that
are expanded away in the proof-irrelevant case, but must be inserted here. Along with
proof relevance, it also makes sense to develop under the conditions of *--without-K* and
*--safe*.

A second aim is to make this library 'ready' to be, in whole or in part, incorporated into
the main standard library. Thus that means removing many custom-made parts written for
Setoid-based reasoning from the previous version, amongst others, and instead rely on the
standard library as much as possible. Also, the style should be adapted to use that of the
standard library.

Another clear design decision, already present in the original, is to internalize to each
category a version of Hom-equality.  In practice what this means is that the work here is
closer in flavour to bicategory-theory than to classical category theory.

Some of the lower-level design decisions (naming conventions, organization) are (will be) 
documented in the proto-contributor's guide.

### Places to find more design notes
- [Category.Discrete](Categories/Category/Discrete.agda)

## Contributing

We welcome contributions! Please submit PRs, issues, etc. A full-fledged contributor's guide
will be written, eventually.

### Naming Conventions

(Some conventions are slowly arising, document them)
- Many definitions (like that of Category) are in Category.Core, to avoid various kinds
  of import loops, and re-exported. .Core modules should only be imported if doing otherwise
  causes an import cycle.

### Organization

(where to find what)

