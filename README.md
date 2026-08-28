# The Candle Interactive Theorem Prover

This repository contains the Candle theorem prover sources. The repository is a
fork of John Harrison's HOL Light sources (based on the commit
e960dd0f636c36d48f79664c7cf11a59ba6f66a3), which are available in the repository
here: [https://github.com/jrh13/hol-light](https://github.com/jrh13/hol-light).
The original README of this repository can be found [here](README.hol-light).

This repository differs from the original HOL Light repository in that some
files have been patched to work with the Candle theorem prover. It also contains
some custom ML source files required to run Candle (these carry the prefix
candle_ in their filenames). The patches are stored under
[candle_patches/](candle_patches/).

- The CakeML project homepage: [www.cakeml.org](www.cakeml.org)
- The Candle homepage:         [www.cakeml.org/candle](www.cakeml.org/candle)

# Features

- Candle is a verified implementation of HOL Light, and comes with a mechanized
  end-to-end soundness result which encompasses the entire theorem proving system.
  Read our ITP'22 paper on Candle for more information: [Candle: A Verified Implementation of HOL Light](https://drops.dagstuhl.de/opus/volltexte/2022/16712/pdf/LIPIcs-ITP-2022-3.pdf).
- Candle comes with a fast in-logic computation primitive: see
  [candle_compute.ml](candle_compute.ml) and
  [compute_examples.ml](compute_examples.ml) for examples.

# Requirements and Authenticated Installation

Candle requires an x86_64 Linux machine, a C compiler, make, and the exact
CakeML and HOL4 revisions pinned by `candle/flyspeck_manifest.json`.  A usable
authenticated launcher also requires a successful pinned CakeML `cake.S`
bootstrap record.  The complete commands and fail-closed acceptance conditions
are documented in
[candle/compatibility/dopen_direct_acceptance.md](candle/compatibility/dopen_direct_acceptance.md).
In outline, record the completed bootstrap and then link it locally with:

    $ /usr/bin/python3 -I candle/cakeml_artifact_provenance.py record-bootstrap ...
    $ CANDLE_BUILD_JOBS=2 ./build-local-cakeml.sh CAKEML_ROOT BOOTSTRAP_RECORD.json
    $ ./candle.sh

`candle.sh` authenticates the clean Candle revision, manifest pins, linked
compiler, runtime inputs, root aliases, bootstrap record, and exact host ELF
closure before every session. Then load the HOL Light sources by writing:

    #use "hol.ml";;

into the REPL.

The historical [build-instructions.sh](build-instructions.sh) download flow is
retained only as an upstream development reference.  It does not create the
bootstrap and linked-provenance records required by `candle.sh`, and therefore
must not be used to produce a promotable Flyspeck-checking artifact.

# Compatibility and Porting

Candle supports much (but not all) of the HOL Light 'base' theories and scripts.
See [hol.ml](hol.ml) for a list of the files that are loaded by Candle. Notable
omissions are:

- the help system
- the theorem database
- metis and compute

Most proof scripts that contain tactic proofs will be accepted by Candle with no
changes. However, because Candle runs on CakeML (not OCaml), there are some
things that Candle does differently, notably:

- CakeML does not support let-polymorphism.
- There is no polymorphic comparison (Pervasives.compare). However, most types
  can be compared for equality using the standard operator (=). Other uses
  require changing your code to use type-specific comparison functions. See e.g.
  setify in lib.ml.
- Pointer equality does not work. There is a stub for (==) in Candle that always
  evaluates to false.
- Expression-level modules and functors are not supported, nor is the 'open'
  declaration.
