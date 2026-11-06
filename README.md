# Malfunction for OxCaml

This repository ports [Malfunction](https://github.com/stedolan/malfunction)
0.7.1 to the [OxCaml](https://oxcaml.org) compiler. Peregrine's benchmarks use
it to compile Peregrine's Malfunction output with OxCaml's flambda2 backend.
The upstream README follows below the line.

The first commit holds the pristine 0.7.1 sources
(`opam source malfunction.0.7.1`). The second holds the port.

## Compiler

The port builds against one OxCaml revision only, because Malfunction uses
the compiler's internal `Lambda` API, which OxCaml changes often:

- compiler `ocaml-variants.5.2.0+ox`
- from the OxCaml opam repository at commit `f1bd228dda31430bf6271f0f9adb2e604c6957ca`:
  `git+https://github.com/oxcaml/opam-repository.git#f1bd228dda31430bf6271f0f9adb2e604c6957ca`

The port does not build with upstream OCaml; use Malfunction 0.7.1 from
opam for that.

## Build

    opam repo add oxcaml-f1bd228 'git+https://github.com/oxcaml/opam-repository.git#f1bd228dda31430bf6271f0f9adb2e604c6957ca' --dont-select
    opam switch create malfunction-oxcaml --repos=oxcaml-f1bd228,default --packages=ocaml-variants.5.2.0+ox
    opam install --switch=malfunction-oxcaml dune ocamlfind zarith
    opam exec --switch=malfunction-oxcaml -- dune build @install
    # or: opam pin add --switch=malfunction-oxcaml malfunction .

The compiler build takes about 45 minutes.

Use the switch's `malfunction cmx -O2 prog.mlf`, then link the `.cmx`
with that switch's `ocamlfind ocamlopt -package zarith`.

## What changed

All of the port lives in `src/`:

- `malfunction_compat.ml` replaces the cppo layer `malfunction_compat.cppo.ml`
  and is written against OxCaml's `Lambda`, so the build no longer needs
  cppo.
- `malfunction_compiler.ml` is adapted to the OxCaml `Lambda` API:
  - `Llet` and `Lswitch` take layouts.
  - `lfunction` takes `lparam` records plus `~mode ~ret_mode`.
  - `Lletrec` binds functions only.
  - The integer and float primitives are `Pscalar`.
  - `Pfield` takes `Reads_vary`.
- The native driver runs Slambda, then `Simplif`, then
  `Flambda2.lambda_to_cmm`.
- `-O2` installs `Oxcaml_flags.opt_flag_handler` through
  `Clflags.Opt_flag_handler.set`. Without the handler, `-O2` silently does
  nothing.
- `src/dune` drops the cppo rule and builds Malfunction itself with warnings
  37 and 58 off and not fatal. When compiling a program, warning 55
  (inlining impossible) is off as well: flambda2 raises it for every
  `[@inline]` external in Zarith.

## Not ported

- `malfunction cmo` (bytecode output) raises an error.
- `compile_and_load` (used by library clients to load compiled code
  in-process) raises an error.
- The REPL (`malfunction eval`) uses the interpreter and should still work,
  but it is untested.
- The test suite (`dune runtest`, which needs `omd`) has not been run on
  OxCaml.

---

**Malfunction** is a high-performance, low-level untyped program
representation, designed as a target for compilers of functional
programming languages.

**Malfunction** is a revolting hack, exposing bits of the OCaml
compiler's guts that were never meant to see the light of day.

"Hello, World" looks like this:

    (module
      (_ (apply (global $Stdlib $print_string) "Hello, world!\n"))
      (export))

Malfunction requires OCaml (at least version 4.04.0, and you may see
better performance with flambda enabled), which you should install
using [OPAM](https://opam.ocaml.org). Then, install malfunction using:

    opam pin add malfunction git://github.com/stedolan/malfunction.git

You can then compile and run the above example with:

    malfunction compile docs/helloworld.mlf -o hello
    ./hello

The syntax is based on s-expressions, and is designed to be easy to
correctly generate, rather than to be particularly beautiful. For
instance, there are no reserved words: all user-defined identifiers
must be prefixed with `$`.

Files are compiled as OCaml modules, and may import values from OCaml
(e.g. `Stdlib.print_string` in the example above) and export
values to OCaml (using the `export` form). Modules written in
malfunction may be combined with an `mli` file written in OCaml.

Malfunction makes no effort to check types. Typical programs do go
wrong. Compilers targeting Malfunction need to convince themselves
that their output won't go wrong, but don't need to explain
their reasoning.

For more, read the [spec](./docs/spec.md), or the
[abstract submitted to the ML Workshop](https://stedolan.net/talks/2016/malfunction/malfunction.pdf),
or [some examples](./docs)

There's also an
[experimental backend](https://github.com/stedolan/idris-malfunction)
for the dependently typed language [Idris](http://idris-lang.org).
