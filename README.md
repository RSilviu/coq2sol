# coq2sol

This repository aims to provide formal semantics for a subset of Solidity smart contracts language.

## Requirements

- [Coq](https://coq.inria.fr/), see the [official installation instructions](https://github.com/coq/coq/wiki#coq-installation)
- CoqIde or [ProofGeneral](https://proofgeneral.github.io/) as a front-end of Coq.
CoqIde is usually installed along with Coq, for further configuring CoqIde refer to [Configuration of CoqIDE](https://github.com/coq/coq/wiki/Configuration%20of%20CoqIDE).

Then build the .v files in the [`main/`](main) directory using

```shell
make
```

and the setup is completed.
