# Formal Methods - Agda Exercises

This repository contains exercises for the **Formal Methods** course, exploring constructive type theory and functional verification using [Agda](https://wiki.portal.chalmers.se/agda/).

The material builds progressively from the foundations of typed $\lambda$-calculus and Church encodings to inductive data types and recursion schemes.

## Repository Contents

- **`Test.agda`**: Initial warmup definitions; defining basic types such as `Bool` from scratch and fundamental logical connectives (`not`, `and`, `or`, `xor`).
- **`BasicFun.agda`**: Functional foundations and simply typed $\lambda$-calculus:
  - Identity, function composition, and $S$ and $K$ combinators.
  - Church encodings over a type parameter (Church numerals, Church booleans, and Church pairs with operations).
- **`BasicInd.agda`**: Inductive data types and structural recursion:
  - Custom data definitions: `Bool`, `Nat`, `List A`, and rose trees `Tree A`.
  - Arithmetic and comparison functions (`+`, `*`, `_?≤_`, `even?`).
  - List processing algorithms (insertion sort `isort`, `fmap`, `fold`, monadic operations).
  - Multi-way tree traversals (`tfmap`).
- **`SimpleTypes.agda`**: Formalization of simple types:
  - Basic syntax and typing rules.
  - Associated properties.
- **`IPL.agda`**: Intuitionistic Propositional Logic (IPL):
  - Definitions of logical connectives.
  - Inference rules of the deductive system.

## Requirements & Usage

You need an installation of Agda (version 2.6+ recommended):

```bash
agda src/Test.agda
agda src/BasicFun.agda
agda src/BasicInd.agda
agda src/SimpleTypes.agda
agda src/IPL.agda
```

## License

This project is licensed under the [MIT License](LICENSE).
