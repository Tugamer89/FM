# Formal Methods - Agda Exercises

This repository contains exercises for the **Formal Methods** course, exploring constructive type theory and functional verification using [Agda](https://wiki.portal.chalmers.se/agda/).

The material builds progressively from the foundations of typed $\lambda$-calculus and Church encodings to inductive data types and recursion schemes.

## Repository Contents

The following files provide auxiliary definitions needed by other files. They do not contain any exercise,  but it is useful to have a look at them to deal with other exercises. 

* SimpleTypes.agda provides definitions of simple types as data types, along with introduction forms (the constructors of the data types) and elimination forms (defined via pattern matching).
* DependentTypes.agda provides definitions os Sigma and Identity types as data types with introduction and dependent eliminators. It also provide dependent eliminators for simple types and Pi types defined as a renaming of Agda's built-in dependent function type.

The following files provide the actual exercises. They are listed in the order in which they should be addressed.

1. BasicFun.agda: basics of functional programming and Church encodings
2. BasicInd.agda: data types, pattern matching and recursion in Agda
3. IPL.agda: simple theorems in Intuitionistic Propositional Logic in Agda via the propositions-as-types correspondence
4. Vectors.agda: first examples of dependent (data) types and dependent functions
5. FOL.agda: simple theorems in First Order Logic in Agda via the propositions-as-types correspondence
6. SumsProds.agda: properties of Pi and Sigma types and their interaction
7. IdTypes.agda: properties of identity types and their interaction with other type formers
8. DepInd.agda: advanced exercises on dependent data types
9. WellFounded.agda: well-founded induction in Agda
10. Sorting.agda: case study on the verification of sorting algorithms
11. Eval.agda: case study on a correct-by-construction interpreter

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
