# Generating Eliminators for Rocq Inductive Types

This repository implements a framework for **automatically generating
eliminators** (recursion and elimination principles) for inductive types in
**Rocq**, including **nested inductive types**.

## ✨ Key Features

* **New positivity** condition for nested inductive types, and proof that any
  positive nested inductive type has a mutual encoding
* **Automatic generation** of eliminators for nested and mutual inductive types,
  based on a **sparse** notion of **parametricity** to minimize unnecessary hypotheses.

## 🛠️ Installation & Setup

  1. Install [opam](https://opam.ocaml.org/doc/Install.html) the package manager of OCaml
  2. You can then install Rocq 9.0 and necessary libraries with the script `opam-artifact-setup.sh`.
    The script creates a fresh switch, and install

    opam pin add rocq-core 9.0.0 &&
    opam install rocq-prover &&
    opam repo add rocq-released https://rocq-prover.org/opam/released &&
    opam install rocq-equations &&
    opam install vsrocq-language-server &&
    opam install rocq-metarocq

    If you have already run the script, and created a switch, the script should detect it.

3. The script will then build the project.
  It can also be built by hand using the usual `make` and `make clean` commands.
  Compilation should take under 5 minutes.

## 📁 Project Structure

* `formalization/`: Formal proofs verifying the correctness of generated eliminators.
  - `typing.v` and `RoseTree.v`: A running example of a mutually nested inductive type with generated eliminators.
  - `Lemma.v`: utility lemmas either missing in MetaRocq or specific to this project
  - `Positivity_condition.v`: specify the new positivity condition for nested inductive types
  - `Nested_to_mutual.v`: The translation from nested inductive types to mutual inductive types.
  - `Nested_to_mutual_proof.v`: Proof the translation preserves positivity.

* `plugin_nested_eliminators/`: Generation of Eliminators
  - `API/`: Generic library for meta-programming on top of MetaRocq.
  - `SparseParametricity/`: Generation of Sparse Parametricity.
  - `Eliminators/`: Core implementation of eliminators.
  - `test_functions.v`: Quoting and Plugin Interface with MetaRocq.
  - `examples.v`: Demonstrations of generated eliminators on standard and nested inductive types.

Note: Guard Checking is unset in the formalization in order not to have to reason
by well-foundedness on the size of the environment. It is clearly decreasing
as a nested inductive type can only refer to previously defined
inductive types, which by definition are themselves defined in smaller environments.

## 📝 Differences with the Paper

In the associated paper, we have proceeded to a few name changes to ease understanding.
For instance, we have changed the constructors' names of the view.

## 🧩 Integration with Rocq

The plugin has been adapted and merged into Rocq, and is part of Rocq 9.2.

- The API used for managing de Bruijn indices is different
- Sparse parametricity and the fundamental theorem have been named `_all` and
  `_all_theorem` to facilitate understanding
- Sparse parametricity and its theorem are Sort Polymorphic to account for
  the different sorts of Rocq. It is ad hoc in the plugin as MetaRocq does not
  have sort polymorphism yet.
- Many small changes were performed to account for different Rocq features
  like primitive records, SProp and relevances, the absence of algebraic universes etc...
- An option to generate partial version of `sparse_parametricity` for only
  some nestable parameters was added

None of these differences required conceptual changes, and they should be
considered as engineering details.
