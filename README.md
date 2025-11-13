# Generating Eliminators for Rocq Inductive Types 

This repository implements a framework for **automatically generating eliminators** (recursion and elimination principles) for inductive types in **Rocq**, with a focus on **nested inductive types**. The implementation builds on **MetaRocq** and extends Rocq’s capabilities by addressing guard condition limitations and enabling sparse parametricity.

## ✨ Key Features

* 🔧 **Automatic generation** of eliminators for nested and mutual inductive types.
* 📦 Based on **MetaRocq** and integrated with **Rocq**’s sort polymorphism and elimination constraints.
* 🧠 Supports **sparse parametricity**, minimizing unnecessary hypotheses.

## 🛠️ Installation & Setup

1. **Install dependencies**
   Make sure you have a working installation of Rocq and MetaCoq.

   ```bash
   opam install rocq rocq-equations rocq-metarocq
   ```

2. **Build the project**

   ```bash
   make
   ```

## 📁 Project Structure

* `theories/API/`: Generic library for meta-programming on top of MetaRocq.
* `theories/SparseParametricity/`: Sparse Parametricity generation.
* `theories/Eliminators/`: Core implementation of recursor generation and elimination logic.
* `theories/examples_submission.v`: Demonstrations of generated eliminators on standard and nested inductive types.
* `formalization/`: Formal proofs verifying the correctness of generated eliminators and termination properties.

## 🚀 Usage

See `theories/examples.v` for usage.

## 🧪 Formalization 

The formalization of the encoding from nested inductive types to mutual inductive types is based on MetaRocq

* `typing.v` and `RoseTree.v`: A running example of a mutually nested inductive type with generated eliminators.
* `positivity_condition.v`: specify the positivity condition.
* `nested_to_mutual.v`: Defines the mutual encoding of a well-formed nested inductive type.
* `nested_to_mutual_proof.v`: Verifies that mutual encoding of a well-formed nested inductive type satisfies the strict positivity condition.


## 🧩 Integration with Rocq

This work is designed to integrate smoothly with Rocq's type theory:

* Uses Rocq’s **elimination constraints** to control allowable eliminators.
* Works with Rocq’s **sort polymorphism** (\SortPolyEC).
* Ensures compatibility with Rocq’s **termination and typing rules**.
