# Polynomial Semantics of Dependent Type Theory

This repository contains the partial Agda formalization accompanying the thesis **"Polynomial Semantics of Dependent Type Theory"** by **Lukas Buchschmid**.

The project formalizes the definitions of Type Structures, Dependent Polynomials, and B-Systems. Furthermore, we formalize the construction of the dependent polynomial Monad derived from a B-System.

## 📂 Project Structure

### 1. Foundations
These modules define the core mathematical structures used throughout the thesis.

* **`TyStr.agda`**: Defines the underlying **Type Structure**, including basic identities regarding context formation.
* **`DepPoly.agda`**: Defines **Dependent Polynomials** and their operations (substitution, composition), along with identities governing their interaction.
* **`BSystems.agda`**: Defines **B-Systems** and the auxiliary structure required to construct the dependent polynomial Monad.
* **`Monad.agda`**: Defines the general structure of a **Dependent Polynomial Monad**.

### 2. Core Proofs & Constructions
These modules contain the main results linking B-Systems to Monads.

* **`BSystemToDepPoly.agda`**: Constructs a dependent polynomial from a B-System. It includes proofs of identities regarding the interaction of generated homomorphisms, which are required to show the polynomial forms a Monad.
* **`BSystemToMonad.agda`**: Constructs the monad natural transformations $\eta$ and $\mu$. (Note: The proof that these satisfy the monad laws is currently omitted).
* **`ConvertingSubstitutions.agda`**: Contains the proof that the morphism of B-Systems induced by a substitution is a homomorphism.