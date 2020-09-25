Amethyst: Neural Network Verification in Agda
---------------------------------------------------------------------------------

[![Build Status](https://travis-ci.org/wenkokke/amethyst.svg?branch=master)](https://travis-ci.org/wenkokke/amethyst)
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]
[![agdarsec][agdarsec-version]][agdarsec]
[![schmitty][schmitty-version]][schmitty]

What is Amethyst?
=================================================================================

Amethyst is a library for lightweight neural network verification in Agda, using
various solvers as backends. 
Let’s look at an example—seen [here][AND-Gate-2-Sigmoid-1] in glorious,
clickable HTML. Our example is a neural network which emulates the logical
AND-gate. We define our model as follows:

```agda
layer0 : Layer Float 2 1
layer0 = record
  { weights    = [ 5.0e1 ] ∷ [ 5.0e1 ] ∷ []
  ; biases     = [ -7.5e1 ]
  ; activation = sigmoid
  }

model : Network Float 2 1 1
model = layer0 ∷ []
```

We can then check properties of the model by specifying constraints that Amethyst
then automatically converts into SMT assertions. Let’s write
some constraints which check if our model correctly implements the AND gate:

```agda
exactConstraints : NetworkConstraints 2 1
exactConstraints (i₀ ∷ i₁ ∷ []) (o₀ ∷ []) =
  (i₀ == 0·0f ∧ i₁ == 0·0f ⇒ o₀ == 0·0f) ∷
  (i₀ == 0·0f ∧ i₁ == 1·0f ⇒ o₀ == 0·0f) ∷
  (i₀ == 1·0f ∧ i₁ == 0·0f ⇒ o₀ == 0·0f) ∷
  (i₀ == 1·0f ∧ i₁ == 1·0f ⇒ o₀ == 1·0f) ∷
  []
```

We then combine the model and the constraints to generate a script for Z3. 
Note that in order to verify that the constraints hold for the model, 
we need to negate the constraints and then check that the corresponding problem is unsatisfiable, 
i.e. that there exists no assignment to the inputs and outputs that violate the constraints. 

The `query` function automatically handles the negation and the script generation for us. 
Therefore all that's left for us to do is to feed it into `z3` and check that the answer is `unsat`:

```agda
_ : z3 (query model exactConstraints) ≡ unsat ∷ []
_ = refl
```

Woo! Turns out our network is correct! Of course, we could’ve checked this by
just running the network in Agda:

```agda
_ : evalNetwork model (0.0 ∷ 0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (0.0 ∷ 1.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ 0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ 1.0 ∷ []) ≡ (1.0 ∷ [])
_ = refl
```

Yeah, that was easier… However, the SMT solver also allows us to run universally
and existentially quantified expressions. For example we might want to the network
models the AND gate correctly for any values sufficiently close to 0.0 and 1.0.
This can be done by defining some new predicates `truthy` and `falsey`:

```agda
ε : ∀ {Γ} → Term Γ REAL
ε = toReal 0.2

truthy : ∀ {Γ} → Term Γ REAL → Term Γ BOOL
truthy x = ∣ 1·0f - x ∣ ≤ ε

falsey : ∀ {Γ} → Term Γ REAL → Term Γ BOOL
falsey x = ∣ 0·0f - x ∣ ≤ ε
```

We can then rewrite our constraints to use these fuzzy values:

```agda
fuzzyConstraints : NetworkConstraints 2 1
fuzzyConstraints (i₀ ∷ i₁ ∷ []) (o₀ ∷ []) =
  (falsey i₀ ∧ falsey i₁ ⇒ falsey o₀) ∷
  (falsey i₀ ∧ truthy i₁ ⇒ falsey o₀) ∷
  (truthy i₀ ∧ falsey i₁ ⇒ falsey o₀) ∷
  (truthy i₀ ∧ truthy i₁ ⇒ truthy o₀) ∷
  []
```

and then rerun the query:

```agda
_ : z3 (query model fuzzyConstraints) ≡ unsat ∷ []
_ = refl
```

Whoa, that’s very cool! Now we know our network is robust around both truthy and
falsey inputs!

Getting Started
=================================================================================

Amethyst requires Agda and several Agda libraries to work:

- agda ([master][agda])
- agda-stdlib ([experimental][agda-stdlib])
- agdarsec ([master][agdarsec)
- schmitty ([latest][schmitty])

Furthermore, Amethyst requires you to install any external solver you’d like to
use, e.g., [Z3][Z3], [CVC4][CVC4], [Marabou][Marabou], etc…

Finally, you’ll have to setup the libraries you want to use in `.agda/libraries`,
and the external solvers in `.agda/executables`:
```sh
# .agda/libraries:
/path/to/standard-library.agda-lib
/path/to/agdarsec/agdarsec.agda-lib
/path/to/schmitty/schmitty.agda-lib
```
```sh
# .agda/executables:
/path/to/z3
/path/to/cvc4
/path/to/marabou
```

We realise this is quite a lot! Unfortunately, Amethyst required the revision of the floating-point primitives in Agda, which explains why it requires patches to its dependencies. The dependencies will stabilise a bit with the release of Agda v2.6.2. To make matters easier, for now, we provide a [Dockerfile](Dockerfile)!

Related Work
=================================================================================

Amethyst follows the same principles as [Lazuli][Lazuli] for Liquid Haskell,
[Sapphire][Sapphire] for Python with Z3, and [StarChild][StarChild] for F*. 

Unlike Lazuli and StarChild, the integration between Amethyst and various
solvers is written in pure Agda, and is highly customisable. Consequently,
Amethyst is able to generate far more concise SMT queries, tailored to the
neural network domain. Furthermore, it offers integration with other solvers,
specific to the neural network domain, such as [Marabou][Marabou] (pending).

Unlike Sapphire, Amethyst is implemented in a dependently-typed language, and is
able to offer a far more seamless integration than would be possible in Python
using the Z3 API.

[Lazuli]: https://github.com/wenkokke/lazuli
[Marabou]: https://github.com/NeuralNetworkVerification/Marabou
[Sapphire]: https://github.com/wenkokke/sapphire
[StarChild]: https://github.com/wenkokke/starchild
[AND-Gate-2-Sigmoid-1]: https://wenkokke.github.io/amethyst/AND-Gate-2-Sigmoid-1.html
[agda]: https://github.com/agda/agda/
[agda-version]: https://img.shields.io/badge/Agda-PR%20%234885-blue
[agda-stdlib]: https://github.com/agda/agda-stdlib/tree/experimental
[agda-stdlib-version]: https://img.shields.io/badge/agdastdlib-experimental-blue
[agdarsec]: https://github.com/gallais/agdarsec
[agdarsec-version]: https://img.shields.io/badge/agdarsec-master-blue
[schmitty]: https://github.com/wenkokke/schmitty
[schmitty-version]: https://img.shields.io/badge/schmitty-latest-blue
[Z3]: https://github.com/Z3Prover/z3
[CVC4]: https://github.com/CVC4/CVC4
