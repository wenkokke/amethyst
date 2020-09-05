Amethyst: Neural Network Verification in Agda
---------------------------------------------------------------------------------

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
  { weights    = [ 5.0e8 ] ∷ [ 5.0e8 ] ∷ []
  ; biases     = [ -7.5e8 ]
  ; activation = sigmoid
  }

model : Network Float 2 1 1
model = layer0 ∷ []
```

We can then check properties of the model by writing SMT assertions. Let’s write
a script which checks if our model correctly implements the AND gate:

```agda
script : Script [] (Reals 2 ++ Reals 1) (SAT ∷ [])
script = withReflectedNetworkAsScript model $ λ where

  -- Give names to input and output nodes:
  iv@(i₀ ∷ i₁ ∷ []) ov@(o₀ ∷ [])

  -- Give remainder of the SMT-LIB script:
    → assert (((i₀ == 0·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 0·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 1·0f))
    ∷ check-sat
    ∷ []
```

We then run our script with Z3, and check that it returns `sat`:

```agda
_ : z3 script ≡ sat ∷ []
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
and existentially quantifier expressions:

```agda
-- pending…
```

Whoa, that’s very cool! Now we know our network is robust around both truthy and
falsey inputs!

Getting Started
=================================================================================

Amethyst requires Agda and several Agda libraries to work:

- [agda][agda] (latest)
- [agda-stdlib][agda-stdlib] (latest)
- [agdarsec][agdarsec] (latest)
- [schmitty][schmitty] (latest)

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

We realise this is quite a lot, and to make matters worse, Amethyst and many of
its dependencies are under active development. To make matters easier, we
provide a [Dockerfile](Dockerfile)!

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
[agda]: https://github.com/agda/agda
[agda-stdlib]: https://github.com/agda/agda-stdlib
[agdarsec]: https://github.com/gallais/agdarsec
[schmitty]: https://github.com/wenkokke/schmitty
[Z3]: https://github.com/Z3Prover/z3
[CVC4]: https://github.com/CVC4/CVC4
