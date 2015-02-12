Snake
=====

This module describes a snake game in terms of three constructions:

  1. A recursive datatype, `Game`
  2. The fixed point of a base functor `GameF`
  3. The free monad over `GameF`

We can convert to and from these constructions freely, and each representation affords its own benefits and tradeoffs:

  * `Game` is readily serializable.
  * `Game'` and `GameT` allow us to unfold the snake game in response to effects (for example, user input).
  * `GameT` offers a DSL for constructing snake games.

Playing the snake game typically occurs in some monad `m` (for example, `IO`) as

  * A value of type `Game' m GameState`
  * A value of type `GameT m GameState Void`

See `play` and `play'` for examples.

The `GameState` simply defines the current location and length of the snake (see `Snake`) and the bounds of the play area.
