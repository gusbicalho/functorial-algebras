# Functorial Algebras

(Partial) (attempt of) Implementation of this paper:

https://arxiv.org/abs/2201.10287

Structured Handling of Scoped Effects: Extended Version
Zhixuan Yang, Marco Paviotti, Nicolas Wu, Birthe van den Berg, Tom Schrijvers

Algebraic effects offer a versatile framework that covers a wide variety of
effects. However, the family of operations that delimit scopes are not algebraic
and are usually modelled as handlers, thus preventing them from being used
freely in conjunction with algebraic operations. Although proposals for scoped
operations exist, they are either ad-hoc and unprincipled, or too inconvenient
for practical programming. This paper provides the best of both worlds: a
theoretically-founded model of scoped effects that is convenient for
implementation and reasoning. Our new model is based on an adjunction between a
locally finitely presentable category and a category of functorial algebras.
Using comparison functors between adjunctions, we show that our new model, an
existing indexed model, and a third approach that simulates scoped operations in
terms of algebraic ones have equal expressivity for handling scoped operations.
We consider our new model to be the sweet spot between ease of implementation
and structuredness. Additionally, our approach automatically induces fusion laws
of handlers of scoped effects, which are useful for reasoning and optimisation.
