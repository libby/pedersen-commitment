Pedersen Commitments
====================

[![CircleCI](https://circleci.com/gh/adjoint-io/pedersen-commitment.svg?style=svg&circle-token=35a75a2815badbfcb8ed604037cff3203b848bd2)](https://circleci.com/gh/adjoint-io/pedersen-commitment)

Commitment schemes are a way for one counterparty to commit to a value such that
the value committed remains private, but can be revealed at a later time when
the committing party divulges a necessary parameter of the commitment process.
Strong commitment schemes must be both information *hiding* and computationally
*binding*.

Pedersen commitment scheme has the following properties:

1. Hiding: A dishonest party cannot discover the honest party's value.
2. Binding: A dishonest party cannot open his or her commitment in more than one way
3. Non-correlation: A dishonest party cannot commit to a value that is in some
   significant way correlated to the honest party's value.

Using Pedersen commitments we implement a [Mutually Independent
Commitments](https://www.iacr.org/archive/asiacrypt2001/22480387.pdf), a secure
multiparty communication protocol in which counterparties can commit to
arbitrary messages or data in a binding way such that all counterparties can
perform zero knowledge equality or non-equality checks of counterparts data,
with the option to reveal the data at a later point; all with perfect
information hiding of the underlying data or messages.

See:

1. Pedersen, Torben Pryds. "Non-interactive and information-theoretic secure verifiable secret sharing." Annual International Cryptology Conference. Springer Berlin Heidelberg, 1991.  APA	
2. Liskov, Moses, et al. "Mutually independent commitments." International Conference on the Theory and Application of Cryptology and Information Security. Springer Berlin Heidelberg, 2001.  APA	
3. Blum, Manuel, and Silvio Micali. "How to generate cryptographically strong sequences of pseudorandom bits." SIAM journal on Computing 13.4 (1984): 850-864.

Usage
-----

```bash
$ stack build
$ stack repl
> :load Example.hs
```

License
-------

```
Copyright 2017 Adjoint Inc

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```

