Pedersen Commitments
====================

Commitment schemes are a way for one counterparty to commit to a value such that
the value committed remains private, but can be revealed at a later time when
the committing party divulges a necessary parameter of the commitment process.
Strong commitment schemes must be both information *hiding* and computationally
*binding*.

The Pedersen commitment scheme has the following properties:

* Hiding: A dishonest party cannot discover the honest party's value.
* Binding: A dishonest party cannot open his or her commitment in more than one way
* Non-correlation: A dishonest party cannot commit to a value that is in some
  significant way correlated to the honest party's value.

* [Reference](https://www.iacr.org/archive/asiacrypt2001/22480387.pdf)

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
