hashdict
=======
Originally an erlang implementation of Elixir's `HashDict`, with `dict` api.
However now the only common feature between the two is the hashing function.
This dictionary should be suitable for both small and large number of keys.
Installation
------------
```
git clone https://github.com/fishcakez/hashdict.git
cd hashdict
make
make tests
```
Docs
----
There are currently no docs but the api and behaviour is identical to `dict`.
See http://www.erlang.org/doc/man/dict.html.
Benchmark
---------
See benchmark file for erlbench results.
