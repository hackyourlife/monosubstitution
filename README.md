MONOSUBSTITUTION
================

These tools can crack (almost) arbitrary monoalphabetic substitution ciphers,
as long as most/all plain text words are in the dictionary.

Algorithms
----------

The "tree" algorithm is an implementation of the algorithm described in
[this paper](http://dl.acm.org/citation.cfm?id=184078).

The "sat" algorithm works differently: it encodes the word patterns into SAT
formulas, expresses the dependencies between words as additional constraints,
and asks a SAT solver for a model. The model is then the assignment of plain
text characters to cipher text characters.

Decryption
----------

```
./decrypt.py de-small 50 tree "vos oçlcsivliens tuf liras frayeras"
```

Arguments:
- `de-small`: dictionary to use.
- `50`: print at most 50 results.
- `tree`: use the tree algorithm. Useful for short cryptograms. Alternatively,
  use `sat`. Try which one gives better result for your particular text.
- `vos oçlcsivliens tuf liras frayeras`: the cryptogram you want to decode.

Scrambling
----------

The scrambling tool tries to make text look like it was a different (foreign)
language. It achieves this by trying to decode it as a foreign language.
Usually this works best for short texts, but fails for longer ones.

```
./encode.py fr 50 sat "oft funktioniert das nicht schlecht"
```

Encryption
----------

This tool can encrypt an arbitrary text with a random permutation of the
alphabet. You can use this to test the power of the decryption tool.

```
./encrypt.py "Das ist ein einfacher Test des Algorithmus"
```
