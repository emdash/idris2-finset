# Finite Sets over Small Types

The [idris2-finite](https://github.com/stefan-hoeck/idris2-finite)
package provides a derivable interface for finite types.

This package extends this crate to efficiently represent sets of any
type implementing `Finite` by using machine integers.

The central type is `BitSet e b`, where e must implement `Finite`, and
`DecEq`, and `b` is a storage type implementing `FiniteBits`. You can
use any combination of element and storage type, so long as it is
large enough. The `Representable` interface captures the constraint
that the cardinality of `e` must be less than the `bitSize` of `b`.

## Example

```idris

||| An element type with finite cardinality.
data Test = A | B | C

-- Derive this set of interfaces.
%runElab derive "Test" [Eq, Ord, Finite, Show]

-- Implement DecEq for the element type. Here's a lazy way to do it.
DecEq Test where decEq = decEq @{FromEq}

-- Establish that our type is representable in 8 bits.
Representable Test Bits8 where Compat = %search

-- now we can use BitSet similarly to SortedSet

test : BitSet Test Bits8
test = insert A $ insert C empty

test2 : BitSet Test Bits8
test2 = insert B $ insert C empty

test3 : BitSet Test Bits8
test3 = test1 `diff` test2
```
