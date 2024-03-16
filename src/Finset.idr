{-
 idris2-finset

 MIT License

 Copyright (c) 2024 emdash

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}

||| Implement sets over small finite types backed by machine integers.
module Finset


import Data.Bits
import Data.Fin
import Data.Finite
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality
import Derive.Finite


%default total
%language ElabReflection


||| The size of the finite type, as a natural number.
public export
cardinality : (0 a : Type) -> Finite a => Nat
cardinality a = length (valuesOf a)

||| A natural number that 'fits inside' the underlying finite type.
public export
Cardinality : (0 a : Type) -> Finite a => Type
Cardinality a = Fin (cardinality a)

||| Like `elemToNat` from standard library, but returns a `Fin`.
elemToFin : Elem x xs -> Fin (length xs)
elemToFin Here      = FZ
elemToFin (There y) = FS (elemToFin y)

||| A proof that for `Finite a`, every `a` has an index in `valuesOf a`.
|||
||| XXX: to be totally correct, we'd need a proof of a unique index.
|||
||| Ideally, the `Finite` interface would ensure this.
|||
||| Ideally We would not need the DecEq constraint
inhabited
  : (a : Type)
  -> DecEq a
  => Finite a
  => (x : a)
  -> Elem x (valuesOf a)
inhabited a x = case isElem x (valuesOf a) of
  Yes elem => elem
  No  _    => assert_total $ idris_crash "Unlawful implementation of Finite!"

||| If `a` is `Finite`, then every `a` maps to a `Fin (cardinality a)`
ord
  : {a : Type}
  -> DecEq a
  => Finite a
  => a
  -> Cardinality a
ord x = elemToFin (inhabited a x)

||| `e` is representable as `b` if `cardinality e <= bitSize` of `b`.
|||
||| This interface captures all the constraints needed for subsequent
||| operations.
public export
interface
     DecEq e
  => Finite e
  => FiniteBits b
  => Representable e b
where
  Compat : LTE (cardinality e) (bitSize {a = b})

||| Convert a value of a finite type to a bit index in the representation.
bitPosition
  : {e : Type}
  -> Representable e b
  => e
  -> Index {a = b}
bitPosition x = bitsToIndex (weakenLTE (ord x) Compat)

||| Concrete type for sets of finite types backed by integers.
export
record BitSet e b where
  constructor Set
  values : b

||| Return an empty `BitSet`.
export
empty : Bits b => Representable e b => BitSet e b
empty = Set zeroBits

||| Return the full bitset
export
full : {e : Type} -> Neg b => Representable e b => BitSet e b
full = case isLT (cardinality e) (bitSize) of
  -- cardinality is less than bitSize, ensure high bits are clear
  Yes prf => Set $ (bit $ bitsToIndex $ natToFinLT {prf} $ cardinality e) - 1
  -- cardinality is equal to bitsize, take the fast path
  No  _   => Set oneBits

||| Insert a value into the given `BitSet`.
export
insert
  : {e : Type}
  -> Representable e b
  => e
  -> BitSet e b
  -> BitSet e b
insert x (Set values) = Set $ setBit values (bitPosition x)

||| Remove the given value from the given `BitSet`.
export
remove
  : {e : Type}
  -> Representable e b
  => e
  -> BitSet e b
  -> BitSet e b
remove x (Set values) = Set $ clearBit values (bitPosition x)

||| True if the given bitset contains the given value.
export
contains
  : {e : Type}
  -> Representable e b
  => e
  -> BitSet e b
  -> Bool
contains x (Set values) = testBit values (bitPosition x)

||| Take the union of two `BitSet`s.
export
union
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> BitSet e b
  -> BitSet e b
union (Set x) (Set y) = Set $ x .|. y

||| Take the intersection of two `BitSet`s.
export
intersect
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> BitSet e b
  -> BitSet e b
intersect (Set x) (Set y) = Set $ x .&. y

||| Take the set difference of x / y.
export
diff
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> BitSet e b
  -> BitSet e b
diff (Set x) (Set y) = Set $ x .&. complement y

||| Returns the number elements in the given bitset.
export
length
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> Nat
length (Set values) = popCount values

||| Convert a `BitSet e b` to a `List e`.
export
asList
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> List e
asList (Set values) =
  let
    values := toList $ asBitVector values
    zipped := zip values $ valuesOf e
  in
    map snd $ filter fst zipped

||| If Show is implemented for `e`, then implement it for `BitSet e b`.
export
implementation
    {e : Type}
  -> Representable e b
  => Show e
  => Show (BitSet e b)
where
  show values = "Set \{show $ the (List e) $ asList values}"


{--- testing ---}

data Test = A | B | C
%runElab derive "Test" [Eq, Ord, Finite, Show]

data Test1 = One | Two | Three
%runElab derive "Test1" [Eq, Ord, Finite, Show]

data Test2 = T2 Test Test1
%runElab derive "Test2" [Eq, Ord, Finite, Show]

DecEq Test  where decEq = decEq @{FromEq}
DecEq Test1 where decEq = decEq @{FromEq}
DecEq Test2 where decEq = decEq @{FromEq}

Representable Test  Bits8  where Compat = %search
Representable Test1 Bits8  where Compat = %search
Representable Test2 Bits16 where Compat = %search

-- expected, because this type is too large for 8-bits
failing "While processing right hand side of Compat"
  -- "can't find an implementation for LTE (cardinality Test2) bitSize"
  Representable Test2 Bits8 where Compat = %search

test : BitSet Test Bits8
test = empty

test1 : BitSet Test Bits8
test1 = insert A $ insert C empty

test2 : BitSet Test Bits8
test2 = insert B $ insert C empty

test3 : BitSet Test Bits8
test3 = test1 `diff` test2

test4 : BitSet Test2 Bits16
test4 = insert (T2 A One) $ insert (T2 C Two) $ insert (T2 B Three) empty
