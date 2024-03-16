||| Implement sets of small finite types using fast integers
module Finset


import Data.Bits
import Data.Fin
import Data.Finite
import Data.List
import Data.List.Elem
import Decidable.Equality
import Derive.Finite


%default total
%language ElabReflection


||| The size of the finite type, as a natural number
public export
cardinality : (0 a : Type) -> Finite a => Nat
cardinality a = length (valuesOf a)

||| The size of the finite type, as `Fin`
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
  No  _    => assert_total $ idris_crash "unlawful implementation of Finite"

||| If `a` is `Finite`, then every `a` maps to a bounded natural
||| number.
ord
  : {a : Type}
  -> DecEq a
  => Finite a
  => a
  -> Cardinality a
ord x = elemToFin (inhabited a x)

||| If `a` is `Finite`, then every natural number less than the size
||| of `a` maps to a value of `a`.
val : Finite a => Cardinality a -> a
val {a} n = index' (valuesOf a) n

||| `e` is representable in terms of `b` if the cardinality of `e` is
||| less than the `bitSize` of `b`.
|||
||| That this is an interface feels like a bit of a hack.
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

||| Concrete type for sets of finite types backed by integers
export
record BitSet e b where
  constructor Set
  values : b

||| Return an empty `BitSet`
export
empty : Bits b => Representable e b => BitSet e b
empty = Set zeroBits

||| Return the full bitset
export
full : Bits b => Representable e b => BitSet e b

||| Insert a value into the given `BitSet`
export
insert
  : {e : Type}
  -> Representable e b
  => e
  -> BitSet e b
  -> BitSet e b
insert x (Set values) = Set $ setBit values (bitPosition x)

||| Remove the given value from the given `BitSet`
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

||| Take the union over two `BitSet`s
export
union
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> BitSet e b
  -> BitSet e b
union (Set x) (Set y) = Set $ x .|. y

||| Take the intersection over two BitSet`s
export
intersect
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> BitSet e b
  -> BitSet e b
intersect (Set x) (Set y) = Set $ x .&. y

||| Take the set difference of x / y
export
diff
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> BitSet e b
  -> BitSet e b
diff (Set x) (Set y) = Set $ x .&. complement y

||| Returns the number elements in the given bitset
export
length
  : {e : Type}
  -> Representable e b
  => BitSet e b
  -> Nat
length (Set values) = popCount values

||| Convert to a list representation
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

||| Give us a nice string representation
|||
||| XXX: How do I customize this for the repl?
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

{- this table is very similar to the one below -}
Prelude.Uninhabited (A = B) where uninhabited Refl impossible
Prelude.Uninhabited (A = C) where uninhabited Refl impossible
Prelude.Uninhabited (B = A) where uninhabited Refl impossible
Prelude.Uninhabited (B = C) where uninhabited Refl impossible
Prelude.Uninhabited (C = A) where uninhabited Refl impossible
Prelude.Uninhabited (C = B) where uninhabited Refl impossible

{-
  it's annoying to have to define DecEq by hand
  how to remove the need for this?
-}
DecEq Test where
  decEq A A = Yes Refl
  decEq A B = No absurd
  decEq A C = No absurd
  decEq B A = No absurd
  decEq B B = Yes Refl
  decEq B C = No absurd
  decEq C A = No absurd
  decEq C B = No absurd
  decEq C C = Yes Refl

{- How to remove the need to implement for each pair of types? -}
Representable Test Bits8 where Compat = %search

test : BitSet Test Bits8
test = empty

test1 : BitSet Test Bits8
test1 = insert A $ insert C empty

test2 : BitSet Test Bits8
test2 = insert B $ insert C empty

test3 : BitSet Test Bits8
test3 = test1 `diff` test2
