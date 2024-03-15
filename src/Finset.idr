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
cardinality : (0 a : Type) -> Finite a => Nat
cardinality a = length (valuesOf a)

||| A natural number bounded by the cardiality of the given type.
Cardinality : (0 a : Type) -> Finite a => Type
Cardinality a = Fin (cardinality a)

||| Like `elemToNat` from standard library, but returns a `Fin`.
elemToFin : Elem x xs -> Fin (length xs)
elemToFin Here = FZ
elemToFin (There y) = FS (elemToFin y)

||| This should be guaranteed by the Finite interface
|||
||| Ideally, the derive macros would generate this function in a more
||| direct way, so that `assert_total` could be dropped here.
inhabited : (a : Type) -> DecEq a => Finite a => (x : a) -> Elem x (valuesOf a)
inhabited a x = case isElem x (valuesOf a) of
  Yes elem => elem
  No  _    => assert_total $ idris_crash "unlawful implementation of Finite"

||| Convert a `Finite a` to a finite natural number
ord : {a : Type} -> DecEq a => Finite a => a -> Cardinality a
ord x = elemToFin (inhabited a x)

||| Convert a finite natural number to a value of a finite type
val : Finite a => Cardinality a -> a
val {a} n = index' (valuesOf a) n


||| This approach will work whenever the cardinality of e is LEQ the
||| bit width of b.
interface DecEq e => Finite e => FiniteBits b => AsBits e b where
  Compat : LTE (cardinality e) (bitSize {a = b})

export
data BitSet : (e : Type) -> (b : Type) -> AsBits e b => Type where
  MkBitSet : AsBits e b => b -> BitSet e b

||| Insert x into xs by setting the corresponding bit.
insert : {e, b : Type} -> AsBits e b => e -> b -> b
insert x xs = setBit xs $ bitsToIndex (weakenLTE (ord x) Compat)

||| Check whether x contains xs by testing the corresponding bit.
contains : {e, b : Type} -> AsBits e b => e -> b -> Bool
contains x xs = testBit xs $ bitsToIndex (weakenLTE (ord x) Compat)

||| Return a list containing just the elements which are present in xs.
asList : {e, b : Type} -> AsBits e b => b -> List e
asList xs =
  let
    xs     := toList $ asBitVector xs
    vals   := valuesOf e
    zipped := zip xs vals
  in map snd $ filter fst zipped




{--- testing ---}

data Test = A | B | C
%runElab derive "Test" [Eq, Ord, Finite]

{- this table is very similar to the one below -}
Prelude.Uninhabited (A = B) where uninhabited Refl impossible
Prelude.Uninhabited (A = C) where uninhabited Refl impossible
Prelude.Uninhabited (B = A) where uninhabited Refl impossible
Prelude.Uninhabited (B = C) where uninhabited Refl impossible
Prelude.Uninhabited (C = A) where uninhabited Refl impossible
Prelude.Uninhabited (C = B) where uninhabited Refl impossible

{- it's annoying to have to define DecEq to use this -}
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


AsBits Test Bits8 where Compat = LTESucc $ LTESucc $ LTESucc $ LTEZero

test : String
test = "Hello from Idris2!"
