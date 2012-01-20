Numeric.NumType.TF -- Type-level (low cardinality) integers
Bjorn Buckwalter, bjorn.buckwalter@gmail.com
License: BSD3


= Summary =

This Module provides unary type-level representations, hereafter
referred to as "NumTypes", of the (positive and negative) integers
and basic operations (addition, subtraction, multiplication, division)
on these. While functions are provided for the operations NumTypes
exist solely at the type level and their only value is 'undefined'.

There are similarities with the HNats of the HList library [1],
which was indeed a source of inspiration. Occasionally references
are made to the HNats. The main addition in this module is negative
numbers.

The practical size of the NumTypes is limited by the type checker
stack. If the NumTypes grow too large (which can happen quickly
with multiplication) an error message similar to the following will
be emitted:

    Context reduction stack overflow; size = 20
    Use -fcontext-stack=N to increase stack size to N

This situation could concievably be mitigated significantly by using
e.g. a binary representation of integers rather than Peano numbers.

Also, even if stack size is increased type-checker performance
quickly gets painfully slow. If you will be working with type-level
integers beyond (-20, 20) this module probably isn't for you. They
are, however, eminently suitably for applications such as representing
physical dimensions.


= Preliminaries =

This module requires GHC 7.0 or later.

> {-# LANGUAGE UndecidableInstances
>            , TypeFamilies
>            , EmptyDataDecls
>            , FlexibleInstances
>            , ScopedTypeVariables
> #-}

> {- |
>    Copyright  : Copyright (C) 2006-2012 Bjorn Buckwalter
>    License    : BSD3
>
>    Maintainer : bjorn.buckwalter@gmail.com
>    Stability  : Stable
>    Portability: GHC only?
>
> Please refer to the literate Haskell code for documentation of 
> the implementation.
> -}

> module Numeric.NumType.TF
>   -- Basic classes (exported versions).
>   ( NumType
>   -- Data types (exported to avoid lengthy qualified types in complier
>   -- error messages).
>   , Z, S, N
>   -- * Type level arithmetics
>   , Pred, Succ, Negate, Add, Sub, Div, Mul
>   -- * Type synonyms for convenience
>   , Zero, Pos1, Pos2, Pos3, Pos4, Pos5, Neg1, Neg2, Neg3, Neg4, Neg5
>   -- * Value level functions
>   -- $functions
>   , toNum, incr, decr, negate, (+), (-), (*), (/)
>   -- * Values for convenience
>   -- | For use with the value level functions.
>   , zero, pos1, pos2, pos3, pos4, pos5, neg1, neg2, neg3, neg4, neg5
>   ) where

> import Prelude hiding ((*), (/), (+), (-), negate)
> import qualified Prelude ((+), negate)

Use the same fixity for operators as the Prelude.

> infixl 7  *, /
> infixl 6  +, -


= NumTypes =

We start by defining a class encompassing all integers with the
class function 'toNum' that converts from the type-level to a
value-level 'Num'.

> class NumTypeI n where
>   -- | Convert a type level integer to an instance of 'Prelude.Num'.
>   toNum :: Num a => n -> a
>   -- | Negation.
>   type Negate n
>   -- | Predecessor.
>   type Pred n
>   -- | Successor.
>   type Succ n


Now we use a trick from Oleg Kiselyov and Chung-chieh Shan [2]:

    -- The well-formedness condition, the kind predicate
    class Nat0 a where toInt :: a -> Int
    class Nat0 a => Nat a           -- (positive) naturals

    -- To prevent the user from adding new instances to Nat0 and especially
    -- to Nat (e.g., to prevent the user from adding the instance |Nat B0|)
    -- we do NOT export Nat0 and Nat. Rather, we export the following proxies.
    -- The proxies entail Nat and Nat0 and so can be used to add Nat and Nat0
    -- constraints in the signatures. However, all the constraints below
    -- are expressed in terms of Nat0 and Nat rather than proxies. Thus,
    -- even if the user adds new instances to proxies, it would not matter.
    -- Besides, because the following proxy instances are most general,
    -- one may not add further instances without overlapping instance extension.
    class    Nat0 n => Nat0E n
    instance Nat0 n => Nat0E n
    class    Nat n => NatE n
    instance Nat n => NatE n

We apply this trick to our NumTypeI class. In our case we will elect to
append an "I" to the internal (non-exported) classes rather than
appending an "E" to the exported classes.

> -- | Class encompassing all valid type level integers.
> class    (NumTypeI n) => NumType n
> instance (NumTypeI n) => NumType n

We do not have to do this for our other classes. They have the above
classes in their constraints and since the instances are complete
(not proven) a new instance cannot be defined (actually used in the
case of GHC) without overlapping instances.

Now we Define the data types used to represent integers. We begin
with 'Zero', which we allow to be used as both a positive and a
negative number in the sense of the previously defined type classes.
'Z' corresponds to HList's 'HZero'.

> -- | Type level zero.
> data Z

Next we define the "successor" type, here called 'S' (corresponding
to HList's 'HSucc').

> -- | Successor for building type level natural numbers.
> data S n

Finally we define the "negation" type used to represent negative
numbers.

> -- | Type level negation of natural numbers.
> data N n

The 'NumTypeI' instances restrict how 'Z', 'S', and 'N' may be combined
to assemble 'NumType's, and the type synonym declarations demonstrate
some basic arithmetic.

> instance NumTypeI Z where  -- Zero.
>   type Negate Z = Z       -- Still zero.
>   type Pred Z = N (S Z)   -- Negative one.
>   type Succ Z = S Z       -- One.
>   toNum _ = 0

> instance NumTypeI (S Z) where   -- One.
>   type Negate (S Z) = N (S Z)  -- Minus one.
>   type Pred (S Z) = Z          -- Zero.
>   type Succ (S Z) = S (S Z)    -- Two.
>   toNum _ = 1

> -- Naturals greater than one.
> instance NumTypeI (S n) => NumTypeI (S (S n)) where  -- N.
>   type Negate (S (S n)) = N (S (S n))              -- -N.
>   type Pred (S (S n)) = S n                        -- N-1
>   type Succ (S (S n)) = S (S (S n))                -- N+1
>   toNum _ = 1 Prelude.+ toNum (undefined :: S n)

> -- Negatives (minus one and below).
> instance NumTypeI (S n) => NumTypeI (N (S n)) where  -- -N
>   type Negate (N (S n)) = S n                      -- N
>   type Pred (N (S n)) = N (S (S n))                -- -(N+1)
>   type Succ (N (S n)) = Negate n                   -- -(N-1)
>        -- NOTE: `N n` would be invalid for `Succ (N (S Z))`
>   toNum _ = Prelude.negate $ toNum (undefined :: S n)


= Show instances =

For convenience we create show instances for the defined NumTypes.

> instance Show Z where show = ("NumType " ++) . show . toNum
> instance NumTypeI (S n) => Show (S n) where show = ("NumType " ++) . show . toNum
> instance NumTypeI (N n) => Show (N n) where show = ("NumType " ++) . show . toNum


= Addition and subtraction =

Now let us move on towards more complex arithmetic operations. We
define type families for addition and subtraction of NumTypes.

> -- | Addition (@a + b@).
> type family Add a b  -- a + b.
> -- | Subtraction (@a - b@).
> type family Sub a b  -- a - b.

Adding anything to Zero gives "anything".

> type instance Add Z n = n

When adding to a non-Zero number our strategy is to "transfer" type
constructors from the first type to the second type until the first
type is Zero.

> type instance Add (S n) n' = Add n (Succ n')
> type instance Add (N n) n' = Add (Succ (N n)) (Pred n')

Substitution is defined trivially with addition and negation.

> type instance Sub a b = Add a (Negate b)


= Multiplication =

Type family for multiplication. Multiplication is limited by the
type checker stack. If the result of multiplication is too large
this error message will be emitted:

    Context reduction stack overflow; size = 20
    Use -fcontext-stack=N to increase stack size to N

> -- | Multiplication (@a * b@).
> type family Mul a b        -- a * b.
> type instance Mul Z n = Z  -- Trivially.

Multiplication is performed by recursive addition of one number
to itself. The recursion is terminated by the `Mul Z n` instance.

> type instance Mul (S n) n' = Add n' (Mul n n')  -- a*b = b+(a-1)*b
> type instance Mul (N n) n' = Negate (Mul n n')  -- (-a)*b = -(a*b)


= Division =

Division is more complicated than multiplication. We start by
defining division only for positive (natural) numbers. This is
necessary to ensure bad division terminates with a proper error
instead of overflowing the context stack (more confusing).

> type family DivP n m            -- n / m.
> type instance DivP Z (S n) = Z  -- Trivially.

The recursive instance for division is quite complex and in fact I
do not recall how I derived it. But it works (I promise!).

> type instance DivP (S n) (S n') = S (DivP (Pred (Sub (S n) n')) (S n'))  -- Oh my!

Now we can generalize division to negative numbers too, building on
top of 'DivP'. A trivial but tedious exercise.

> -- | Division (@a / b@).
> type family Div a b            -- a / b.
> type instance Div Z (N n) = Z  -- Mustn't allow “Div Z Z”!
> type instance Div Z (S n) = Z
> type instance Div (S n) (S n') = DivP (S n) (S n')
> type instance Div (N n) (N n') = DivP n n'
> type instance Div (N n) (S n') = N (DivP n (S n'))
> type instance Div (S n) (N n') = N (DivP (S n) n')


= Value level functions =

> {- $functions
> Using the above type classes we define functions for various
> arithmetic operations. All functions are undefined and only operate
> on the type level. Their main contribution is that they facilitate
> NumType arithmetic without explicit (and tedious) type declarations.
> -}

The main reason to collect all functions here is to keep the
preceeding sections free from distraction.

> -- | Negate a 'NumType'.
> negate :: NumType a => a -> Negate a
> negate _ = undefined

> -- | Increment a 'NumType' by one.
> incr :: NumType a => a -> Succ a
> incr _ = undefined

> -- | Decrement a 'NumType' by one.
> decr :: NumType a => a -> Pred a
> decr _ = undefined

> -- | Add two 'NumType's.
> (+) :: (NumType a, NumType b) => a -> b -> Add a b
> _ + _ = undefined

> -- | Subtract the second 'NumType' from the first.
> (-) :: (NumType a, NumType b) => a -> b -> Sub a b
> _ - _ = undefined

> -- | Multiply two 'NumType's.
> (*) :: (NumType a, NumType b) => a -> b -> Mul a b
> _ * _ = undefined

> -- | Divide the first 'NumType' by the second.
> (/) :: (NumType a, NumType b) => a -> b -> Div a b
> _ / _ = undefined


= Convenince types and values =

Finally we define some type synonyms for the convenience of clients
of the library.

> type Zero = Z
> type Pos1 = S Z
> type Pos2 = S Pos1
> type Pos3 = S Pos2
> type Pos4 = S Pos3
> type Pos5 = S Pos4
> type Neg1 = N Pos1
> type Neg2 = N Pos2
> type Neg3 = N Pos3
> type Neg4 = N Pos4
> type Neg5 = N Pos5

Analogously we also define some convenience values (all 'undefined'
but with the expected types).

> zero :: Z  -- ~ hZero
> zero = undefined
> pos1 :: Pos1
> pos1 = incr zero
> pos2 :: Pos2
> pos2 = incr pos1
> pos3 :: Pos3
> pos3 = incr pos2
> pos4 :: Pos4
> pos4 = incr pos3
> pos5 :: Pos5
> pos5 = incr pos4
> neg1 :: Neg1
> neg1 = decr zero
> neg2 :: Neg2
> neg2 = decr neg1
> neg3 :: Neg3
> neg3 = decr neg2
> neg4 :: Neg4
> neg4 = decr neg3
> neg5 :: Neg5
> neg5 = decr neg4


= References =

[1] http://homepages.cwi.nl/~ralf/HList/
[2] http://okmij.org/ftp/Computation/resource-aware-prog/BinaryNumber.hs

