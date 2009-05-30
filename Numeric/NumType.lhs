Numeric.NumType -- Type-level (low cardinality) integers
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

This module requires GHC 6.6 or later. We utilize multi-parameter
type classes, phantom types, functional dependencies and undecidable
instances (and possibly additional unidentified GHC extensions).

> {-# LANGUAGE UndecidableInstances
>            , ScopedTypeVariables
>            , EmptyDataDecls
>            , FunctionalDependencies
>            , MultiParamTypeClasses
>            , FlexibleInstances
> #-}

> {- |
>    Copyright  : Copyright (C) 2006-2009 Bjorn Buckwalter
>    License    : BSD3
>
>    Maintainer : bjorn.buckwalter@gmail.com
>    Stability  : Stable
>    Portability: GHC only?
>
> Please refer to the literate Haskell code for documentation of both API
> and implementation.
> -}

> module Numeric.NumType
>   -- Basic classes (exported versions).
>   ( NumType, PosType, NegType, NonZero
>   -- Arithmetic classes.
>   , Succ, Negate, Sum, Div, Mul
>   -- Functions.
>   , toNum, incr, decr, negate, (+), (-), (*), (/)
>   -- Data types.
>   , Zero, Pos, Neg
>   -- Type synonyms for convenience.
>   , Pos1, Pos2, Pos3, Pos4, Pos5, Neg1, Neg2, Neg3, Neg4, Neg5
>   -- Values for convenience.
>   , zero, pos1, pos2, pos3, pos4, pos5, neg1, neg2, neg3, neg4, neg5
>   ) where

> import Prelude hiding ((*), (/), (+), (-), negate)
> import qualified Prelude ((+), (-))

Use the same fixity for operators as the Prelude.

> infixl 7  *, /
> infixl 6  +, -


= NumTypes =

We start by defining a class encompassing all integers with the
class function 'toNum' that converts from the type-level to a
value-level 'Num'.

> class NumTypeI n where toNum :: (Num a) => n -> a

Then we define classes encompassing all positive and negative
integers respectively. The 'PosTypeI' class corresponds to HList's
'HNat'. We also define a class for non-zero numbers (used to
prohibit division by zero).

> class (NumTypeI n) => PosTypeI n
> class (NumTypeI n) => NegTypeI n
> class (NumTypeI n) => NonZeroI n

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

We apply this trick to our classes. In our case we will elect to
append an "I" to the internal (non-exported) classes rather than
appending an "E" to the exported classes.

> class    (NumTypeI n) => NumType n
> instance (NumTypeI n) => NumType n
> class    (PosTypeI n) => PosType n
> instance (PosTypeI n) => PosType n
> class    (NegTypeI n) => NegType n
> instance (NegTypeI n) => NegType n
> class    (NonZeroI n) => NonZero n
> instance (NonZeroI n) => NonZero n

We do not have to do this for our other classes. They have the above
classes in their constraints and since the instances are complete
(not proven) a new instance cannot be defined (actually used in the
case of GHC) without overlapping instances.

Now we Define the data types used to represent integers. We begin
with 'Zero', which we allow to be used as both a positive and a
negative number in the sense of the previously defined type classes.
'Zero' corresponds to HList's 'HZero'.

> data Zero
> instance NumTypeI Zero where toNum _ = 0
> instance PosTypeI Zero
> instance NegTypeI Zero

Next we define the "successor" type, here called 'Pos' (corresponding
to HList's 'HSucc').

> data Pos n
> instance (PosTypeI n) => NumTypeI (Pos n) where
>   toNum _ = toNum (undefined :: n) Prelude.+ 1
> instance (PosTypeI n) => PosTypeI (Pos n)
> instance (PosTypeI n) => NonZeroI (Pos n)

We could be more restrictive using "data (PosTypeI n) => Pos n" but
this constraint will not be checked (by GHC) anyway when 'Pos' is
used solely at the type level.

Finally we define the "predecessor" type used to represent negative
numbers.

> data Neg n
> instance (NegTypeI n) => NumTypeI (Neg n) where
>   toNum _ = toNum (undefined :: n) Prelude.- 1
> instance (NegTypeI n) => NegTypeI (Neg n)
> instance (NegTypeI n) => NonZeroI (Neg n)


= Show instances =

For convenience we create show instances for the defined NumTypes.

> instance Show Zero where show _ = "NumType 0"
> instance (PosTypeI n) => Show (Pos n) where show x = "NumType " ++ show (toNum x :: Integer)
> instance (NegTypeI n) => Show (Neg n) where show x = "NumType " ++ show (toNum x :: Integer)


= Negation, incrementing and decrementing =

We start off with some basic building blocks. Negation is a simple
matter of recursively changing 'Pos' to 'Neg' or vice versa while
leaving 'Zero' unchanged.

> class (NumTypeI a, NumTypeI b) => Negate a b | a -> b, b -> a

> instance Negate Zero Zero
> instance (PosTypeI a, NegTypeI b, Negate a b) => Negate (Pos a) (Neg b)
> instance (NegTypeI a, PosTypeI b, Negate a b) => Negate (Neg a) (Pos b)

We define a type class for incrementing and decrementing NumTypes.
The 'incr' and 'decr' functions correspond roughly to HList's 'hSucc'
and 'hPred' respectively.

> class (NumTypeI a, NumTypeI b) => Succ a b | a -> b, b -> a

To increment NumTypes we either prepend 'Pos' to numbers greater
than or equal to Zero or remove a 'Neg' from numbers less than Zero.

> instance Succ Zero (Pos Zero)
> instance (PosTypeI a) => Succ (Pos a) (Pos (Pos a))
> instance Succ (Neg Zero) Zero
> instance (NegTypeI a) => Succ (Neg (Neg a)) (Neg a)


= Addition and subtraction =

Now let us move on towards more complex arithmetic operations. We
define a class for addition and subtraction of NumTypes.

> class (Add a b c, Sub c b a)
>    => Sum a b c | a b -> c, a c -> b, b c -> a

In order to provide instances satisfying the functional dependencies
of 'Sum', in particular the property that any two parameters uniquely
define the third, we must use helper classes.

> class (NumTypeI a, NumTypeI b, NumTypeI c) => Add a b c | a b -> c
> class (NumTypeI a, NumTypeI b, NumTypeI c) => Sub a b c | a b -> c

Adding anything to Zero gives "anything".

> instance (NumTypeI a) => Add Zero a a

When adding to a non-Zero number our strategy is to "transfer" type
constructors from the first type to the second type until the first
type is Zero. We use the 'Succ' class to do this.

> instance (PosTypeI a, Succ b c, Add a c d) => Add (Pos a) b d
> instance (NegTypeI a, Succ c b, Add a c d) => Add (Neg a) b d

We define our helper class for subtraction analogously.

> instance (NumType a) => Sub a Zero a
> instance (Succ a' a, PosTypeI b, Sub a' b c) => Sub a (Pos b) c
> instance (Succ a a', NegTypeI b, Sub a' b c) => Sub a (Neg b) c

While we cold have defined a single 'Sub' instance using negation and
addition.

] instance (Negate b b', Add a b' c) => Sub a b c

However, the constraints of such a 'Sub' instance which are not
also constraints of the 'Sub' class can complicate type signatures
(is this true or was I confused by other issues at the time?). Thus
we elect to use the lower level instances analoguous to the 'Add'
instances.

Using the helper classes we can provide an instance of 'Sum' that
satisfies its functional dependencies. We provide an instance of
'Sum' in terms of 'Add' and 'Sub'.

> instance (Add a b c, Sub c b a) => Sum a b c


= Division =

We will do division on NumTypes before we do multiplication. This
may be surprising but it will in fact simplify the multiplication.
The reason for this is that we can have a "reverse" functional
dependency for division but not for multiplication. Consider the
expressions "x / y = z". If y and z are known we can always determine
x. However, in "x * y = z" we can not determine x if y and z are
zero.

The 'NonZeroI' class is used as a constraint on the denominator 'b'
in our 'Div' class.

> class (NumTypeI a, NonZeroI b, NumTypeI c) => Div a b c | a b -> c, c b -> a

Zero divided by anything (we don't bother with infinity) equals
zero.

> instance (NonZeroI n) => Div Zero n Zero

Note that We could omit the 'NonZeroI' class completely and instead
provide the following two instances.

] instance (PosTypeI n) => Div Zero (Pos n) Zero
] instance (NegTypeI n) => Div Zero (Neg n) Zero

Going beyond zero numbers we start with a base case with all numbers
positive. We recursively subtract the denominator from nominator
while incrementing the result, until we reach the zero case.

> instance ( Sum n' (Pos n'') (Pos n)
>          , Div n'' (Pos n') n''', PosTypeI n''')
>       => Div (Pos n) (Pos n') (Pos n''')

Now we tackle cases with negative numbers involved. We trivially
convert these to the all-positive case and negate the result if
appropriate.

> instance ( NegTypeI n, NegTypeI n'
>          , Negate n p, Negate n' p'
>          , Div (Pos p) (Pos p') (Pos p''))
>       => Div (Neg n) (Neg n') (Pos p'')
> instance ( NegTypeI n, Negate n p'
>          , Div (Pos p) (Pos p') (Pos p'')
>          , Negate (Pos p'') (Neg n''))
>       => Div (Pos p) (Neg n) (Neg n'')
> instance ( NegTypeI n, Negate n p'
>          , Div (Pos p') (Pos p) (Pos p'')
>          , Negate (Pos p'') (Neg n''))
>       => Div (Neg n) (Pos p) (Neg n'')


= Multiplication =

Class for multiplication. Limited by the type checker stack. If the
multiplication is too large this error message will be emitted:

    Context reduction stack overflow; size = 20
    Use -fcontext-stack=N to increase stack size to N

> class (NumTypeI a, NumTypeI b, NumTypeI c) => Mul a b c | a b -> c

Providing instances for the 'Mul' class is really easy thanks to
the 'Div' class having the functional dependency "c b -> a".

> instance (NumTypeI n) => Mul n Zero Zero
> instance (PosTypeI p, Div c (Pos p) a) => Mul a (Pos p) c
> instance (NegTypeI n, Div c (Neg n) a) => Mul a (Neg n) c


= Functions =

Using the above type classes we define functions for various
arithmetic operations. All functions are undefined and only operate
on the type level. Their main contribution is that they facilitate
NumType arithmetic without explicit (and tedious) type declarations.

The main reason to collect all functions here is to keep the
preceeding sections free from distraction.

> negate :: (Negate a b) => a -> b
> negate _ = undefined

> incr :: (Succ a b) => a -> b
> incr _ = undefined
> decr :: (Succ a b) => b -> a
> decr _ = undefined

> (+) :: (Sum a b c) => a -> b -> c
> _ + _ = undefined
> (-) :: (Sum a b c) => c -> b -> a
> _ - _ = undefined

> (/) :: (Div a b c) => a -> b -> c
> _ / _ = undefined

> (*) :: (Mul a b c) => a -> b -> c
> _ * _ = undefined


= Convenince types and values =

Finally we define some type synonyms for the convenience of clients
of the library.

> type Pos1 = Pos Zero
> type Pos2 = Pos Pos1
> type Pos3 = Pos Pos2
> type Pos4 = Pos Pos3
> type Pos5 = Pos Pos4
> type Neg1 = Neg Zero
> type Neg2 = Neg Neg1
> type Neg3 = Neg Neg2
> type Neg4 = Neg Neg3
> type Neg5 = Neg Neg4

Analogously we also define some convenience values (all 'undefined'
but with the expected types).

> zero :: Zero  -- ~ hZero
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

