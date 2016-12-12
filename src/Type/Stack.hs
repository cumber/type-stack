{-|
Module      : Type.Stack
Description : Type level list of transformers as a transformer
Copyright   : © Benjamin Mellor 2016
License     : BSD-style (see the file LICENSE)

Maintainer  : ben@smokingkangaroo.com
Stability   : experimental
Portability : portable

Uses type-level lists to represent a stack of transformers instead of
nesting them. This can lead to type signatures with fewer parentheses,
and cleanly separates the transformer stack from the type it is ultimately
applied to.

This documentation refers to anything of kind @(* -> *) -> (* -> *)@ as a
"transformer". Most usefully these will be monad transfomers, but not all
tools in this library require transformers to be instances of 'MonadTrans'.
-}

{-# LANGUAGE ConstraintKinds
           , DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , InstanceSigs
           , MultiParamTypeClasses
           , PolyKinds
           , RoleAnnotations
           , ScopedTypeVariables
           , StandaloneDeriving
           , TypeApplications
           , TypeFamilyDependencies
           , TypeOperators
           , UndecidableInstances
           , UndecidableSuperClasses
  #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module Type.Stack
  ( ApplyAll
  , All
  , type (++)
  , Stack (..)
  , LiftStack (..)
  , stackUp
  , stackDown
  , deriveStack
  , StackLifting (..)
  )
where

import Control.Monad.Trans.Class

import qualified Data.Constraint as Constraint
import Data.Constraint ((:-), (\\))
import qualified Data.Constraint.Lifting as Constraint
import qualified Data.Constraint.Unsafe as Constraint

import Data.Kind (Constraint)


{-|
Apply each of a list of @k -> k@ type constructors to a @base :: k@. Basically
a type level foldr.
 -}
type family ApplyAll fs base
  where ApplyAll '[] base = base
        ApplyAll (f : fs) base = f (ApplyAll fs base)


{-|
A @Stack@ is a newtype wrapper around a set of transformers applied to a base
@* -> *@ type and then finally to a result type.

Because an applied set of transformers is itself a valid @* -> *@ "base" type,
a given value could be wrapped up in @Stack@ wrappers of many possible types;
the choice decides what the "base" of the stack is (treated as an opaque
monolithic @* -> *@ type), and gives all the outer layers as a type-level list
where they can be individually manipulated.

It would be possible to work directly with the wrapped value if we could use
partial type family injectivity, where knowing the result plus some of the
 arguments determines the other arguments ("type C injectivity" according to
the breakdown on <https://ghc.haskell.org/trac/ghc/wiki/InjectiveTypeFamilies>).
Instead the @Stack@ newtype effectively tags a type resulting from 'ApplyAll'
with the arguments to the type family.

These types are isomorphic:

@
Stack [MaybeT, ReaderT Int, StateT Bool] Identity
Stack [MaybeT, ReaderT Int] (StateT Bool Identity)
Stack [MaybeT] (ReaderT Int (StateT Bool Identity))
Stack '[] (MaybeT (ReaderT Int (StateT Bool Identity)))
@

All of them are newtype wrappers around:

@
MaybeT (ReaderT Int (StateT Bool Identity))
@

Any @* -> *@ instance on the transformer stack (i.e. polymorphic in the @a@
parameter of the final type) can be lifted to the @Stack@-wrapped version
using 'deriveStack'. Pre-written 'Functor', 'Applicative', and 'Monad' instances
are provided here for convenience, since the usual use-case of @Stack@ is
expected to be for monad transformer stacks. The source code provides an example
of using 'deriveStack' to implement whatever instances are required.
-}
newtype Stack fs (base :: * -> *) a
  = Stack { unstack :: ApplyAll fs base a }

deriving instance Show (ApplyAll fs base a) => Show (Stack fs base a)


instance Functor (ApplyAll fs base) => Functor (Stack fs base)
  where fmap = fmap \\ deriveStack @ Functor @ fs @ base

instance Applicative (ApplyAll fs base) => Applicative (Stack fs base)
  where pure = pure \\ deriveStack @ Applicative @ fs @ base
        (<*>) = (<*>) \\ deriveStack @ Applicative @ fs @ base

instance Monad (ApplyAll fs base) => Monad (Stack fs base)
  where return = return \\ deriveStack @ Monad @ fs @ base
        (>>=) = (>>=) \\ deriveStack @ Monad @ fs @ base
        (>>) = (>>) \\ deriveStack @ Monad @ fs @ base
        fail = fail \\ deriveStack @ Monad @ fs @ base


{-|
A given stack of monad transformers is itself a monad transformer
-}
instance LiftStack fs => MonadTrans (Stack fs)
  where lift = liftStack


{-|
Type-level list concatenation
-}
type family xs ++ ys
  where '[] ++ ys = ys
        (x : xs) ++ ys = x : (xs ++ ys)

{-|
Pull layers from the base of a 'Stack' up into the stack; the proxy argument
controls how many levels will be pulled up.
-}
stackUp
 :: (ApplyAll (fs ++ gs) base ~ ApplyAll fs (ApplyAll gs base))
 => proxy gs -> Stack fs (ApplyAll gs base) a -> Stack (fs ++ gs) base a
stackUp _ = Stack . unstack


{-|
Push layers from the stack of a 'Stack' down into the base; the proxy argument
controls how many levels will be pulled up.
-}
stackDown
 :: (ApplyAll (fs ++ gs) base ~ ApplyAll fs (ApplyAll gs base))
 => proxy gs -> Stack (fs ++ gs) base a -> Stack fs (ApplyAll gs base) a
stackDown _ = Stack . unstack


{-|
A class providing 'liftStack', which conceptually is just 'lift' composed together
sufficiently to work on any level of a monad transformer stack. However it
returns its result wrapped in a 'Stack'; this can either be unwrapped or can be
the outer layer of your monad stack.

If you're just using 'Stack' to manage a monad transformer stack, then you can
ignore the superclass 'StackLifting' and the fact that this is a class;
"morally" this is just:

@
liftStack :: (All MonadTrans fs, Monad base) => base a -> Stack fs base a
@
-}
class StackLifting Monad fs => LiftStack fs
  where liftStack :: Monad base => base a -> Stack fs base a

instance LiftStack '[]
  where liftStack = Stack

instance (MonadTrans f, Constraint.Lifting Monad f, LiftStack fs)
      => LiftStack (f : fs)
  where liftStack
          :: forall base a
           . Monad base
          => base a -> Stack (f : fs) base a

        liftStack
          = Stack . lift . unstack . liftStack @ fs
              \\ underiveStack @ Monad @ fs @ base
              \\ stackLifting @ Monad @ fs @ base


{-|
Generate a constraint that all elements of a type list meet a given constraint
-}
type family All constraint ts :: Constraint
  where All c '[] = ()
        All c (t : ts) = (c t, All c ts)

{-|
Anything thing that the stack of transfomers (applied to @base@) is an instance
of, 'Stack fs base' is also an instance of.

(Most are not implemented as real instances; this allows you to generate the
'Constraint.Dict' as if they __were__ implemented)
-}
deriveStack :: c (ApplyAll fs base) :- c (Stack fs base)
deriveStack = Constraint.unsafeCoerceConstraint


underiveStack :: c (Stack fs base) :- c (ApplyAll fs base)
underiveStack = Constraint.unsafeCoerceConstraint


{-|
If all the elements in the stack of a 'Stack' lift through @c@, and @c base@
holds, then @c@ also holds for the 'Stack'.
-}
class All (Constraint.Lifting c) fs => StackLifting c fs
  where stackLifting :: c base :- (c (Stack fs base))

instance StackLifting c '[]
  where stackLifting :: forall base. c base :- c (Stack '[] base)
        stackLifting
          = Constraint.Sub $ Constraint.Dict \\ deriveStack @ c @ '[] @ base

instance (Constraint.Lifting c f, StackLifting c fs) => StackLifting c (f : fs)
  where stackLifting
         :: forall base
          . c base :- (c (Stack (f : fs) base))

        stackLifting
          = Constraint.Sub
              ( Constraint.Dict
                  \\ deriveStack @ c @ (f : fs) @ base
                  \\ Constraint.lifting @ c @ f @ (ApplyAll fs base)
                  \\ underiveStack @ c @ fs @ base
                  \\ stackLifting @ c @ fs @ base
              )
