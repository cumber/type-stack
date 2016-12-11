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
           , ScopedTypeVariables
           , TypeApplications
           , TypeFamilyDependencies
           , TypeOperators
           , UndecidableInstances
           , UndecidableSuperClasses
  #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module Type.Stack
  ( Stack
  , type (@@)
  , liftStackBase
  )
where

import Control.Monad.Trans.Class

import qualified Data.Constraint as Constraint
import Data.Constraint ((:-))
import qualified Data.Constraint.Lifting as Constraint
import qualified Data.Constraint.Unsafe as Constraint

import Data.Functor.Identity (Identity)

import Data.Kind (Constraint)


{-|
Stacking a list of transfomers is just their composition applied to
'Identity'.

These types are equivalent:

@
Stack [MaybeT, ReaderT Int]
MaybeT (ReaderT Int Identity)
@
-}
type family Stack fs = r | r -> fs
  where Stack '[] = Identity
        Stack (f : fs) = f (Stack fs)

newtype StackBase fs (base :: * -> *) a
  = StackBase { unStack :: (ApplyNested fs base) a }


type family ApplyNested fs base
  where ApplyNested '[] base = base
        ApplyNested (f : fs) base = f (ApplyNested fs base)


{-|
An infix operator for 'Stack'ing a list of transformers and applying
the result to a type.

These types are equivalent:

@
[ReaderT Int, MaybeT] @@ Bool
Stack [ReaderT Int, MaybeT] Bool
ReaderT Int (MaybeT Identity) Bool
@
-}
type fs @@ a = Stack fs a


class LiftStackBase fs
  where liftStackBase :: Monad base => base a -> StackBase fs base a

instance LiftStackBase '[]
  where liftStackBase = StackBase

instance (MonadTrans f, LiftStackBase fs, All (Constraint.Lifting Monad) fs, NestedLifting fs) => LiftStackBase (f : fs)
  where liftStackBase
          :: forall base a
           . Monad base
          => base a -> StackBase (f : fs) base a

        liftStackBase
          = case nestedLifting @ fs @ Monad @ base of
              Constraint.Sub Constraint.Dict
                ->  case underiveStack @ Monad @ fs @ base of
                      Constraint.Sub Constraint.Dict
                        ->  StackBase . lift . unStack . liftStackBase @ fs


type family All constraint (ts :: [(* -> *) -> (* -> *)]) = (r :: Constraint) | r -> ts
  where All c '[] = ()
        All c (t : ts) = (c t, All c ts)


deriveStack :: c (ApplyNested fs base) :- c (StackBase fs base)
deriveStack = Constraint.unsafeCoerceConstraint


underiveStack :: c (StackBase fs base) :- c (ApplyNested fs base)
underiveStack = Constraint.unsafeCoerceConstraint


class NestedLifting fs
  where nestedLifting
         :: c base
         => All (Constraint.Lifting c) fs :- c (StackBase fs base)

instance NestedLifting '[]
  where nestedLifting
         :: forall c base
          . c base
         => () :- c (StackBase '[] base)

        nestedLifting
          = Constraint.Sub
              ( case deriveStack @ c @ '[] @ base of
                  Constraint.Sub Constraint.Dict -> Constraint.Dict
              )

instance NestedLifting fs => NestedLifting (f : fs)
  where nestedLifting
         :: forall c base
          . c base
         => All (Constraint.Lifting c) (f : fs)
              :-  c (StackBase (f : fs) base)

        nestedLifting
          = Constraint.Sub
              ( case nestedLifting @ fs @ c @ base of
                  Constraint.Sub Constraint.Dict
                    ->  case underiveStack @ c @ fs @ base of
                          Constraint.Sub Constraint.Dict
                            ->  case Constraint.lifting @ c @ f @ (ApplyNested fs base) of
                                  Constraint.Sub Constraint.Dict
                                    ->  case deriveStack @ c @ (f : fs) @ base of
                                          Constraint.Sub Constraint.Dict
                                            ->  Constraint.Dict
              )
