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
  , liftStack
  )
where

import Control.Monad.Trans.Class

import qualified Data.Constraint as Constraint
import Data.Constraint ((:-))
import qualified Data.Constraint.Lifting as Constraint
import qualified Data.Constraint.Unsafe as Constraint

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
newtype Stack fs (base :: * -> *) a
  = Stack { unStack :: (ApplyAll fs base) a }


type family ApplyAll fs base
  where ApplyAll '[] base = base
        ApplyAll (f : fs) base = f (ApplyAll fs base)


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


class LiftStack fs
  where liftStack :: Monad base => base a -> Stack fs base a

instance LiftStack '[]
  where liftStack = Stack

instance (MonadTrans f, LiftStack fs, All (Constraint.Lifting Monad) fs, StackLifting fs) => LiftStack (f : fs)
  where liftStack
          :: forall base a
           . Monad base
          => base a -> Stack (f : fs) base a

        liftStack
          = case nestedLifting @ fs @ Monad @ base of
              Constraint.Sub Constraint.Dict
                ->  case underiveStack @ Monad @ fs @ base of
                      Constraint.Sub Constraint.Dict
                        ->  Stack . lift . unStack . liftStack @ fs


type family All constraint ts :: Constraint
  where All c '[] = ()
        All c (t : ts) = (c t, All c ts)


deriveStack :: c (ApplyAll fs base) :- c (Stack fs base)
deriveStack = Constraint.unsafeCoerceConstraint


underiveStack :: c (Stack fs base) :- c (ApplyAll fs base)
underiveStack = Constraint.unsafeCoerceConstraint


class StackLifting fs
  where nestedLifting
         :: c base
         => All (Constraint.Lifting c) fs :- c (Stack fs base)

instance StackLifting '[]
  where nestedLifting
         :: forall c base
          . c base
         => () :- c (Stack '[] base)

        nestedLifting
          = Constraint.Sub
              ( case deriveStack @ c @ '[] @ base of
                  Constraint.Sub Constraint.Dict -> Constraint.Dict
              )

instance StackLifting fs => StackLifting (f : fs)
  where nestedLifting
         :: forall c base
          . c base
         => All (Constraint.Lifting c) (f : fs)
              :-  c (Stack (f : fs) base)

        nestedLifting
          = Constraint.Sub
              ( case nestedLifting @ fs @ c @ base of
                  Constraint.Sub Constraint.Dict
                    ->  case underiveStack @ c @ fs @ base of
                          Constraint.Sub Constraint.Dict
                            ->  case Constraint.lifting @ c @ f @ (ApplyAll fs base) of
                                  Constraint.Sub Constraint.Dict
                                    ->  case deriveStack @ c @ (f : fs) @ base of
                                          Constraint.Sub Constraint.Dict
                                            ->  Constraint.Dict
              )
