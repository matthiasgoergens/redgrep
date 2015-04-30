{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, OverlappingInstances #-}

module Cursor where
import Types
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Result as R
import Result (Result())


-- Cursor will need to come with a history (ie partial result)
-- we will merge history (eg via `const') for equal cursors.
-- But we'll need to stick the history somewhere.
-- Can we stick it in the f?
data Cursor f x y where
    -- = before sym, we need (Eps Sym) and (Nil SymError), too.
    Before :: Cursor f x y

    Alt :: f (Cursor f l le) -> f (Cursor f r re) -> Cursor f (Alt l r) (Cut le re)
    Cut :: f (Cursor f l le) -> f (Cursor f r re) -> Cursor f (Cut l r) (Alt le re)

    Seq :: f (Cursor f l le) -> f (Cursor f r re) -> Cursor f (Seq l r) (Alt le (Seq l re))
    
    Not :: f (Cursor f x e) -> Cursor f e x
    Rep :: f (Cursor f x e) -> Cursor f (Rep x) (Seq (Rep x) e) 

    -- Not quite sure..  We need to keep Results (== history) and Cursors separate.
    -- Cursors are keys, Results are values.
    -- Eps == After.
    -- Eps :: f () -> Cursor f x y
    Eps :: f (Result x) -> Cursor f x y
    -- Nil :: f () -> Cursor f x y
    Nil :: f (Result y) -> Cursor f x y

{-
data ReC x where
    SymC :: ReC Sym
    AltC :: ReC x -> ReC y -> ReC (Alt x y)
    CutC1 :: ReC x -> ReC (Cut x y)
    CutC2 :: ReC y -> ReC (Cut x y)
    -- magic here!
    SeqCL :: ReC x -> ReC (Seq x y)
    SeqCR :: ReC y -> ReC (Seq x y)
    RepC :: ReC x -> ReC (Rep x)
    -- change to alt..
    NotC :: ReS1 x -> ReC (Not x)
    -- or ReS1 x?
    EpsC :: x -> ReC x
    NilC :: ReC x
-}

