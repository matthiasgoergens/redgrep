{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, OverlappingInstances #-}

module Cursor where
import Types
import qualified Data.Set as Set
import Data.Set (Set)

data Cursor f x y where
    -- = before sym, we need (Eps Sym) and (Nil SymError), too.
    Before :: Cursor f x y

    AltL :: f (Cursor f l le) -> Cursor f (Alt l r) (Cut le re)
    AltR :: f (Cursor f r re) -> Cursor f (Alt l r) (Cut le re)
    AltE :: f (Cursor f l le) -> f (Cursor f r re) -> Cursor f (Alt l r) (Cut le re)

    Cut :: f (Cursor f l le) -> f (Cursor f r re) -> Cursor f (Cut l r) (Alt le re)
    CutLE :: f (Cursor f l le) -> Cursor f (Cut l r) (Alt le re)
    CutRE :: f (Cursor f r re) -> Cursor f (Cut l r) (Alt le re)

    -- hmm, something's missing.
    SeqL :: f (Cursor f l le) -> Cursor f (Seq l r) (Alt le (Seq l re))
    SeqR :: f (Cursor f r re) -> Cursor f (Seq l r) (Alt le (Seq l re))
    
    Not :: f (Cursor f x e) -> Cursor f e x

    -- Not quite sure..
    Eps :: f (Result x) -> Cursor f x y
    Nil :: f (Result y) -> Cursor f x y

data Result x = Weird
    deriving (Eq, Ord, Show)

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

