------------------------------------------------------------------------
-- Code related to definitional interpreters
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README where

------------------------------------------------------------------------
-- Responses to some challenges from Ancona, Dagnino and Zucca

-- The syntax of a toy programming language that only supports
-- allocation and deallocation of memory.

import Only-allocation

-- Definitional interpreters can model systems with bounded space.

import Bounded-space

-- Upper bounds of colists containing natural numbers.

import Upper-bounds

-- Definitional interpreters can model systems with unbounded space.

import Unbounded-space

------------------------------------------------------------------------
-- Other code

-- A small language with lambdas, general recursion, natural numbers,
-- references and IO.

import Lambda
