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
-- An example involving a simple λ-calculus

-- Some developments from "Operational Semantics Using the Partiality
-- Monad" by Danielsson, implemented using the delay monad.
--
-- These developments to a large extent mirror developments in
-- "Coinductive big-step operational semantics" by Leroy and Grall.

-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants.

import Lambda.Syntax

-- A definitional interpreter.

import Lambda.Interpreter

-- A type soundness result.

import Lambda.Type-soundness

-- A virtual machine.

import Lambda.Virtual-machine

-- A compiler.

import Lambda.Compiler

-- Compiler correctness.

import Lambda.Compiler-correctness

------------------------------------------------------------------------
-- Other code

-- A small language with lambdas, general recursion, natural numbers,
-- references and IO.

import Lambda
