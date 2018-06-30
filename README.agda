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

-- Some developments based on "Operational Semantics Using the
-- Partiality Monad" by Danielsson.
--
-- These developments to a large extent mirror developments in
-- "Coinductive big-step operational semantics" by Leroy and Grall.
--
-- The main differences compared to those two pieces of work are
-- perhaps the use of sized types, and the analysis of stack space
-- usage.

-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants.

import Lambda.Syntax

-- A delay monad with the possibility of crashing.

import Lambda.Delay-crash

-- A definitional interpreter.

import Lambda.Interpreter

-- A type soundness result.

import Lambda.Type-soundness

-- A combination of the delay monad (with the possibility of crashing)
-- and a kind of writer monad yielding colists.

import Lambda.Delay-crash-colist

-- A virtual machine.

import Lambda.Virtual-machine

-- A compiler.

import Lambda.Compiler

-- Compiler correctness.

import Lambda.Compiler-correctness

-- A definitional interpreter that is annotated with information about
-- the stack size of the compiled program.

import Lambda.Interpreter.Annotated

-- The actual maximum stack size of the compiled program matches the
-- maximum stack size of the annotated source-level semantics.

import Lambda.Compiler-correctness.Sizes-match

------------------------------------------------------------------------
-- Other code

-- A small language with lambdas, general recursion, natural numbers,
-- references and IO.

import Lambda
