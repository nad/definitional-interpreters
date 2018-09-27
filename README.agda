------------------------------------------------------------------------
-- Code related to the paper "Total Definitional Interpreters for
-- Looping Programs"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README where

------------------------------------------------------------------------
-- Pointers to results from the paper

-- In order to more easily find code corresponding to results from the
-- paper, see the following module. Note that some of the code
-- referenced below (for instance the code related to time complexity)
-- is not discussed at all in the paper.

import README.Pointers-to-results-from-the-paper

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
-- perhaps the following ones:
--
-- * Sized types are used.
--
-- * The infinite set of uninterpreted constants has been replaced by
--   booleans, and definitions (named, unary, recursive functions)
--   are included.
--
-- * The virtual machine and the compiler include support for tail
--   calls.
--
-- * Stack space usage is analysed.

-- The syntax of, and a type system for, an untyped λ-calculus with
-- booleans and recursive unary function calls.

import Lambda.Syntax

-- A delay monad with the possibility of crashing.

import Lambda.Delay-crash

-- A definitional interpreter.

import Lambda.Interpreter

-- A type soundness result.

import Lambda.Type-soundness

-- A combination of the delay monad (with the possibility of crashing)
-- and a kind of writer monad yielding colists.

import Lambda.Delay-crash-trace

-- Virtual machine instructions, state etc.

import Lambda.Virtual-machine.Instructions

-- A virtual machine.

import Lambda.Virtual-machine

-- A compiler.

import Lambda.Compiler

-- Compiler correctness.

import Lambda.Compiler-correctness

-- A definitional interpreter that is instrumented with information
-- about the stack size of the compiled program.

import Lambda.Interpreter.Stack-sizes

-- The actual maximum stack size of the compiled program matches the
-- maximum stack size of the instrumented source-level semantics.

import Lambda.Compiler-correctness.Sizes-match

-- An example: A non-terminating program that runs in bounded stack
-- space.

import Lambda.Interpreter.Stack-sizes.Example

-- A counterexample: The trace of stack sizes produced by the virtual
-- machine is not necessarily bisimilar to that produced by the
-- instrumented interpreter.

import Lambda.Interpreter.Stack-sizes.Counterexample

-- A counterexample: The number of steps taken by the uninstrumented
-- interpreter is not, in general, linear in the number of steps taken
-- by the virtual machine for the corresponding compiled program.

import Lambda.Interpreter.Steps.Counterexample

-- A definitional interpreter that is instrumented with information
-- about the number of steps required to run the compiled program.

import Lambda.Interpreter.Steps

-- The "time complexity" of the compiled program matches the one
-- obtained from the instrumented interpreter.

import Lambda.Compiler-correctness.Steps-match
