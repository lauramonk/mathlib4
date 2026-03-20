/-
Copyright (c) 2025 Laura Monk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laura Monk and Freddie Nash
-/

module

public import Mathlib.Combinatorics.Graph.Dart
public import Mathlib.Combinatorics.GraphLike.Symm

/-!
In this file we make `Graph` an instance of `GraphLike`.
-/

@[expose] public section

variable {α β : Type*}

--- TODO: instance : SymmGraphLike α (Graph α β) where
