/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
import Corpus.Data.List.Basic
import Corpus.Data.Option.Basic

/-!
# corpus

A formal mathematics library whose admission is decisive checks — kernel
verification and axiom-profile legibility — never the standing of who
produced a contribution.

Every declaration in this library carries a declared axiom profile, and the
audit (`Corpus/Audit.lean`) recomputes each profile from the kernel
environment and fails on any mismatch. Same-statement replacements are
admitted exactly when they are measurably better — today's measured axis:
a strictly smaller axiom profile.

This root imports the library's contents; `Counterexamples/` is the
negative-space library and builds as its own target.
-/
