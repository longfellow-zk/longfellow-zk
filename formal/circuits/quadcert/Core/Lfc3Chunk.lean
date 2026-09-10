/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import quadcert.Core.Lfc3

/-!
# Stating an expansion chunk so `rfl` can close it

A generated chunk theorem has the shape

```
layer.expandChunk gBound tree count start = .ok (terms, stop)
```

and `by rfl` on it blew the native stack on ECDSA2's layer 10, chunk 7 — 709 terms, while its
siblings at 1,024 terms passed. The reduction itself is *fine*: `expandChunk` computes the
right 709 terms and the right stop cursor, and `rfl` closes both

```
(layer.expandChunk …).toOption.map (·.1) = some terms
(layer.expandChunk …).toOption           = some (terms, stop)
```

It is only the direct `_ = .ok (…)` form that fails, so this is `isDefEq`'s unification strategy
on that shape and not the cost of the computation. Raising `maxRecDepth` does not help — it
turns the error into an actual segfault.

Stating the chunk through `toOption` and converting keeps the theorem the composition lemma
wants while giving `rfl` the shape it can handle.
-/

namespace Quadcert.Lfc3

/-- `toOption` determines the `Except`: `none` is the only image of an error. -/
theorem eq_ok_of_toOption {ε α : Type} {e : Except ε α} {v : α}
    (h : e.toOption = some v) : e = .ok v := by
  cases e with
  | error _ => exact absurd h (by simp [Except.toOption])
  | ok a => simp only [Except.toOption, Option.some.injEq] at h; rw [h]

end Quadcert.Lfc3
