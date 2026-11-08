# Third-party dependencies

The formalization uses Lean4.35.0 and the dependencies pinned in `verification/lean/lake-manifest.json`. Dependency source and build caches are not bundled; Lake downloads their recorded revisions on reproduction.

- **mathlib4**: `https://github.com/leanprover-community/mathlib4.git`, revision `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0). Apache License2.0; original text copied unchanged in `licenses/mathlib-APACHE2.txt`.
- **fixed-point-theorems**: `https://github.com/harfe/fixed-point-theorems-lean4.git`, revision `93a3eed3364281a9dbf9652bb52356a8db65057c`. Copyright(c)2026 harfe; MIT license copied unchanged in `licenses/fixed-point-theorems-MIT.txt`. The chore proof imports its proved Kakutani theorem. The transitive axiom audit applies to project declarations using this dependency too.

Other transitive packages, their source URLs and exact revisions are listed in the Lake manifest. These notices describe dependency licensing; they do not assign a license to the authors' manuscript or project sources.
