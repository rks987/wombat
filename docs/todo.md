# Analysis of Undefined Operators, Types, and Behaviours

This document details the operators, types, and behaviors mentioned in `docs/notes.txt`, `docs/wombat.typ`, and `tests/yoneda.w` that are **not** defined in `tests/wombat.wh` or `tests/builtin.wh`.

---

## 1. Undefined Operators and Syntactic Elements

| Operator | Type/Use | Source File | Description |
| :--- | :--- | :--- | :--- |
| `if ... then ... else ...` | Flow control | `docs/wombat.typ` (lines 9, 401) | Mentioned as a fundamental suboperator sequence, but not defined in headers. |
| `^` | Prefix | `docs/notes.txt` (Note 10), `docs/wombat.typ` (line 43) | "forces success targeting" (e.g. `^expr`). |
| `^=` | Infix | `docs/notes.txt` (Note 10), `docs/wombat.typ` (line 44) | Explicitly for unification. |
| `^` | Infix | `docs/notes.txt` (Note 10), `docs/wombat.typ` (line 45) | For exponentiation / function space (e.g. `Y^X` or `X^2`). |
| `⁻¹` | Postfix | `docs/wombat.typ` (line 64) | Inverse operator for embedding pairs (e.g., `f⁻¹`). |
| `//` | Infix | `docs/wombat.typ` (line 364, 383) | Subset/refinement type constructor (e.g. `T//{...}`). |
| `∪` | Infix | `docs/notes.txt` (Note 6), `docs/wombat.typ` (line 274) | Lattice LUB (Union) operator. |
| `∩` | Infix | `docs/notes.txt` (Note 6), `docs/wombat.typ` (line 274) | Lattice GLB (Intersection) operator. |
| `⋃`, `⋂` | Prefix / Big | `docs/notes.txt` (Note 6), `docs/wombat.typ` (line 274) | "the big ones that take a set input" (set-based union/intersection). |
| `≡` | Infix | `docs/wombat.typ` (line 154), `tests/yoneda.w` (line 223) | Alias for equality proposition `=%`. |
| `@≡` | Infix | `docs/wombat.typ` (line 154) | Alias for equality proposition witness `@=%`. |
| `=%` | Infix | `docs/wombat.typ` (line 154), `tests/yoneda.w` (line 48) | Standalone equality proposition operator. |
| `@=%` | Infix | `docs/wombat.typ` (line 154), `tests/yoneda.w` (line 83) | Standalone equality proposition witness operator. |
| `@∀%` | Prefix | `tests/yoneda.w` (line 86, 87) | Universal quantification witness constructor (e.g. `@∀%{...}`). |
| `@∃%` | Prefix | Conceptual | Existential quantification witness constructor. |
| `Isa%` | Infix | `docs/wombat.typ` (line 350) | Infix subtyping/inclusion proposition operator (defined as a function in headers, not an operator). |
| `==` | Infix | `docs/wombat.typ` (line 155), `tests/yoneda.w` (line 80, 402) | Alias for boolean comparison `=?`. |
| `/` | Infix | `docs/wombat.typ` (line 242), `tests/yoneda.w` (line 402) | Division (e.g. `n/1` or `f/k`), which returns a `Rational`. |
| `∅` | Constant | `docs/wombat.typ` (line 328) | Empty set literal/symbol (e.g. `Union(∅)`). |

---

## 2. Undefined Types

| Type | Classification | Source File | Description |
| :--- | :--- | :--- | :--- |
| `Nat` | Base Type | `docs/notes.txt` (Note 8), `docs/wombat.typ` (line 346, 382), `tests/yoneda.w` (line 231) | Natural numbers. Used extensively in comments and examples but never declared. |
| `Int` | Base Type | `docs/wombat.typ` (line 83, 242) | Integer type. |
| `Rational` | Base Type | `docs/wombat.typ` (line 242, 403) | Rational number type. |
| `String` | Base Type | `docs/wombat.typ` (line 346) | String type. |
| `Unit` | Base Type | `docs/wombat.typ` (line 400), `tests/yoneda.w` (line 275) | Unit type (only referenced, never declared as `Unit : Type`). |
| `UnionType` | Type Constructor | `docs/notes.txt` (Note 6), `docs/wombat.typ` (line 276) | The actual type backing a `Union` of types (different from the `Union` function itself). |
| `IntersectionType` | Type Constructor | `docs/notes.txt` (Note 6), `docs/wombat.typ` (line 276) | The actual type backing an `Intersection` of types. |
| `~>` | Arrow | `docs/wombat.typ` (line 49) | Partial action type constructor (impurity/effects). |
| `~>>` | Arrow | `docs/wombat.typ` (line 49) | Total action type constructor. |
| `<=>>` | Arrow | `docs/wombat.typ` (line 59), `tests/yoneda.w` (line 33, 69) | Embedding (invertible procedure) type constructor. |
| `Vector` | Constructor | `docs/wombat.typ` (line 77) | Dependent vector type (`Vector(length, Type)`). |
| `TimeOrder` | Base Type | `docs/wombat.typ` (line 423) | Used for controlling evaluation order in Action calls. |
| `Category` | Structure Type | `tests/yoneda.w` (line 30) | Category structure definition. |
| `Functor` | Structure Type | `tests/yoneda.w` (line 90) | Functor structure definition. |
| `NatTran` / `Natran` | Structure Type | `tests/yoneda.w` (lines 101, 127) | Natural transformation structure definition. |
| `FunctorCat` | Category Constructor | `tests/yoneda.w` (line 110) | Functor category constructor type. |
| `Isomorphism%` | Prop Constructor | `tests/yoneda.w` (line 120) | Prop type asserting an isomorphism between morphisms. |
| `YonedaConstruction` | Structure Type | `tests/yoneda.w` (line 227) | Auxiliary structure for the Yoneda Lemma. |

---

## 3. Undefined Behaviours and Conformance Traits

| Behaviour / Trait | Description | Source File |
| :--- | :--- | :--- |
| `Inductive` | Needed for induction constraints (e.g. for `Nat`). | `docs/notes.txt` (Note 8) |
| `Combinable` | Used for combining lists/procedures when non-distinct. | `docs/wombat.typ` (line 111) |
| `Distinguishable` | Used to assert elements can be compared/distinguished. | `docs/wombat.typ` (line 110, 115) |
| `Semigroup` | Algebraic structure with associative `op`. | `docs/wombat.typ` (line 168) |
| `Monoid` | Algebraic structure extending `Semigroup` with a `unit`. | `docs/wombat.typ` (line 178) |

---

## 4. Undefined Functions, Methods, and Properties

| Name | Type | Source File | Description |
| :--- | :--- | :--- | :--- |
| `combine` | Function | `docs/wombat.typ` (line 104) | Resolves the union of list elements or applies `Combinable` behaviors. |
| `map` | Function | `docs/wombat.typ` (line 353) | Standard list mapping function. |
| `.len` | Property | `docs/wombat.typ` (line 78) | Retrieves list or vector length. |
| `.to`, `.rev` | Properties | `docs/wombat.typ` (line 62) | Accesses forward/reverse procedures in an embedding (`<=>>`). |
| `.at(...)` | Method | `tests/yoneda.w` (lines 56, 168, 206) | Instantiates a universal quantifier (e.g., `allIso.at(A)`). |
| `.pickOne` | Method | `tests/yoneda.w` (lines 132, 168) | Pulls a witness from an existential quantifier. |
| `.given(...)` | Method | `tests/yoneda.w` (line 197) | Feeds constraints/arguments to a witness/proposition. |
| `firstCase` | Function | `tests/builtin.wh` (line 115) | Used in the definition of `Totalise` in `builtin.wh` but never defined itself. |
| `toForAll%` | Function | `tests/yoneda.w` (lines 56, 73, 191) | Builds a universal quantification witness. |
| `toImplies%` | Function | `tests/yoneda.w` (lines 130, 160) | Builds an implication witness. |
| `comp` | Function | `tests/yoneda.w` (line 21) | Function composition helper (defined in `yoneda.w` but not globally in headers). |
| `Op` | Function | `tests/yoneda.w` (line 52) | Creates the opposite category. |
| `TypeCat` | Constant / Cat | `tests/yoneda.w` (line 66) | Category of Wombat types and pure total functions. |
| `HomFunctor` | Function | `tests/yoneda.w` (line 180) | Hom-functor constructor. |
| `yoneda` | Function / Theorem | `tests/yoneda.w` (line 223) | The Yoneda lemma representation. |
| `debug.log` | Function | `docs/wombat.typ` (line 83) | Logging helper. |

---

## 5. Undefined Proof / Compiler Directives

In `tests/yoneda.w`, inline compiler tactics and axioms are introduced inside `{% ... %}` blocks (which are also not parsed or defined by `wombat.wh`'s commented-out `%` tokens):

- `{% apply <name> %}` (e.g., `apply comp`, `apply id`, `apply 2 {}`, `apply Isomorphism%`)
- `{% axiom <name> %}` (e.g., `axiom unelaborate`, `axiom componentsEqual`, `axiom equalClosures`, `axiom combineInnerForAll`)
- `{% reverseApply <name> %}` (e.g., `reverseApply Isomorphism%`)
