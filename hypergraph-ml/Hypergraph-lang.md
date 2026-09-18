
## Goal of the language

The goal of this language is to describe information using directed hypergraphs. Hypergraphs are a more generalized graph. Its behavior is more sophisticated than formats like `JSON`, `TOML`, `YAML` etc. but fundamentally it's goal does is not to perform computation.

To make defining hypergraphs easier, we will first define the following notation:
### Language objects

##### Structs

Structs are basically containers of various types:

```hg
struct myCar<T,B> {
	axel: T,
	gear: B,
	model_no: Int
}
```

structs can be initialized in the order of their parameters:
```hg
struct Car {
	wheels: Int,
	weight: Decimal
}

let car: Car = Car(4, 1000.0)

```

##### Enums

Enums are essentially a list of possible, named members:
```hg
enum Option<A> {
	Some(A),
	None
}
```

Enums can be initialized by using the syntax `Enum::status`
```hg
let nothing: Option<Int> = Option::None
```

The type `Option<T>` is special and does not need to have the `Option::` identifier.
##### Sets

Sets are containers containing any items in the language
```hg
let s: Set<Int> = {1}
```

You can put anything in a set, for example a struct, or an enum:
```hg
enum Bye {
	Cya
}
struct Hi {
	bye: Bye,
}

let s: Set<Hi> = {Hi(Bye::Cya)}
```
##### Lists

Lists are ordered containers. They use square brackets:

```hg
let values: List<Int> = [1, 2, 1]
let empty: List<Int> = []
```

As with sets, lists may contain any language object and their element type may
be a sum:

```hg
let mixed: List<Int + String> = [1, "one", 2, "two"]
let nested: List<List<Int>> = [[1, 2], [3]]
```
##### Edges

 There are 2 types of edges, directed-edges and undirected-edges
 All edges have 3 components, a head, a tail and a payload.

The following are two equivalent directed edges:
```hg
let ht: Edge<Int, Decimal, String> = {1} -["Payload"]-> {1.1}
let ht: Edge<Int, Decimal, String> = {1.1} <-["Payload"]- {1}
```

Notice how the head and tail are sets of items, this is what defines the 
directed hyperedge of the hypergraph. 

The first type parameter `Int` defines the tail of the edge, `Decimal` defines the head of the edge. The final type `String` defines the payload type. Both the head and the tail values are embedded in a set. The payload type is also implicitly embedded in an `Option` type.

You can imagine the Edge type being the following struct:
```
struct Edge<T,H,P> {
    tail: Set<T>,
    head: Set<H>,
    payload: Option<P>,
}
```

Since the payload type is embedded in `Option`, it is also possible to define an edge without an edge payload. This works for both edge types:
```hg
let ud: Edge<Int, Decimal, !> = {1} -> {1.1}
```

Undirected edges are special, they can be represented by a set of two directed edges, both in inverse directions, but they are not equivalent, since 'side surgery' works on `UndirectedEdge`s (see section Operations on Edges).

An undirected edge is very similar in syntax except for the arrows on both sides (`<-[...]->`) in both directions:
```hg
let ud: UndirectedEdge<Int, Decimal, String> = {1} <-["Payload"]-> {1.1}
```

An `UndirectedEdge<T,H,P>` can be converted to `Set<Edge<T,H,P> + Edge<H,T,P>>`.

When the expected set accepts only directed edges, the conversion inserts both orientations as separate members. A `Graph<T,H,P>` keeps the undirected edge as one member.

```hg
let a: Edge<Int, Decimal, Bottom> = {1} -> {2.0}
let b: UndirectedEdge<Int, Decimal, Bottom> = {2} <-> {3.0}

// b contributes one directed edge in each direction.
let g: Set<Edge<Int,Decimal,Bottom> + Edge<Decimal,Int,Bottom>> = {a, b}
```

The type coercion is also irreversible, meaning that for example, `g` here no longer has any knowledge of the original `UndirectedEdge`.  
##### Graphs

Graphs are an emergent object, meaning that they aren't really a separate object from the previous ones. They are of the type `Graph<T,H,P> = Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>`:

```hg
let a: Edge<Int, Int, Bottom> = {1} -> {2}
let b: Edge<Int, Int, Bottom> = {2} -> {3}
let c: Edge<Int, Int, Bottom> = {3} -> {1}

let g: Graph<Int, Int, Bottom> = {a, b, c}
```

### Operations

##### Operations on Sets

There are 3 fundamental operations on sets
	- Union:  `|`
	- Intersection: `&`
	- Difference: `-`

These can be applied to sets and will behave like set operations:
```hg
let setA: Set<Int> = {1, 2, 3}
let setB: Set<Int> = {2, 3, 4}

let union: Set<Int> = setA | setB // {1, 2, 3, 4}
let intersection: Set<Int> = setA & setB // {2, 3}
let difference: Set<Int> = setA - setB // {1}
```

It is also possible to do this in-place:
```hg
let A: mut Set<Int> = {2,5,7}
A |= {3}   // {2, 3, 5, 7} 
A &= {5,7} // {5, 7}
A -= {7}   // {5}
```

##### Operations on Edges

Operations on `Edge`s are similar to operations on sets, however unlike sets, operations on edge
only work with other edges. The operations perform edge 'side surgery' meaning the set operations are applied to the tail/head sets of the edge.

```hg
let edgeA: mut Edge<Int,Int,Bottom> = {1} -> {2}
let edgeB: Edge<Int,Int,Bottom> = {3} -> {4}

let edgeC: Edge<Int,Int,Bottom> = edgeA | edgeB // {1, 3} -> {2, 4}
edgeA |= edgeB // same as edgeC, but now in-place, so edgeA is now equivalent to edgeC
```

Note that this also works for type `UndirectedEdge` but not a `Set<Edge<...>+Edge<...>>` containing two identical directed edges in opposite directions, which could represent an undirected edge.

If an Edge has a payload, then side surgery is only possible if the payload between the two edges of the binary operation is equal. 

```hg
let edgeA: mut Edge<Int,Int,String> = {1} -["Bob"]-> {2}
let edgeB: Edge<Int,Int,String> = {3} -["Bob"]-> {4}
let edgeC: Edge<Int,Int,String> = {3} -["Alice"]-> {4}

// allowed
edgeA |= edgeB
// not allowed: the payload values differ
edgeA |= edgeC
```


### Type System

##### Type Algebra

This subsection defines the mathematical background, not additional language rules.

`ACUIhE` uses finite terms of the form:

```typesystem
t ::= 0 | constant | variable | t + t | h_l(t) | E(t)
```

Here `0` is `Bottom`. Each fixed label `l` names a homomorphism; substitution replaces variables only.

The following laws hold for arbitrary terms and every label `l`:

```typesystem
(a+b)+c = a+(b+c)             a+b = b+a
a+0 = a                     a+a = a
h_l(a+b) = h_l(a)+h_l(b)     h_l(0) = 0
E(0) = 0
E(a) = E(b)  iff  a = b
```

Terms are identified by the least congruence satisfying these laws; the resulting quotient is the free algebra. No additional equations are assumed.

The derived order is `a <=_+ b` iff `a+b = b`. The language rules specify where this order permits assignment.

With decidable symbol equality, the canonical graph normal form decides equality of terms.

##### The type family `O_i(A₁, ..., Aₙ) = E(c_i + h₁(A₁) + ... + hₙ(Aₙ))`

The constant `c_i` identifies the declaration, and each homomorphism label identifies a field within it:

```hg
struct Example<T,A> {
    a: String,
    b: T,
    c: A,
}
```

Its type is `Example<T,A> = E(c_Example + h_a(String) + h_b(T) + h_c(A))`.

Labels are scoped to their declaration. A field of type `Bottom` is still required.

Enums label their payloads by variant and retain a constant tag for each variant:

```typesystem
Option<A> = E(c_Option + c_None + c_Some + h_Some(A))
```

The variant tags belong to `Option`; a value selects exactly one variant.

Applying `E` does not generally preserve type inclusion.

##### Distributivity and type `Eq`

Collection types use a constant tag to preserve their identity when the element type is `Bottom`:

```typesystem
Set<A> = c_Set + h_Set(A)
List<A> = c_List + h_List(A)
```

The tags are distinct constants. These definitions give the distributive equations:

```typesystem
Set<A+B> = Set<A>+Set<B>
List<A+B> = List<A>+List<B>
```

In `Set<Int + String>`, the sum specifies the types allowed for each element. An element of type `T` fits `Set<A>` when `T <=_+ A`; the same rule applies to lists.

This does not allow a scalar to acquire a sum type:

```hg
let value: Int + String = 1 // rejected
```

These collection literals are valid:

```hg
let mixed: Set<Int + String> = {1, "one"}
let integers: Set<Int + String> = {1, 2}
let sequence: List<Int + String> = [1, "one", 2]
```

An empty list is inferred as `List<Bottom>` unless its expected type supplies another element type. The same rule applies to empty sets.

`Eq(A)` means values of `A` support equality; the compiler derives it. Equal types do not imply equal values.

`Eq(A+B)` holds exactly when every summand supports equality. Equality of a compound value depends on its stored values.

A set whose element type includes an edge type is treated as a graph. `Eq` is not derived for the graph itself.

An edge supports `Eq` when its stored values do, allowing a graph to deduplicate its edges.

```hg
let gA: Set<Edge<Int,Int,Bottom>> = {{1}->{2}, {2}->{3}}
let gB: Set<Edge<Int,Int,Bottom>> = {{2}->{3}, {1}->{2}}

// Independent graph constructions have distinct identities.
let superg: Set<Set<Edge<Int,Int,Bottom>>> = {gA, gB}
let superg2 = superg | {gA} // gA keeps its identity and deduplicates.
```

##### Type `Opaque`

`Opaque<Hide,Marker>` compares a hidden value by its identity `Marker`. The type checker still checks `Hide`, but equality does not inspect its contents.

The compiler assigns a fresh constant `Marker` when the graph value is constructed. Reusing that value preserves its marker; inference cannot merge distinct markers.

When a graph is stored inside another value, the compiler wraps that position in `Opaque`. The wrapper appears in the internal type; the written annotation is checked against `Hide`.

```hg
let g = {{1} -> {2}}
let flights = {3} <-> {4}
let atlas = {g, flights}   // g is compared by identity.
let summary = {g, 1} -> {2} // g keeps the same identity as a vertex.
```

`Eq(Opaque<Hide,Marker>)` does not require `Eq(Hide)`.

##### Type `!`

`!` is another name for `Bottom`, the algebraic zero, so `Bottom <=_+ T` for every type `T`. `Bottom` has no values. A missing edge payload is `None`, whose type can be `Option<Bottom>`.

An unconstrained type variable defaults to `Bottom` after the document's constraints are collected. A constrained problem need not have a least solution, as with `X+Y=Int`.

##### Type Aliasing

An alias substitutes its supplied arguments into the right hand side:

```hg
alias Graph<T,H,P> = Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>
```

The names in angle brackets are bound parameters. The alias introduces no new type and is expanded before type checking.

##### Type `Int` and `Decimal`

`Int` stores arbitrary precision integers. `Decimal` stores exact finite decimal values at arbitrary precision, so `1.1` equals `1.10`. They are distinct types.
