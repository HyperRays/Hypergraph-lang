
## Goal of the language

The goal of this language is to describe information using directed hypergraphs. Hypergraphs are a more generalized version of graphs. Its behavior is more sophisticated than formats like `JSON`, `TOML`, `YAML` etc. but fundamentally it does not perform computation.

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

let car: Car = Car(4, 1000)

```

##### Enums

Enums are essentially a list of possible named statuses:
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
##### Edges

 There are 2 types of edges; directed-edges and undirected-edges
 All edges have 3 components, a head, a tail and a payload.

The following are two equivalent directed edges:
```hg
let ht: Edge<Int, Decimal, String> = {1} -["Payload"]-> {1.1}
let ht: Edge<Int, Decimal, String> = {1.1} <-["Payload"]- {1}
```

Notice how the head and tail are sets of items, this is what defines the 
hyperedge of the hypergraph. 

The first type parameter `Int` defines the tail of the edge, `Decimal` defines the head of the edge. The final type `String` defines the payload type. Both the head and the tail values are embedded in a set. The payload type is also implicitly embedded in an `Option` type.

Since the payload type is embedded in `Option`, it is also possible to define an edge without an edge payload. This works for both edge types:
```hg
let ud: Edge<Int, Decimal, EmptySet> = {1} -> {1.1}
```

Undirected edges are special, they can be represented by a set of two directed edges, both in inverse directions, but they are not equivalent, since 'side surgery' works on UndirectedEdges (see section Operations on Edges).

An undirected edge is very similar in syntax except for the arrows on both sides (`<-[...]->`) in both directions:
```hg
let ud: UndirectedEdge<Int, Decimal, String> = {1} <-["Payload"]-> {1.1}
```

A special behaviour of `UndirectedEdge` is that when put into a `Set<Edge>`, its type can be 'demoted' into that of `Edge` and two edges are inserted into that set.  This is due to the type `Set<Edge>` being the emergent type of a `Graph` which will be explained in more detail in the type system section.

```hg
let a: Edge<Int, Decimal, EmptySet> = {1} -> {2}
let b: UndirectedEdge<Int, Decimal, EmptySet> = {2} <-> {3}

// b can be 'demoted' to type Edge
// and the set g then ends up with 3 elements
// {1} -> {2}, {2} -> {3}, {2} <- {3}
// This is useful when extracting exact edges from undirected ones
let g: Set<Edge<Int, Decimal, EmptySet>> = {a, b}  
```

However unless explicitly coerced, the type remains as `Set<Edge + UndirectedEdge>` and can be interpreted as `Set<Edge>` whenever necessary (usually internal to the compiler, when emitting adjacency matrices). The type coercion is also irreversible, meaning that in that context, the original `UndirectedEdge` cannot be recovered.  
##### Graphs

Graphs are an emergent object, meaning that they aren't really a separate object from the previous ones. They are of the type `Graph<T,H,P> = Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>`:

```hg
let a: Edge<Int, Decimal, EmptySet> = {1} -> {2}
let b: Edge<Int, Decimal, EmptySet> = {2} -> {3}
let c: Edge<Int, Decimal, EmptySet> = {3} -> {1}

let g: Graph<Int, Decimal, EmptySet> = {a, b, c}
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

Operations on Edges are similar to operations on sets, however unlike sets, operations on edges
only work with other edges. The operations perform edge 'side surgery' meaning the set operations are applied to the tail/head sets of the edge.

```hg
let edgeA: mut Edge<Int,Int,EmptySet> = {1} -> {2}
let edgeB: Edge<Int,Int,EmptySet> = {3} -> {4}

let edgeC: Edge<Int,Int,EmptySet> = edgeA | edgeB // {1, 3} -> {2, 4}
edgeA |= edgeB // same as edgeC, but now in-place, so edgeA is now equivalent to edgeC
```

Note that this also works for type `UndirectedEdge` but not a `Set<Edge>` containing two identical directed edges in opposite directions, which could represent an undirected edge.

If an Edge has a payload, then side surgery is only possible if the payload between the two edges of the binary operation is equal. 

```hg
let edgeA: mut Edge<Int,Int,String> = {1} -["Bob"]-> {2}
let edgeB: Edge<Int,Int,String> = {3} -["Bob"]-> {4}
let edgeC: Edge<Int,Int,String> = {3} -["Alice"]-> {4}

// allowed
edgeA |= edgeB
// not allowed
edgeB |= edgeC
```
### Type System

##### Type lattice 

The type system of this language builds a typed sum lattice, this means that concatenation of multiple types is denoted by `A+B+C`. Additionally some types are distributive over addition so:
```typesystem
DIS (A + B + C) = (DIS A) + (DIS B) + (DIS C) 
```

Mutability is denoted by the type `mut`. 
```hg
let a: mut Set<Int> = {1} // this variable is now mutable.
```

##### Distributivity and type `Eq`

Distribution of types over the sum is mainly important for the `Eq` type which allows the type checker to check if a variable is allowed to be checked for equality.  Most importantly this allows to poison types of `T<..., Set<Edge<...>>, ...>` which allows us to sidestep (hyper-)graph isomorphism. Important to note is that the type `Eq` is internal to the type checker and cannot be manually asserted by the user. 

An example of this (`T = Set`):
```hg
let gA: Set<Edge<Int,Int,EmptySet>> = {{1}->{2}, {2}->{3}}
let gB: Set<Edge<Int,Int,EmptySet>> = {{2}->{3}, {1}->{2}}

// Set deduplication requires checking equality between items,
// but since both gA and gB are graphs this would require graph isomorphism
// so sidestepping this means wrapping each in the Opaque<..., Marker> type
// done automatically by the type checker making gA distinct from gB by type inequality.
let superg: Set<Set<Edge<Int,Int,EmptySet>>> = {gA, gB}

// Union at the outer level compares gA to gB by Marker type
let superg2 = superg | {gA}   // still {gA, gB} — gA deduplicates by marker
```

The type `T` could also be some struct or even an edge, meaning that struct parameters and edge payloads get the same treatment (edge sides are sets). 

Since sets can hold inhomogeneous types, they in fact also distribute over the sum:
```typesystem
Set<A+B> = Set<A>+Set<B>
```

This gives the type checker a very easy way to represent some complex type in a canonical form: distribute all types into sums. This also allows for easy checking of `Eq` poisoning. The `Eq` type is derived and applied whenever an operation requires checking if two items have equality.

##### Type `Opaque`

Now, the type `Opaque<Hide, Marker>` is special, the type `Hide` is hidden from the type checker and the unique type `Marker` is set at the source of the value initialization. This allows for the type checker to assert equality by the unique `Marker` type, but not by value for types of nested graph. The type `Opaque` isn't user definable, it is set internally by the compiler.

```hg
let g = {{1} -> {2}}
let flights = {3} <-> {4}
let atlas   = {g, flights}      // graph as a member
let summary = {g, 1} -> {2}     // graph as a vertex
```

This is important, since the edges values are sets, and connecting edges together requires checking for head/tail equality. An unnamed graph would lead to a graph isomorphism problem drastically increasing computation. This also means that the type `Eq` does not poison a set inside of an `Opaque` type when that is nested inside of another set (`Set<Opaque<Set<Edge<...>>, Marker>>` is not poisoned).

The type `Eq` also distributes into the generic parameters `<...>`, since equality also depends on what the generic parameters are set to. Only for `Opaque` is there the exception for the parameter `Hide`. 

##### Type `EmptySet`

Note that `EmptySet` has been used for every example where the `Edge` does not have a payload, this is due to the property of `T :> EmptySet` meaning any type is inferable from an `EmptySet`, so you could have just as well used some other type `T`, but since it is not being used, it does not really matter.
##### Type Aliasing

Type aliasing is very simple, you define what generics you need in the angle brackets `<...>` and then use them on the right hand side. 

An example that you have already seen:
```hg
alias Graph<T,H,P> = Set<Edge<T,H,P> + UndirectedEdge<T,H,P>>
```

This creates the aliased type `Graph` with the free types `T`, `H`, `P`. 

##### Type `Int` and `Decimal`

Both types `Int` and `Decimal` are arbitrary precision. `Decimal` is like a floating point value, but checks for exact equality and that to, to an arbitrary precision, so `1.1` is equal to `1.10`.  
