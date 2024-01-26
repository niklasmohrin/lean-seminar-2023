# Construction of a Flow Equivalent Forest in Lean 4

## Setup

1. Install `elan`.
2. Run `lake exe cache get` to not compile `mathlib4` yourself.
3. Run `lake build` to check the project.

## Theorem

For an undirected flow network $G$, we define its _flow matrix_ to be the matrix $M$ such that for all vertices $u$, $v$, the value $M[u, v]$ is the max flow in $G$ from $u$ to $v$ (and $M$ is undefined along the diagonal).

For all $M$, it holds that
$$M \text{ is the flow matrix of some undirected network } G \iff M \text{ is symmetrical and } \forall u, v, w: \min(M[u, v], M[v, w]) \le M[u, w].$$

In particular, given a matrix $M$ with the conditions of the right side, we can construct an undirected network $G$ with flow matrix $M$ whose underlying graph of all non-zero capacity edges is acyclic. This implies that for any undirected flow network, there is a flow network based on a forest that has the same maximum flow between any two vertices.

The main result of our project is the construction of the acyclic network for a given matrix, see `FlowEquivalentForest/Flow/Matrix.lean`.

## Bibliography

- Gomory, Ralph E., and Tien Chung Hu. "Multi-terminal network flows." _Journal of the Society for Industrial and Applied Mathematics_ 9.4 (1961): 551-570.
