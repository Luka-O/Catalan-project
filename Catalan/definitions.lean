import Mathlib
open BigOperators
open Finset
open Finset.antidiagonal


/- Small task 1 -/
/- Recursive definition of Catalan numbers -/
def my_catalan : ℕ → ℕ
| 0 => 1
| n + 1 => ∑ i : Fin (n + 1), my_catalan (i) * my_catalan (n - i)


/- Small task 2 -/
/- Definition of plane trees -/
inductive plane_tree : Type
| make_plane_tree : List plane_tree → plane_tree


/- Small task 3 -/
/- Definition of full binary trees -/
inductive full_binary_tree : Type
| leaf : full_binary_tree
| join : (T1 T2 : full_binary_tree) → full_binary_tree


/- Small task 4 -/
/- Definition of full binary trees with n inner nodes (not counting the leaves) -/
inductive full_binary_tree_with_n_inner_nodes : ℕ → Type
| leaf : full_binary_tree_with_n_inner_nodes 0
| join : (n m : ℕ) → full_binary_tree_with_n_inner_nodes n → full_binary_tree_with_n_inner_nodes m →
        full_binary_tree_with_n_inner_nodes (n + m + 1)


/- Small task 5 -/
/- Ballot sequences with length 2n are formalized as: ballot_sequence 2n 0 -/
inductive ballot_sequence : ℕ → ℕ → Type
| empty : ballot_sequence 0 0
| plus_one : ballot_sequence len sum → ballot_sequence (len + 1) (sum + 1)
| minus_one : ballot_sequence len (sum + 1) → ballot_sequence (len + 1) sum
