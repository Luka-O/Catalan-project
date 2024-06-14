# Formalization project for Logika v Računalništvu

This is the formalization project about Catalan numbers for the course Logika v Računalništvu, FMF, 2023/24.

All solutions for this project are in the folder `Catalan`. Solutions for small tasks are in the file [definitions.lean](https://github.com/Luka-O/Catalan-project/blob/main/Catalan/definitions.lean). We have completed all 5 small tasks:
1. Formalize the Catalan numbers using the recursive definition.
2. Formalize the concept of plane trees.
3. Formalize the concept of full binary trees.
4. Construct the type of full binary trees with `n` inner nodes.
5. Define the type of ballot sequences of length `n`.

We have also completed 5 larger tasks:
1. Construct a bijection that proves commutativity of `Fin` and `Sigma`. ([Task 1](https://github.com/Luka-O/Catalan-project/blob/main/Catalan/commutativity_fin_sigma.lean))
2. Construct a bijection between Catalan numbers from their recursive definition. ([Task 2](https://github.com/Luka-O/Catalan-project/blob/main/Catalan/catalan_bijection.lean))
3. Construct a bijection between lists of plane trees and plane trees. ([Task 4](https://github.com/Luka-O/Catalan-project/blob/main/Catalan/list_plane_tree_isomorphism.lean))
4. Construct the `rotating isomorphism`, which is the isomorphism between plane trees and full binary trees. ([Task 5](https://github.com/Luka-O/Catalan-project/blob/main/Catalan/rotating_isomorphism.lean))
5. Prove that $(n + 1) \mid \binom{2n}{n}$. ([Task 6](https://github.com/Luka-O/Catalan-project/blob/main/Catalan/binomial_divisibility.lean))

# Download
Clone the repository, open the terminal, navigate to the location of the repository, and then run the command `lake exe cache get`.
