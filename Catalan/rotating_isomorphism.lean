import Mathlib
import «Catalan».definitions

/- Large task 5 -/
/- Construction of the rotating isomorphism between plane trees and full binary trees -/

def extract_list_from_plane_tree : plane_tree → List plane_tree
| .make_plane_tree l => l

def number_of_nodes_of_plane_tree : plane_tree → ℕ
  | .make_plane_tree [] => 1
  | .make_plane_tree (x :: xs) => (number_of_nodes_of_plane_tree x) + (number_of_nodes_of_plane_tree (.make_plane_tree xs))

def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
| .make_plane_tree [] => .leaf
| .make_plane_tree (x :: xs) => .join
    (full_binary_tree_of_plane_tree x)
    (full_binary_tree_of_plane_tree (.make_plane_tree xs))

def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| .leaf => .make_plane_tree []
| .join T1 T2 => .make_plane_tree (
    (plane_tree_of_full_binary_tree T1) ::
    (extract_list_from_plane_tree (plane_tree_of_full_binary_tree T2)))

/- Proof that plane_tree_of_full_binary_tree is left inverse of full_binary_tree_of_plane_tree. -/
/- This function requires proof that n = number of nodes in tree. However this proof is not used in the function. -/
/- In fact n never appears in the function. This proof is only needed because Lean cannot infer termination without it. -/
/- With the proof that ties the number of nodes to a variable n Lean is capable of proving termination on its own. -/
def plane_tree_to_plane_tree_inverse_auxilary : (number_of_nodes_of_plane_tree x = n) → plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree x) = x := by
  intros h0
  cases x with
  | make_plane_tree l =>
    cases l with
    | nil =>
      rfl
    | cons a as =>
      unfold full_binary_tree_of_plane_tree
      unfold plane_tree_of_full_binary_tree
      unfold extract_list_from_plane_tree
      simp
      have h1 : plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree a) = a := by
        exact (plane_tree_to_plane_tree_inverse_auxilary (Eq.refl (number_of_nodes_of_plane_tree a)))
      have h2 : plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree (plane_tree.make_plane_tree as)) = plane_tree.make_plane_tree as := by
        exact (plane_tree_to_plane_tree_inverse_auxilary (Eq.refl (number_of_nodes_of_plane_tree (plane_tree.make_plane_tree as))))
      rw [h1, h2]
      simp

lemma plane_tree_to_plane_tree_inverse : ∀ x, plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree x) = x := by
  intro x
  exact (plane_tree_to_plane_tree_inverse_auxilary (Eq.refl (number_of_nodes_of_plane_tree x)))

lemma plane_tree_of_extracted_list_eq_plane_tree : plane_tree.make_plane_tree (extract_list_from_plane_tree x) = x := by
  cases x with
  | make_plane_tree l =>
    unfold extract_list_from_plane_tree
    simp

lemma full_binary_tree_to_full_binary_tree_inverse : ∀ x, full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree x) = x := by
  intro x
  induction x with
  | leaf =>
    rfl
  | join T1 T2 hT1 hT2 =>
    unfold plane_tree_of_full_binary_tree
    unfold full_binary_tree_of_plane_tree
    rw [hT1]
    rw [plane_tree_of_extracted_list_eq_plane_tree]
    rw [hT2]

/- Bijection between plane trees and full binary trees proven with rotating isomorphism -/
theorem bijection_plane_tree_full_binary_tree : plane_tree ≃ full_binary_tree := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · exact full_binary_tree_of_plane_tree
  · exact plane_tree_of_full_binary_tree
  · exact plane_tree_to_plane_tree_inverse
  · exact full_binary_tree_to_full_binary_tree_inverse
