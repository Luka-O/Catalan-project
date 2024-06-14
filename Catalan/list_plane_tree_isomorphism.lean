import Mathlib
import «Catalan».definitions

/- Large task 4 -/
/- Construction of a bijection between lists of plane trees and plane trees. -/

def list_plane_tree_of_plane_tree : plane_tree → List plane_tree
| .make_plane_tree l => l

def plane_tree_of_list_plane_tree : List plane_tree → plane_tree
| l => .make_plane_tree l

lemma plane_tree_of_list_plane_tree_inverse_list_plane_tree_of_plane_tree : ∀ x, plane_tree_of_list_plane_tree (list_plane_tree_of_plane_tree x) = x := by
  intro x
  cases x with
    | make_plane_tree l =>
      unfold list_plane_tree_of_plane_tree
      simp
      rfl

lemma list_plane_tree_of_plane_tree_inverse_plane_tree_of_list_plane_tree : ∀ x, list_plane_tree_of_plane_tree (plane_tree_of_list_plane_tree x) = x := by
  intro x
  rfl

/- Bijection between lists of plane trees and plane trees -/
theorem bijection_plane_tree_list_plane_tree : plane_tree ≃ List plane_tree := by
  refine Equiv.mk ?_ ?_ ?_ ?_
  · exact list_plane_tree_of_plane_tree
  · exact plane_tree_of_list_plane_tree
  · exact plane_tree_of_list_plane_tree_inverse_list_plane_tree_of_plane_tree
  · exact list_plane_tree_of_plane_tree_inverse_plane_tree_of_list_plane_tree
